#!/usr/bin/env bash
set -euo pipefail

cd "$(dirname "$0")/.."
root="$PWD"
tools="$root/.lake/comparator-tools"
mkdir -p "$tools"

checkout() {
  local name="$1" repository="$2" revision="$3"
  local destination="$tools/$name"

  if [[ ! -d "$destination/.git" ]]; then
    git init -q "$destination"
    git -C "$destination" remote add origin "$repository"
  fi

  git -C "$destination" fetch --depth=1 origin "$revision"
  git -C "$destination" checkout --detach "$revision"
}

# Comparator and its locked exporter/checker dependencies match Lean 4.32.0.
checkout comparator https://github.com/leanprover/comparator.git \
  07bc4ea40f2266dcb861820a2ec1fa3244ed307f
cmp lean-toolchain "$tools/comparator/lean-toolchain"

# Backport upstream 9badaf470d8f724346d33738bd273efacd78df76 without upgrading Lean.
# Landrun must preserve the exporter's own `--` separator.
python3 - "$tools/comparator/Main.lean" <<'PY'
import sys
from pathlib import Path

path = Path(sys.argv[1])
source = path.read_text()
old = 'args ++ #[spawnArgs.cmd] ++ spawnArgs.args'
new = 'args ++ #["--", spawnArgs.cmd] ++ spawnArgs.args'
assert source.count(old) + source.count(new) == 1
path.write_text(source.replace(old, new))
PY
(cd "$tools/comparator" && lake build comparator lean4export)

checkout landrun https://github.com/Zouuup/landrun.git \
  811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
(cd "$tools/landrun" && go build -o landrun ./cmd/landrun)

# Run in the build workspace: Comparator's lake build calls reuse its .lake.
comparator="$tools/comparator/.lake/build/bin/comparator"
exporter="$tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export"
landrun="$tools/landrun/landrun"
challenges=(challenges/*/comparator.json)

for index in "${!challenges[@]}"; do
  challenge="${challenges[$index]}"
  echo "Comparing topic $((index + 1)) of ${#challenges[@]}: $challenge"

  systemd-run --user --pipe --wait --collect \
    --property=RestrictAddressFamilies=~AF_UNIX \
    --working-directory="$root" \
    --setenv="PATH=$PATH" \
    --setenv="COMPARATOR_LEAN4EXPORT=$exporter" \
    --setenv="COMPARATOR_LANDRUN=$landrun" \
    lake env "$comparator" "$challenge"
done
