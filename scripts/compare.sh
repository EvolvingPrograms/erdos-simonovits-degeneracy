#!/usr/bin/env bash
set -euo pipefail
cd "$(dirname "$0")/.."
root="$PWD"
tools="$root/.lake/comparator-tools"
mkdir -p "$tools"

checkout() {
  if [[ ! -d "$tools/$1/.git" ]]; then
    git init -q "$tools/$1"
    git -C "$tools/$1" remote add origin "$2"
  fi
  git -C "$tools/$1" fetch --depth=1 origin "$3"
  git -C "$tools/$1" checkout --detach "$3"
}

# Comparator and its locked exporter/checker dependencies match Lean 4.32.0.
checkout comparator https://github.com/leanprover/comparator.git 07bc4ea40f2266dcb861820a2ec1fa3244ed307f
cmp lean-toolchain "$tools/comparator/lean-toolchain"
(cd "$tools/comparator" && lake build comparator lean4export)
checkout landrun https://github.com/Zouuup/landrun.git 811cfff51ceaf3d9843708aa6d22e9b84ccac8b4
(cd "$tools/landrun" && go build -o landrun ./cmd/landrun)

# Run in the build workspace: Comparator's lake build calls reuse its .lake.
for challenge in challenges/challenge*.json; do
  systemd-run --user --pipe --wait --collect \
    --property=RestrictAddressFamilies=~AF_UNIX \
    --working-directory="$root" --setenv="PATH=$PATH" \
    --setenv="COMPARATOR_LEAN4EXPORT=$tools/comparator/.lake/packages/lean4export/.lake/build/bin/lean4export" \
    --setenv="COMPARATOR_LANDRUN=$tools/landrun/landrun" \
    lake env "$tools/comparator/.lake/build/bin/comparator" "$challenge"
done
