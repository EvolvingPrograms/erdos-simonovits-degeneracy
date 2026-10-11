"""Audit the all-r and sharp r = 3 counterexamples, using built modules."""
import re
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGETS = (
    "RDegenerateGraphsTarget.rDegenerateExtremalCounterexample_exact",
    "ThreeDegenerateGraphsTarget.threeDegenerateExtremalCounterexample_sharp",
)
ALLOWED = {"propext", "Quot.sound", "Classical.choice"}


def main():
    subprocess.run(["git", "rev-parse", "HEAD"], cwd=ROOT, check=True)
    with tempfile.NamedTemporaryFile(mode="w", suffix=".lean", dir=ROOT) as source:
        source.write("import Theorem12\nimport Theorem12r3\n")
        source.write("".join(f"#print axioms {name}\n" for name in TARGETS))
        source.flush()
        result = subprocess.run(
            ["lake", "env", "lean", source.name], cwd=ROOT,
            text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
        )
    print(result.stdout, end="", flush=True)
    result.check_returncode()
    for name in TARGETS:
        match = re.search(r"'" + re.escape(name) + r"' depends on axioms: \[([^]]*)\]", result.stdout)
        if not match:
            raise SystemExit(f"Missing axiom report: {name}")
        axioms = {a.strip() for a in match[1].split(",") if a.strip()}
        if axioms - ALLOWED:
            raise SystemExit(f"Unexpected axioms for {name}: {sorted(axioms - ALLOWED)}")


if __name__ == "__main__":
    main()
