# Comparing the mathematics with Lean

These specifications state five results independently of the proof development.
They are grouped into four topics. Each topic has a mathematical explanation,
a table translating its notation into Lean, and the complete challenge and
solution.

## Statements

For the graph statements, $H$ is finite, connected, and bipartite. Constants are
positive, and the extremal-number inequalities hold for all sufficiently large
natural numbers $n$. “Exact degeneracy $r$” means $r$-degenerate but not
$(r-1)$-degenerate.

| Topic | Mathematical statement | Lean declaration |
| --- | --- | --- |
| [Every degeneracy](AllR/) | For every $r\ge2$, some $H$ of exact degeneracy $r$ satisfies $\operatorname{ex}(n;H)\ge c n^{2-1/r+1/(28r^2)}$ | [`rDegenerateExtremalCounterexample`](AllR/Challenge.lean) |
| [Degeneracy 3](ThreeDegenerate/) | Some 3-degenerate $H$ satisfies $\operatorname{ex}(n;H)\ge c n^{5/3+\varepsilon}$ for some $\varepsilon>0$ | [`threeDegenerateExtremalCounterexample`](ThreeDegenerate/Challenge.lean) |
| [Sharp degeneracy 3](ThreeDegenerate/) | Some $H$ of exact degeneracy 3 satisfies $\operatorname{ex}(n;H)\ge c n^{5/3+1/160}$ | [`threeDegenerateExtremalCounterexample_sharp`](ThreeDegenerate/Challenge.lean) |
| [Window law](WindowLaw/) | For $0<\lambda$ and $\lambda\log 2<1$, $r^2\mathrm{width}(r,\lambda)\to\lambda^4(\log 2)^3/64$ | [`width_tendsto`](WindowLaw/Challenge.lean) |
| [Family law](FamilyLaw/) | For every fixed $\theta\in\mathbb R$, $8r^2\varepsilon_r^{\max}(\beta_\theta)\to1-\theta$ | [`eight_rsq_epsMax_tendsto`](FamilyLaw/Challenge.lean) |

## Reading a comparison

Each topic has the same four files:

| File | Purpose |
| --- | --- |
| `Definitions.lean` | Mathematical definitions, importing only Mathlib. |
| `Challenge.lean` | The theorem statements, with intentional `sorry` placeholders. |
| `Solution.lean` | The same statements, supplied by the existing proofs. |
| `comparator.json` | The module names, theorem names, and permitted axioms. |

Read the definitions and challenge to judge whether they express the intended
mathematics. The solution imports the definitions and proof modules; it never
imports the challenge. This keeps the challenge placeholders out of the proof.

[Comparator](https://github.com/leanprover/comparator) then checks that the
statements and their definitions agree, that proof dependencies use only
`propext`, `Classical.choice`, and `Quot.sound`, and that the exported proofs
replay through Lean's kernel. No native-evaluation axioms are permitted.

The two 3-degenerate results share a single comparison. Four comparisons cover
all five theorems without exporting the same 3-degenerate modules twice.

## Running the comparisons

From the repository root:

```sh
lake exe cache get
lake build Comparison ChallengeFaithful
python3 scripts/audit_axioms.py
bash scripts/compare.sh
```

The last command requires Linux, Go, and a working systemd user manager. It
builds pinned Comparator, exporter, checker, and Landrun tools with the project's
Lean 4.32.0 toolchain. The setup includes upstream Comparator's argument-separator
fix and the systemd socket restriction. It uses real Landrun, not the macOS
fallback shim.

[CI](../.github/workflows/build.yml) runs on pushes to `main` and pull requests,
and can be started manually. After building, it audits the two main
counterexample endpoints and runs Comparator in the **same workspace**, reusing
the built modules. Logs identify each topic's position out of four. The
`proof-verification` artifact contains `axiom-audit.txt` and `comparator.txt`.

The axiom audit and Comparator are separate checks. A successful build alone
does not establish that a proof has no admitted dependencies.
