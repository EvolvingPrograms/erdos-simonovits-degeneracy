# The 3-degenerate counterexamples

Both statements assert that a finite connected bipartite graph has extremal
number larger than the conjectured order $n^{5/3}$. The second makes the
**exact degeneracy** and **exponent gain** explicit.

## Mathematics and Lean

In each row, the constants are positive and the inequality holds for every
sufficiently large natural number $n$.

| Statement | Degeneracy in Lean | Exponent in Lean | Declaration |
| --- | --- | --- | --- |
| Some 3-degenerate $H$ satisfies $\operatorname{ex}(n;H)\ge c n^{5/3+\varepsilon}$ for some $c,\varepsilon>0$ | `IsThreeDegenerate H` | `(5 : ℝ) / 3 + ε` | `threeDegenerateExtremalCounterexample` |
| Some $H$ of degeneracy exactly 3 satisfies $\operatorname{ex}(n;H)\ge c n^{5/3+1/160}$ for some $c>0$ | `IsDegenerate 3 H ∧ ¬ IsDegenerate 2 H` | `(5 : ℝ) / 3 + 1 / 160` | `threeDegenerateExtremalCounterexample_sharp` |

The namespace is `ThreeDegenerateGraphs`. In [Definitions.lean](Definitions.lean),
`IsDegenerate r H` means that every nonempty finite vertex set contains a vertex
with at most $r$ neighbours in that set. `IsThreeDegenerate H` is an abbreviation
for `IsDegenerate 3 H`; it does not assert exact degeneracy.

`∀ᶠ n : ℕ in atTop` means “for every sufficiently large natural number $n$.”
The existential graph and constants are chosen before this quantifier.

## Challenges and solutions

Both [challenge statements](Challenge.lean) are checked in one Comparator run:

```lean
/-- There is a connected bipartite 3-degenerate graph with a **positive exponent gain**. -/
theorem threeDegenerateExtremalCounterexample :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsThreeDegenerate H ∧
      ∃ c ε : ℝ,
        0 < c ∧
        0 < ε ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((5 : ℝ) / 3 + ε) ≤
            (extremalNumber n H : ℝ) := by
  sorry

/-- There is a connected bipartite graph of **exact degeneracy** 3
with **sharp gain** `1 / 160` above the conjectured exponent `5 / 3`. -/
theorem threeDegenerateExtremalCounterexample_sharp :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsDegenerate 3 H ∧
      ¬ IsDegenerate 2 H ∧
      ∃ c : ℝ,
        0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((5 : ℝ) / 3 + 1 / 160) ≤
            (extremalNumber n H : ℝ) := by
  sorry
```

[Solution.lean](Solution.lean) supplies them from the corresponding declarations
in the `ThreeDegenerateGraphsTarget` namespace of
[Theorem12r3.lean](../../proofs/Theorem12r3.lean). The sharp statement uses
`threeDegenerateExtremalCounterexample_sharp`, not a theorem with an unspecified
gain.

## Files and verification

[Definitions.lean](Definitions.lean) imports only Mathlib.
[Challenge.lean](Challenge.lean) states the specification using those definitions.
[Solution.lean](Solution.lean) imports the same definitions and supplies the
existing proof; it does not import the challenge or its placeholders.

[comparator.json](comparator.json) selects the theorem names and permits only
`propext`, `Classical.choice`, and `Quot.sound`. Comparator compares the
statements and their definitions, checks the proof dependencies, and replays
the proof through Lean's kernel. The two `sorry` placeholders mark the
statements to be checked; the solution must have no `sorryAx` dependency.

See [running all comparisons](../README.md#running-the-comparisons) for the CI
workflow and local commands.
