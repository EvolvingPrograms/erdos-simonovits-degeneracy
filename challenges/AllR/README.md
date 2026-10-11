# Counterexamples at every degeneracy

For every integer $r \ge 2$, there is a finite connected bipartite graph $H_r$
of **degeneracy exactly $r$** and a constant $c>0$ such that, for all sufficiently
large $n$,

$$\mathrm{ex}(n;H_r) \ge c\,n^{2-1/r+1/(28r^2)}.$$

The positive gain $1/(28r^2)$ makes the exponent strictly larger than
the conjectured $2-1/r$.
The graph and the constant may depend on $r$, but not on $n$.

## Mathematics and Lean

| Mathematics | Lean expression |
| --- | --- |
| Every integer $r\ge2$ | `(r : ℕ) (hr : 2 ≤ r)` |
| A finite graph $H$ on $q$ vertices | `H : SimpleGraph (Fin q)` |
| Connected and bipartite | `H.Connected ∧ H.IsBipartite` |
| Degeneracy exactly $r$ | `IsDegenerate r H ∧ ¬ IsDegenerate (r - 1) H` |
| A positive constant independent of $n$ | `∃ c : ℝ, 0 < c ∧ ...` |
| For every sufficiently large natural number $n$ | `∀ᶠ n : ℕ in atTop, ...` |
| Extremal number $\mathrm{ex}(n;H)$, viewed as a real number | `(extremalNumber n H : ℝ)` |

[The degeneracy definition](Definitions.lean) says that every nonempty finite
vertex set contains a vertex with at most $r$ neighbours in that set:

```lean
def IsDegenerate {V : Type*} (r : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty →
    ∃ v ∈ s, (neighborsWithin G s v).card ≤ r
```

## Challenge and solution

The [complete challenge](Challenge.lean) keeps the exact degeneracy and exponent
visible in the statement:

```lean
/-- For every `r ≥ 2`, a connected bipartite graph has **exact degeneracy** `r`
and **exponent gain** `1 / (28 r²)`. -/
theorem rDegenerateExtremalCounterexample (r : ℕ) (hr : 2 ≤ r) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsDegenerate r H ∧
      ¬ IsDegenerate (r - 1) H ∧
      ∃ c : ℝ,
        0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (28 * (r : ℝ) ^ 2)) ≤
            (extremalNumber n H : ℝ) := by
  sorry
```

The [solution](Solution.lean) supplies this statement with one line:

```lean
  RDegenerateGraphsTarget.rDegenerateExtremalCounterexample_exact r hr
```

That theorem is proved in [Theorem12.lean](../../proofs/Theorem12.lean).

## Files and verification

[Definitions.lean](Definitions.lean) imports only Mathlib.
[Challenge.lean](Challenge.lean) states the specification using those definitions.
[Solution.lean](Solution.lean) imports the same definitions and supplies the
existing proof; it does not import the challenge or its placeholders.

[comparator.json](comparator.json) selects the theorem names and permits only
`propext`, `Classical.choice`, and `Quot.sound`. Comparator compares the
statements and their definitions, checks the proof dependencies, and replays
the proof through Lean's kernel. The `sorry` in the challenge marks the
statement to be checked; the solution must have no `sorryAx` dependency.

See [running all comparisons](../README.md#running-the-comparisons) for the CI
workflow and local commands.
