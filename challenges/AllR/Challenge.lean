import AllR.Definitions

/-!
# Challenge: a counterexample at every degeneracy

The placeholder specifies the statement that Comparator checks.
-/

namespace RDegenerateGraphs

open Filter SimpleGraph

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

end RDegenerateGraphs
