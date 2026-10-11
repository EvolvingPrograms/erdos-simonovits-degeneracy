import AllR.Definitions
import Theorem12

/-!
# Solution: a counterexample at every degeneracy

The statement below is supplied by the existing proof.
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
            (extremalNumber n H : ℝ) :=
  RDegenerateGraphsTarget.rDegenerateExtremalCounterexample_exact r hr

end RDegenerateGraphs
