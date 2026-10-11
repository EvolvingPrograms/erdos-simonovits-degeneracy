import ThreeDegenerate.Definitions
import Theorem12r3

/-!
# Solution: the 3-degenerate counterexamples

Both statements below are supplied by the existing proofs.
-/

namespace ThreeDegenerateGraphs

open Filter SimpleGraph

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
            (extremalNumber n H : ℝ) :=
  ThreeDegenerateGraphsTarget.threeDegenerateExtremalCounterexample

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
            (extremalNumber n H : ℝ) :=
  ThreeDegenerateGraphsTarget.threeDegenerateExtremalCounterexample_sharp

end ThreeDegenerateGraphs
