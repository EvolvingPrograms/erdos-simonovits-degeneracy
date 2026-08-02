import Mathlib

/-!
# A 3-degenerate counterexample to the Erdős–Simonovits degeneracy conjecture

Statement file, in the idiom of `J_TwoDegenerateGraphs.lean`.
Target theorem: there is a connected bipartite 3-degenerate graph `H` with
`ex(n; H) ≥ c * n ^ (5/3 + ε)` for all large `n`, refuting
`ex(n; H) = O(n^(2 - 1/r))` (Erdős problem #146) at `r = 3`.
-/

namespace ThreeDegenerateGraphs

open Filter Finset SimpleGraph
open scoped Topology

noncomputable def neighborsWithin {V : Type*} (G : SimpleGraph V)
    (s : Finset V) (v : V) : Finset V := by
  classical
  exact s.filter (G.Adj v)

def IsDegenerate {V : Type*} (r : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty →
    ∃ v ∈ s, (neighborsWithin G s v).card ≤ r

abbrev IsThreeDegenerate {V : Type*} (G : SimpleGraph V) : Prop :=
  IsDegenerate 3 G

open Classical in
theorem threeDegenerateExtremalCounterexample :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsThreeDegenerate H ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((5 : ℝ) / 3 + ε) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  sorry

end ThreeDegenerateGraphs
