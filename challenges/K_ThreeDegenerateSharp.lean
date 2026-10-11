import Mathlib

/-! Sharp r = 3 challenge: exact degeneracy and gain 1/160. -/
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
theorem threeDegenerateExtremalCounterexample_sharp :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsDegenerate 3 H ∧ ¬ IsDegenerate 2 H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((5 : ℝ) / 3 + 1 / 160) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  sorry

end ThreeDegenerateGraphs
