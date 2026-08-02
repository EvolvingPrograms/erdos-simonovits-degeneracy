import Mathlib

/-!
# Challenge 2: an r-degenerate counterexample at every level r ≥ 2

Frozen statement file, in the idiom of `K_ThreeDegenerateGraphs.lean`.
Target theorem: for every `r ≥ 2` there is a connected bipartite graph `H`
of degeneracy exactly `r` (that is, `r`-degenerate but not
`(r-1)`-degenerate) with `ex(n; H) ≥ c · n^(2 - 1/r + 1/(28 r²))` for all
large `n`, refuting `ex(n; H) = O(n^(2 - 1/r))` (Erdős problem #146) at
every level.
-/

namespace RDegenerateGraphs

open Filter Finset SimpleGraph
open scoped Topology

noncomputable def neighborsWithin {V : Type*} (G : SimpleGraph V)
    (s : Finset V) (v : V) : Finset V := by
  classical
  exact s.filter (G.Adj v)

def IsDegenerate {V : Type*} (r : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty →
    ∃ v ∈ s, (neighborsWithin G s v).card ≤ r

open Classical in
theorem rDegenerateExtremalCounterexample (r : ℕ) (hr : 2 ≤ r) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsDegenerate r H ∧
      ¬ IsDegenerate (r - 1) H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (28 * (r : ℝ) ^ 2)) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  sorry

end RDegenerateGraphs
