import Theorem2

/-!
# Comparator solution for Challenge 2 (`K_RDegenerateGraphs.lean`)

Restates the challenge verbatim and discharges it with
`RDegenerateGraphsTarget.rDegenerateExtremalCounterexample_exact`.

Judged by `comparator` with `challenges/challenge2.json`.
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
            (SimpleGraph.extremalNumber n H : ℝ) :=
  RDegenerateGraphsTarget.rDegenerateExtremalCounterexample_exact r hr

end RDegenerateGraphs
