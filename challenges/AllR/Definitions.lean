import Mathlib

/-!
# Definitions for a counterexample at every degeneracy

These mathematical definitions depend only on Mathlib.
The challenge and its solution import this same specification.
-/

namespace RDegenerateGraphs

open SimpleGraph

/-- The neighbours of `v` that lie in the finite vertex set `s`. -/
noncomputable def neighborsWithin {V : Type*} (G : SimpleGraph V)
    (s : Finset V) (v : V) : Finset V := by
  classical
  exact s.filter (G.Adj v)

/-- **Degeneracy at most `r`**: every nonempty finite vertex set has a vertex
with at most `r` neighbours in that set. -/
def IsDegenerate {V : Type*} (r : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty →
    ∃ v ∈ s, (neighborsWithin G s v).card ≤ r

end RDegenerateGraphs
