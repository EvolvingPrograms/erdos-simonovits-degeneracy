import Mathlib

/-!
# Definitions for a 3-degenerate counterexample

These mathematical definitions depend only on Mathlib.
The challenge and its solution import this same specification.
-/

namespace ThreeDegenerateGraphs

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

/-- The specialization to degeneracy at most 3. -/
abbrev IsThreeDegenerate {V : Type*} (G : SimpleGraph V) : Prop :=
  IsDegenerate 3 G

end ThreeDegenerateGraphs
