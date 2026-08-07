import Theorem12r3

/-!
# Comparator-format solution file

`leanprover/comparator` judges a submission by exporting a `Challenge`
module (here `K_ThreeDegenerateGraphs.lean`, the frozen statement with its
intentional `sorry`) and a `Solution` module, and checking that the
solution proves a theorem of the **same name and statement** using only the
permitted axioms.

This file is that solution: it restates the challenge verbatim — the
auxiliary definitions token-for-token and the theorem with the identical
fully qualified name `ThreeDegenerateGraphs.threeDegenerateExtremalCounterexample`
— and discharges it with the proof from `Theorem12r3.lean`; cf.
`tests/ChallengeFaithful.lean`.

Judged by `comparator` with `challenges/challenge1.json`:
  challenge_module = "K_ThreeDegenerateGraphs", solution_module = "Solution".
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
            (SimpleGraph.extremalNumber n H : ℝ) :=
  ThreeDegenerateGraphsTarget.threeDegenerateExtremalCounterexample

end ThreeDegenerateGraphs
