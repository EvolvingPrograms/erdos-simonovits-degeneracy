import Assembly3
import AssemblyR

/-!
# Theorem 1.2 at `r = 3`: the sharp counterexample

There is a connected bipartite graph `H` of degeneracy exactly `3` and a
constant `c > 0` with `c · n^(5/3 + 1/160) ≤ ex(n, H)` eventually, refuting
`ex(n; H) = O(n^(2 - 1/3))` (Erdős problem #146) at `r = 3`.

Two independent routes reach this, and both are stated below:

* the hand-certified `r = 3` assembly of `proofs/scratch/Assembly3.lean`, which gives the
  weaker gain `1/4000` (`threeDegenerateExtremalCounterexample_exact`);
* the general-`r` pipeline of `proofs/lib/AssemblyR.lean` specialized at `r = 3`,
  fed with Lemma 4.4's window bound for `r = 3`, which gives the sharp gain
  `1/160` (`threeDegenerateExtremalCounterexample_sharp`).

The second is the headline. The first is kept because it is genuinely
independent of the general-`r` machinery: `proofs/scratch/Assembly3.lean` does not import
`proofs/lib/AssemblyR.lean`.
-/
/-! ## The target statement, verbatim from `scratchpad/ThreeDegenerate.lean` -/

namespace ThreeDegenerateGraphsTarget

open Filter Finset SimpleGraph

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
  obtain ⟨q, H, hcon, hbip, hdeg, -, hbnd⟩ :=
    ThreeAssembly.threeDegenerateExtremalCounterexample
  exact ⟨q, H, hcon, hbip, hdeg, hbnd⟩

-- The same, with the degeneracy pinned exactly: `H` is 3-degenerate but
-- not 2-degenerate, and the exponent gain is `ε = 1/4000`.
open Classical in
theorem threeDegenerateExtremalCounterexample_exact :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsThreeDegenerate H ∧
      ¬ IsDegenerate 2 H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((5 : ℝ) / 3 + 1 / 4000) ≤
            (SimpleGraph.extremalNumber n H : ℝ) :=
  ThreeAssembly.threeDegenerateExtremalCounterexample_explicit

-- The same, with the exponent gain pinned to `ε = 1/4000`.
open Classical in
theorem threeDegenerateExtremalCounterexample_explicit :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsThreeDegenerate H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((5 : ℝ) / 3 + 1 / 4000) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  obtain ⟨q, H, hcon, hbip, hdeg, -, hbnd⟩ :=
    ThreeAssembly.threeDegenerateExtremalCounterexample_explicit
  exact ⟨q, H, hcon, hbip, hdeg, hbnd⟩

-- **The sharp `r = 3` form**: degeneracy exactly 3 and exponent
-- `5/3 + 1/160` — past the midpoint evaluation (roughly `1/590`) for this case.
open Classical in
theorem threeDegenerateExtremalCounterexample_sharp :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsDegenerate 3 H ∧
      ¬ IsDegenerate 2 H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((5 : ℝ) / 3 + 1 / 160) ≤
            (SimpleGraph.extremalNumber n H : ℝ) :=
  RAssembly.threeDegenerateExtremalCounterexample_sharp
end ThreeDegenerateGraphsTarget
