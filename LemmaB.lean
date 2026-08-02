import BernsteinStrip

/-!
# Lemma B: the supremum of `G_r` sits at the symmetric point

Design-notes reference (notes not shipped in this repository): §4 (statement in §4.7).

Target:
`supG r lam = Gfun r lam (1/2) (1/2)` for `2 ≤ r`, `0 < lam ≤ 27/20`.

The proof combines per-term concavity in `v`, transfer of curvature bounds
through a Bernstein operator in `q`, and Lemma A away from a central strip;
all of that development is `lib/BernsteinStrip.lean`.

A quantified version valid for every subcritical `λ` once `r ≥ R(λ)` is
`lib/LemmaBQuant.lean`; it is that version which makes Theorem 3(a)
unconditional on the full range `λ ln 2 < 1`.
-/

namespace DegeneracyLaw
namespace LemmaB

open TwoDegenerateGraphs Finset

noncomputable section

/-- **The pointwise form of Lemma B**: the centre dominates on the whole box. -/
theorem Gfun_le_center (r : ℕ) (lam q v : ℝ) (hr : 2 ≤ r)
    (hlam0 : 0 < lam) (hlam : lam ≤ 27 / 20)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    Gfun r lam q v ≤ Gfun r lam (1 / 2) (1 / 2) := by
  have hL : (0 : ℝ) < Real.log 2 := log_two_pos
  have hpa0 : 0 < lam * Real.log 2 := mul_pos hlam0 hL
  have hpa1 : lam * Real.log 2 < 1 := by
    have h9 := Real.log_two_lt_d9
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 27 / 20 - lam) hL.le]
  by_cases hs : inStrip lam v
  · exact Gfun_le_center_strip r lam q v hr hpa0 hpa1 hq hv hs
  · exact Gfun_le_center_offstrip r lam q v hr hlam0 hlam hq hv hs

/-! ## §5 From the pointwise bound to the supremum -/

/-- **Lemma B** (paper §4.7) at the Theorem-2 operating point `λ ≤ 1.35`,
where the threshold `r₀(λ)` equals `2`, so there are no finite exceptions. -/
theorem supG_eq_center (r : ℕ) (lam : ℝ) (hr : 2 ≤ r) (hlam0 : 0 < lam)
    (hlam : lam ≤ 27 / 20) :
    supG r lam = Gfun r lam (1 / 2) (1 / 2) :=
  supG_eq_center_of_le r lam fun q hq v hv =>
    Gfun_le_center r lam q v hr hlam0 hlam hq hv

end

end LemmaB
end DegeneracyLaw
