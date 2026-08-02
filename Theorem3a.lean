import WindowLimit

/-!
# Theorem 3(a): the limit of the rescaled feasibility window

For every fixed `λ` with `λ ln 2 < 1`, at the tuned radius
`τ_r = 1/2 - λ ln 2/(4r)`,

  `r² · (C_r - A_r) → λ⁴ ln³2 / 64`.

The comparison sequences and the pointwise sandwich that prove it live in
`lib/WindowLimit.lean`; this file states the theorem and discharges the
center-maximization hypothesis on the full subcritical range using the
quantified Lemma B (`DegeneracyLawQuant.supG_eq_center_quant`).

Sharpness — the rescaled width tends to `-∞` once `λ ln 2 > 1`, so the phase
transition sits exactly at Gibbs weight `2^λ = e` — is `Prop63.lean`.
-/

namespace DegeneracyLaw

open Filter Topology

noncomputable section

/-- **Theorem 3(a), unconditional, full subcritical range.** For every fixed
`λ` with `λ ln 2 < 1`, `r² · width_r → W(λ) = λ⁴ ln³2 / 64`.  The sandwich
only needs Lemma B eventually in `r`, so the quantified Lemma B
(`DegeneracyLawQuant.supG_eq_center_quant`, valid for `r ≥ R_of λ`)
discharges the center-maximization hypothesis with no cap on `λ`. -/
theorem width_tendsto_unconditional_full (lam : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam * Real.log 2 < 1) :
    Tendsto (fun r : ℕ => (r : ℝ) ^ 2 * width r lam) atTop (𝓝 (Wconst lam)) := by
  have ha0 : 0 < lam * Real.log 2 :=
    mul_pos hlam0 (Real.log_pos (by norm_num))
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (lowerSeq_tendsto lam) (upperSeq_tendsto lam) ?_ ?_
  · filter_upwards [eventually_ge_atTop (max 2 (DegeneracyLawQuant.R_of lam))]
      with r hr
    exact lowerSeq_le_rsq_width lam hlam0 hlam1 (le_trans (le_max_left _ _) hr)
      (DegeneracyLawQuant.supG_eq_center_quant r lam ha0 hlam1
        (le_trans (le_max_right _ _) hr))
  · filter_upwards [eventually_ge_atTop 2] with r hr
    exact rsq_width_le_upperSeq lam hlam0 hlam1 hr

/-- **Eventual positivity, full subcritical range**: unconditional form of
`width_eventually_pos`. -/
theorem width_eventually_pos_full (lam : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam * Real.log 2 < 1) :
    ∀ᶠ r : ℕ in atTop, 0 < width r lam := by
  have h := width_tendsto_unconditional_full lam hlam0 hlam1
  have hpos : ∀ᶠ r : ℕ in atTop, 0 < (r : ℝ) ^ 2 * width r lam :=
    h.eventually (eventually_gt_nhds (Wconst_pos hlam0)) |>.mono fun r hr => hr
  filter_upwards [hpos, eventually_ge_atTop 1] with r hr hr1
  have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hr1
  have hsq : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  nlinarith [hr, hsq]

end

end DegeneracyLaw
