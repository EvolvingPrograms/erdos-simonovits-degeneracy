import Lemma61
import LemmaC
import LemmaB
import LemmaBQuant

/-!
# Theorem 3(a): the limit of the rescaled feasibility window

The two-sided bounds are already available:

* `DegeneracyLaw.width_le_mul` (Lemma 6.1, **unconditional**) gives
  `width r λ ≤ W(λ)/r² · (1 - 1/r)`;
* `DegeneracyLaw.width_ge` (Lemma C, bound (5.6), conditional on Lemma B) gives
  `W(λ)/r² · (1 - (1 + a²/3)/r) - a⁶/(1920 ln2 · r⁵ (1 - a²/4)) ≤ width r λ`,
  where `a = λ ln 2`.

Multiplying both by `r²` and letting `r → ∞`, all subleading terms are explicit
powers of `1/r`, so the sandwich closes on `W(λ)`:

  `r² · width_r → W(λ) = λ⁴ ln³2 / 64`.

Lemma B is taken here as a hypothesis
`hB : ∀ r ≥ 2, supG r λ = G_r(1/2,1/2)` rather than imported.

Design-notes reference (notes not shipped in this repository): §6.7-6.8 and §9.3.
-/

namespace DegeneracyLaw

open Filter Topology

noncomputable section

/-! ## The two comparison sequences -/

/-- The rescaled upper bound sequence `W(λ)(1 - 1/r)` from Lemma 6.1. -/
def upperSeq (lam : ℝ) (r : ℕ) : ℝ := Wconst lam * (1 - 1 / (r : ℝ))

/-- The rescaled lower bound sequence from Lemma C, bound (5.6). -/
def lowerSeq (lam : ℝ) (r : ℕ) : ℝ :=
  Wconst lam * (1 - (1 + (lam * Real.log 2) ^ 2 / 3) * (1 / (r : ℝ)))
    - (lam * Real.log 2) ^ 6 /
        (1920 * Real.log 2 * (1 - (lam * Real.log 2) ^ 2 / 4)) * (1 / (r : ℝ)) ^ 3

/-- `1/r → 0` along `atTop` in `ℕ`. -/
theorem tendsto_inv_nat : Tendsto (fun r : ℕ => 1 / (r : ℝ)) atTop (𝓝 0) :=
  tendsto_one_div_atTop_nhds_zero_nat

theorem upperSeq_tendsto (lam : ℝ) :
    Tendsto (upperSeq lam) atTop (𝓝 (Wconst lam)) := by
  show Tendsto (fun r : ℕ => upperSeq lam r) atTop _
  have h : Tendsto (fun r : ℕ => Wconst lam * (1 - 1 / (r : ℝ))) atTop
      (𝓝 (Wconst lam * (1 - 0))) :=
    (tendsto_const_nhds.sub tendsto_inv_nat).const_mul _
  simpa [upperSeq] using h

theorem lowerSeq_tendsto (lam : ℝ) :
    Tendsto (lowerSeq lam) atTop (𝓝 (Wconst lam)) := by
  show Tendsto (fun r : ℕ => lowerSeq lam r) atTop _
  set c : ℝ := 1 + (lam * Real.log 2) ^ 2 / 3 with hc
  set K : ℝ := (lam * Real.log 2) ^ 6 /
      (1920 * Real.log 2 * (1 - (lam * Real.log 2) ^ 2 / 4)) with hK
  have h1 : Tendsto (fun r : ℕ => Wconst lam * (1 - c * (1 / (r : ℝ)))) atTop
      (𝓝 (Wconst lam * (1 - c * 0))) :=
    (tendsto_const_nhds.sub (tendsto_inv_nat.const_mul c)).const_mul _
  have h2 : Tendsto (fun r : ℕ => K * (1 / (r : ℝ)) ^ 3) atTop (𝓝 (K * 0 ^ 3)) :=
    (tendsto_inv_nat.pow 3).const_mul K
  have h := h1.sub h2
  simpa [lowerSeq, hc, hK] using h

/-! ## The pointwise sandwich -/

theorem rsq_width_le_upperSeq (lam : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam * Real.log 2 < 1) {r : ℕ} (hr : 2 ≤ r) :
    (r : ℝ) ^ 2 * width r lam ≤ upperSeq lam r := by
  have hr0 : (0 : ℝ) < r := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (le_trans (by norm_num) hr)
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hra : lam * Real.log 2 < 2 * (r : ℝ) := by linarith
  have h := width_le_mul r lam hr hlam0 hra
  have hsq : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  have := mul_le_mul_of_nonneg_left h hsq.le
  refine this.trans (le_of_eq ?_)
  rw [upperSeq]
  field_simp
  try ring

theorem lowerSeq_le_rsq_width (lam : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam * Real.log 2 < 1) {r : ℕ} (hr : 2 ≤ r)
    (hB : supG r lam = Gfun r lam (1 / 2) (1 / 2)) :
    lowerSeq lam r ≤ (r : ℝ) ^ 2 * width r lam := by
  have hr0 : (0 : ℝ) < r := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (le_trans (by norm_num) hr)
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h := LemmaC.width_ge r lam hr hlam0 hlam1 hB
  have hsq : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  have h' := mul_le_mul_of_nonneg_left h hsq.le
  refine le_trans (le_of_eq ?_) h'
  have hApos : (0 : ℝ) < lam * Real.log 2 := by positivity
  have hden : (0 : ℝ) < 1 - (lam * Real.log 2) ^ 2 / 4 := by nlinarith [hApos, hlam1]
  rw [lowerSeq]
  field_simp
  try ring

/-! ## Theorem 3(a) -/

/-- **Theorem 3(a) (the design notes §6.7-6.8).** Conditional on Lemma B (`hB`), the rescaled
feasibility window converges: `r² · width_r → W(λ) = λ⁴ ln³2 / 64`. -/
theorem width_tendsto (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam * Real.log 2 < 1)
    (hB : ∀ r : ℕ, 2 ≤ r → supG r lam = Gfun r lam (1 / 2) (1 / 2)) :
    Tendsto (fun r : ℕ => (r : ℝ) ^ 2 * width r lam) atTop (𝓝 (Wconst lam)) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (lowerSeq_tendsto lam) (upperSeq_tendsto lam) ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with r hr
    exact lowerSeq_le_rsq_width lam hlam0 hlam1 hr (hB r hr)
  · filter_upwards [eventually_ge_atTop 2] with r hr
    exact rsq_width_le_upperSeq lam hlam0 hlam1 hr

/-! ## Positivity of the window -/

theorem Wconst_pos {lam : ℝ} (hlam0 : 0 < lam) : 0 < Wconst lam := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  rw [Wconst]
  positivity

/-- **Eventual positivity at fixed `λ`.** From Theorem 3(a) and `W(λ) > 0`. -/
theorem width_eventually_pos (lam : ℝ) (hlam0 : 0 < lam) (hlam1 : lam * Real.log 2 < 1)
    (hB : ∀ r : ℕ, 2 ≤ r → supG r lam = Gfun r lam (1 / 2) (1 / 2)) :
    ∀ᶠ r : ℕ in atTop, 0 < width r lam := by
  have h := width_tendsto lam hlam0 hlam1 hB
  have hpos : ∀ᶠ r : ℕ in atTop, 0 < (r : ℝ) ^ 2 * width r lam :=
    h.eventually (eventually_gt_nhds (Wconst_pos hlam0)) |>.mono fun r hr => hr
  filter_upwards [hpos, eventually_ge_atTop 1] with r hr hr1
  have hr0 : (0 : ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hr1
  have hsq : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  nlinarith [hr, hsq]

/-- **Positivity at `λ = 27/20`, every `r ≥ 2`, no limit needed.**
Restatement of `LemmaC.width_pos_at_135`. -/
theorem width_pos_at_135' (r : ℕ) (hr : 2 ≤ r)
    (hB : ∀ r : ℕ, 2 ≤ r → supG r (27 / 20) = Gfun r (27 / 20) (1 / 2) (1 / 2)) :
    0 < width r (27 / 20) :=
  LemmaC.width_pos_at_135 r hr (hB r hr)

/-! ## Unconditional form: `hB` discharged by Lemma B -/

/-- **Theorem 3(a), unconditional** for subcritical `λ ≤ 27/20`: Lemma B
(`LemmaB.supG_eq_center`) discharges the `hB` hypothesis of `width_tendsto`. -/
theorem width_tendsto_unconditional (lam : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam * Real.log 2 < 1) (hlam2 : lam ≤ 27/20) :
    Tendsto (fun r : ℕ => (r : ℝ) ^ 2 * width r lam) atTop (𝓝 (Wconst lam)) :=
  width_tendsto lam hlam0 hlam1
    (fun r hr => LemmaB.supG_eq_center r lam hr hlam0 hlam2)

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
