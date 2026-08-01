import Theorem3b

/-!
# §10.4(c): the asymptotics of `r(1 - β_r)` along the tuned sequence

This file closes the one analytic gap left open in `Theorem3b.lean`: the limit

  `r (1 - β_r) → 1/(8 ln 2)`

which `sixteen_rsq_epsMax_tendsto` took as an explicit hypothesis.  With it,
Theorem 3(b) — `16 r² ε^max_r → 1` — becomes **unconditional**.

## The argument

At the midpoint `β_r = ½(A_r + C_r)` the ledger identity of
`DegeneracyLedger.one_sub_beta_eq` gives, exactly,

  `r (1 - β_r) = r (1 - C_r) + (r² · width_r) / (2 r)`.

* The **second** term tends to `0`: `r² width_r → 1/(64 ln 2)` by
  `DegeneracyLawB.width_tuned_tendsto`, and `1/r → 0`.
* The **first** term is squeezed.  `1 - C_r = r (1 - h(τ_r))` and
  `τ_r = ½ - x_r` with `x_r = a_r/(4r)`, `a_r = λ_r ln 2`.  The two-sided
  entropy-defect bound `DegeneracyLedger.binEntropy_defect_bounds`,

    `(2/ln2) x² ≤ 1 - h(½ - x) ≤ (2/ln2) x² + (3/ln2) x⁴`,

  multiplied by `r²`, gives

    `λ_r² ln2 / 8 ≤ r (1 - C_r) ≤ λ_r² ln2 / 8 + 3 λ_r⁴ ln³2 / (256 r²)`,

  and both sides tend to `(1/ln2)² ln2 / 8 = 1/(8 ln 2)` because
  `λ_r → 1/ln 2` (`DegeneracyLawB.tendsto_lamR`).

The upper half is `DegeneracyLedger.r_mul_one_sub_Cside_le`, already in
`LedgerR.lean`; only the matching lower half (`le_r_mul_one_sub_Cside`) is new.

**This file is `sorry`-free.**
-/

namespace DegeneracyLedger

open Filter Topology DegeneracyLaw TwoDegenerateGraphs

noncomputable section

/-! ## §1 The lower half of the entropy-defect estimate -/

/-- **Companion to `r_mul_one_sub_Cside_le`.**  With `τ_r = 1/2 - λ ln2/(4r)`,

  `r (1 - C_r) = r² (1 - h(τ_r)) ≥ λ² ln 2 / 8`.

This is the `k = 1` term of the all-positive series (5.2), i.e. the lower half
of `binEntropy_defect_bounds`. -/
theorem le_r_mul_one_sub_Cside (r : ℕ) (lam : ℝ) (hr : 1 ≤ r)
    (hlam0 : 0 ≤ lam) (hlam : lam * Real.log 2 ≤ (r : ℝ)) :
    lam ^ 2 * Real.log 2 / 8 ≤ (r : ℝ) * (1 - Cside r (tauOf r lam)) := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hr0 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  set x : ℝ := lam * Real.log 2 / (4 * (r : ℝ)) with hxdef
  have hx0 : 0 ≤ x := by
    have : 0 ≤ lam * Real.log 2 := mul_nonneg hlam0 hlog.le
    positivity
  have hxle : x ≤ 1 / 4 := by
    rw [hxdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hlam, hr0]
  have hxabs : |x| ≤ 1 / 4 := by
    rw [abs_of_nonneg hx0]; linarith
  have htau : tauOf r lam = 1 / 2 - x := by
    simp only [tauOf, hxdef]; try ring
  have hb := (binEntropy_defect_bounds hxabs).1
  have hxsq : x ^ 2 = lam ^ 2 * Real.log 2 ^ 2 / (16 * (r : ℝ) ^ 2) := by
    rw [hxdef]; field_simp; ring
  have hlhs : lam ^ 2 * Real.log 2 / 8
      = (r : ℝ) ^ 2 * (2 / Real.log 2 * x ^ 2) := by
    rw [hxsq]; field_simp; ring
  have hmul : (r : ℝ) ^ 2 * (2 / Real.log 2 * x ^ 2)
      ≤ (r : ℝ) ^ 2 * (1 - binaryEntropy (1 / 2 - x)) :=
    mul_le_mul_of_nonneg_left hb (by positivity)
  calc lam ^ 2 * Real.log 2 / 8 = (r : ℝ) ^ 2 * (2 / Real.log 2 * x ^ 2) := hlhs
    _ ≤ (r : ℝ) ^ 2 * (1 - binaryEntropy (1 / 2 - x)) := hmul
    _ = (r : ℝ) * (1 - Cside r (tauOf r lam)) := by
        rw [one_sub_Cside, htau]; ring

end

end DegeneracyLedger

namespace DegeneracyLawB

open Filter Topology DegeneracyLaw DegeneracyLedger TwoDegenerateGraphs

noncomputable section

/-! ## §2 The two squeezing sequences converge to `1/(8 ln 2)` -/

lemma tendsto_lamSq_log :
    Tendsto (fun r : ℕ => lamR r ^ 2 * Real.log 2 / 8) atTop
      (𝓝 (1 / (8 * Real.log 2))) := by
  have hL := logTwoPos
  have h : Tendsto (fun r : ℕ => lamR r ^ 2 * Real.log 2 / 8) atTop
      (𝓝 ((1 / Real.log 2) ^ 2 * Real.log 2 / 8)) :=
    ((tendsto_lamR.pow 2).mul_const _).div_const _
  have hval : (1 / Real.log 2) ^ 2 * Real.log 2 / 8 = 1 / (8 * Real.log 2) := by
    field_simp
  rwa [hval] at h

lemma tendsto_lamTail :
    Tendsto (fun r : ℕ => lamR r ^ 2 * Real.log 2 / 8
        + 3 * lamR r ^ 4 * Real.log 2 ^ 3 / (256 * (r : ℝ) ^ 2)) atTop
      (𝓝 (1 / (8 * Real.log 2))) := by
  have hL := logTwoPos
  have htail : Tendsto (fun r : ℕ =>
      3 * lamR r ^ 4 * Real.log 2 ^ 3 / 256 * ((1 : ℝ) / (r : ℝ)) ^ 2) atTop
      (𝓝 (3 * (1 / Real.log 2) ^ 4 * Real.log 2 ^ 3 / 256 * (0 : ℝ) ^ 2)) :=
    ((((tendsto_lamR.pow 4).const_mul 3).mul_const _).div_const _).mul
      (tendsto_inv_nat.pow 2)
  norm_num at htail
  have h := tendsto_lamSq_log.add htail
  rw [add_zero] at h
  refine h.congr ?_
  intro r
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr; norm_num
  · have hrne : ((r : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
    field_simp

/-! ## §3 `r (1 - C_r) → 1/(8 ln 2)` along the tuned sequence -/

theorem tendsto_r_one_sub_Cside :
    Tendsto (fun r : ℕ => (r : ℝ) * (1 - Cside r (tauOf r (lamR r)))) atTop
      (𝓝 (1 / (8 * Real.log 2))) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun r : ℕ => lamR r ^ 2 * Real.log 2 / 8)
    (h := fun r : ℕ => lamR r ^ 2 * Real.log 2 / 8
        + 3 * lamR r ^ 4 * Real.log 2 ^ 3 / (256 * (r : ℝ) ^ 2))
    tendsto_lamSq_log tendsto_lamTail ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with r hr
    have hr1 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    exact le_r_mul_one_sub_Cside r (lamR r) (by omega) (lamR_pos hr).le
      (by linarith [(aR_mem hr).2.le])
  · filter_upwards [eventually_ge_atTop 2] with r hr
    exact r_mul_one_sub_Cside_le r (lamR r) hr (lamR_pos hr).le (aR_mem hr).2.le

/-! ## §4 §10.4(c): `r (1 - β_r) → 1/(8 ln 2)` -/

/-- **Paper §10.4(c).**  Along the tuned sequence `λ_r = (1 - ln r/r)/ln 2`, at
the midpoint `β_r = ½(A_r + C_r)`,

  `r (1 - β_r) ⟶ 1/(8 ln 2)`.

This is the hypothesis `hbeta` of `sixteen_rsq_epsMax_tendsto`; with it that
theorem becomes unconditional (see `sixteen_rsq_epsMax_tendsto'`). -/
theorem tendsto_r_one_sub_betaMid :
    Tendsto (fun r : ℕ => (r : ℝ) * (1 - betaMid r (lamR r))) atTop
      (𝓝 (1 / (8 * Real.log 2))) := by
  have hL := logTwoPos
  -- the window term `(r² width_r) · (1/r) / 2 → 0`
  have hwin : Tendsto (fun r : ℕ =>
      ((r : ℝ) ^ 2 * width r (lamR r)) * ((1 : ℝ) / (r : ℝ)) / 2) atTop
      (𝓝 ((1 / (64 * Real.log 2)) * 0 / 2)) :=
    (width_tuned_tendsto.mul tendsto_inv_nat).div_const 2
  rw [mul_zero, zero_div] at hwin
  have h := tendsto_r_one_sub_Cside.add hwin
  rw [add_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with r hr
  have hrne : ((r : ℝ)) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have hdec := one_sub_beta_eq r (lamR r) (betaMid r (lamR r)) (betaMid_spec r (lamR r))
  rw [hdec]
  field_simp

/-! ## §5 Theorem 3(b), unconditional -/

/-- **Theorem 3(b) (PAPER.md Thm 10.6(b)), unconditional.**

Along the tuned sequence `λ_r = λ*(1 - ln r / r)`, at the ledger midpoint `β_r`,

  `16 r² ε^max_r ⟶ 1`,

i.e. `ε^max_r ∼ 1/(16 r²)` — the sharp constant of the paper.  The `hbeta`
hypothesis of `DegeneracyLawB.sixteen_rsq_epsMax_tendsto` is discharged by
`tendsto_r_one_sub_betaMid`. -/
theorem sixteen_rsq_epsMax_tendsto' :
    Tendsto (fun r : ℕ =>
      16 * (r : ℝ) ^ 2 * epsMaxR r (lamR r) (betaMid r (lamR r))) atTop (𝓝 1) :=
  sixteen_rsq_epsMax_tendsto tendsto_r_one_sub_betaMid

end

end DegeneracyLawB
