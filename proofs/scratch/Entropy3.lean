import CompactnessAndDegeneracy

/-!
# The r = 3 entropy lemma (the Lemma 3.2 analogue)

This file formalises step 3 of `research/THEOREM_r3.md`: the Gibbs/tangent-line
bound on the conditional entropy `H(Z | X₁X₂X₃)` for `X₁,X₂,X₃` i.i.d.
Bernoulli(q).

Everything is in **nats** (`Real.log`, `Real.binEntropy`); the research notes
are in base 2, so every base-2 constant appears here multiplied by `Real.log 2`.
The Gibbs weight is `2 ^ (-7/4)` per unit disagreement (`λ = 7/4` in base 2),
i.e. `θ = exp (-(7/12) * log 2)` per coordinate.
-/

namespace ThreeDegenerateGraphs

open TwoDegenerateGraphs

/-! ## A quartic majorant for the binary entropy

`Real.binEntropy q = log 2 - Σ_{n ≥ 1} (2q-1)^(2n) / (2n(2n-1))`, so every
truncation of the series is an upper bound.  Pinsker (`binary_pinsker`) is the
`n = 1` truncation; the `r = 3` certificate needs the `n ≤ 2` truncation.
-/

noncomputable def quarticGap (q : ℝ) : ℝ :=
  Real.log 2 - Real.binEntropy q - (2 * q - 1) ^ 2 / 2 - (2 * q - 1) ^ 4 / 12

noncomputable def quarticGapDeriv (q : ℝ) : ℝ :=
  Real.log q - Real.log (1 - q) - 2 * (2 * q - 1) - (2 / 3) * (2 * q - 1) ^ 3

noncomputable def quarticGapDerivTwo (q : ℝ) : ℝ :=
  q⁻¹ + (1 - q)⁻¹ - 4 - 4 * (2 * q - 1) ^ 2

theorem quarticGap_continuous : Continuous quarticGap := by
  unfold quarticGap
  fun_prop

theorem quarticGap_hasDerivAt {q : ℝ} (hqzero : q ≠ 0) (hqone : q ≠ 1) :
    HasDerivAt quarticGap (quarticGapDeriv q) q := by
  have hlinear : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 q := by
    simpa using (hasDerivAt_const_mul (x := q) (2 : ℝ)).sub_const 1
  have hderiv :=
    (((Real.hasDerivAt_binEntropy hqzero hqone).const_sub (Real.log 2)).sub
      ((hlinear.pow 2).div_const 2)).sub ((hlinear.pow 4).div_const 12)
  convert hderiv using 1
  all_goals
    first
    | rfl
    | (dsimp [quarticGap, quarticGapDeriv]; ring)

theorem quarticGapDeriv_hasDerivAt {q : ℝ} (hqzero : q ≠ 0) (hqone : q ≠ 1) :
    HasDerivAt quarticGapDeriv (quarticGapDerivTwo q) q := by
  have hlinear : HasDerivAt (fun x : ℝ => 2 * x - 1) 2 q := by
    simpa using (hasDerivAt_const_mul (x := q) (2 : ℝ)).sub_const 1
  have hcomplement : HasDerivAt (fun x : ℝ => 1 - x) (-1) q := by
    simpa using (hasDerivAt_id q).const_sub 1
  have hcomplement_ne : 1 - q ≠ 0 := sub_ne_zero.mpr hqone.symm
  have hderiv :=
    (((Real.hasDerivAt_log hqzero).sub (hcomplement.log hcomplement_ne)).sub
      (hlinear.const_mul 2)).sub ((hlinear.pow 3).const_mul (2 / 3))
  convert hderiv using 1
  all_goals
    first
    | rfl
    | (dsimp [quarticGapDeriv, quarticGapDerivTwo]; ring)

theorem quarticGapDerivTwo_nonneg {q : ℝ} (hqzero : 0 < q) (hqone : q < 1) :
    0 ≤ quarticGapDerivTwo q := by
  have hcomplement : 0 < 1 - q := sub_pos.mpr hqone
  have hidentity :
      quarticGapDerivTwo q = (2 * q - 1) ^ 4 / (q * (1 - q)) := by
    unfold quarticGapDerivTwo
    field_simp [hqzero.ne', hcomplement.ne']
    ring
  rw [hidentity]
  exact div_nonneg (by positivity) (mul_pos hqzero hcomplement).le

theorem quarticGap_convex : ConvexOn ℝ (Set.Icc 0 1) quarticGap := by
  refine convexOn_of_hasDerivWithinAt2_nonneg
    (f' := quarticGapDeriv) (f'' := quarticGapDerivTwo)
    (convex_Icc (0 : ℝ) 1) quarticGap_continuous.continuousOn ?_ ?_ ?_
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hq
    exact (quarticGap_hasDerivAt hq'.1.ne' hq'.2.ne).hasDerivWithinAt
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hq
    exact (quarticGapDeriv_hasDerivAt hq'.1.ne' hq'.2.ne).hasDerivWithinAt
  · intro q hq
    have hq' : q ∈ Set.Ioo (0 : ℝ) 1 := by simpa only [interior_Icc] using hq
    exact quarticGapDerivTwo_nonneg hq'.1 hq'.2

@[simp] theorem quarticGap_half : quarticGap ((2 : ℝ)⁻¹) = 0 := by
  unfold quarticGap
  rw [Real.binEntropy_two_inv]
  norm_num

@[simp] theorem quarticGapDeriv_half : quarticGapDeriv ((2 : ℝ)⁻¹) = 0 := by
  unfold quarticGapDeriv
  norm_num

/-- The order-two truncation of the binary entropy series: a strictly better
majorant than Pinsker, needed for the `r = 3` constant. -/
theorem binary_quartic (q : ℝ) (hqzero : 0 ≤ q) (hqone : q ≤ 1) :
    Real.binEntropy q ≤
      Real.log 2 - (2 * q - 1) ^ 2 / 2 - (2 * q - 1) ^ 4 / 12 := by
  have habove :
      ∀ x : ℝ, 0 ≤ x → x ≤ 1 → (2 : ℝ)⁻¹ ≤ x → 0 ≤ quarticGap x := by
    intro x hxzero hxone hxhalf
    by_cases hxeq : x = (2 : ℝ)⁻¹
    · simp [hxeq]
    · have hxstrict : (2 : ℝ)⁻¹ < x := lt_of_le_of_ne hxhalf (Ne.symm hxeq)
      have hmid : HasDerivAt quarticGap 0 ((2 : ℝ)⁻¹) := by
        convert quarticGap_hasDerivAt (q := (2 : ℝ)⁻¹) (by norm_num)
          (by norm_num) using 1
        exact quarticGapDeriv_half.symm
      have hslope := quarticGap_convex.le_slope_of_hasDerivAt
        (show (2 : ℝ)⁻¹ ∈ Set.Icc 0 1 by constructor <;> norm_num)
        (show x ∈ Set.Icc 0 1 from ⟨hxzero, hxone⟩) hxstrict hmid
      rw [slope_def_field, quarticGap_half, sub_zero] at hslope
      rcases (div_nonneg_iff.mp hslope) with hpositive | hnegative
      · exact hpositive.1
      · exfalso
        have hden : 0 < x - (2 : ℝ)⁻¹ := sub_pos.mpr hxstrict
        linarith [hnegative.2]
  by_cases hhalf : (2 : ℝ)⁻¹ ≤ q
  · have hgap := habove q hqzero hqone hhalf
    unfold quarticGap at hgap
    linarith
  · have hcomplement : (2 : ℝ)⁻¹ ≤ 1 - q := by
      norm_num at hhalf ⊢
      linarith
    have hgap := habove (1 - q) (sub_nonneg.mpr hqone) (by linarith) hcomplement
    unfold quarticGap at hgap
    rw [Real.binEntropy_one_sub] at hgap
    nlinarith [hgap]

/-! ## The Gibbs weight and the tangent points -/

/-- `θ = 2 ^ (-7/12)`: the per-coordinate Gibbs weight for `λ = 7/4`, `r = 3`. -/
noncomputable def theta : ℝ := Real.exp (-(7 / 12 : ℝ) * Real.log 2)

theorem theta_pos : 0 < theta := Real.exp_pos _

/-- `2 ^ (1/8) = θ⁰ / σ₀`. -/
noncomputable def ratioZero : ℝ := Real.exp ((1 / 8 : ℝ) * Real.log 2)
/-- `2 ^ (-11/48) = θ¹ / σ₁`. -/
noncomputable def ratioOne : ℝ := Real.exp (-(11 / 48 : ℝ) * Real.log 2)
/-- `2 ^ (-13/16) = θ² / σ₁`. -/
noncomputable def ratioTwo : ℝ := Real.exp (-(13 / 16 : ℝ) * Real.log 2)
/-- `2 ^ (-13/8) = θ³ / σ₀`. -/
noncomputable def ratioThree : ℝ := Real.exp (-(13 / 8 : ℝ) * Real.log 2)

theorem ratioZero_pos : 0 < ratioZero := Real.exp_pos _
theorem ratioOne_pos : 0 < ratioOne := Real.exp_pos _
theorem ratioTwo_pos : 0 < ratioTwo := Real.exp_pos _
theorem ratioThree_pos : 0 < ratioThree := Real.exp_pos _

/-- Helper: to bound `exp (c * log 2)` it suffices to bound an integer power. -/
theorem exp_log_two_le_of_pow {c : ℝ} {n : ℕ} {b : ℝ} (hn : n ≠ 0)
    (hb : 0 ≤ b) (hpow : Real.exp ((n : ℝ) * c * Real.log 2) ≤ b ^ n) :
    Real.exp (c * Real.log 2) ≤ b := by
  have hexp : Real.exp (c * Real.log 2) ^ n =
      Real.exp ((n : ℝ) * c * Real.log 2) := by
    rw [← Real.exp_nat_mul]; ring_nf
  rw [← hexp] at hpow
  exact (pow_le_pow_iff_left₀ (Real.exp_pos _).le hb hn).mp hpow

theorem exp_two_pow_eq (k : ℤ) :
    Real.exp ((k : ℝ) * Real.log 2) = (2 : ℝ) ^ k := by
  rw [← Real.log_zpow 2 k, Real.exp_log (by positivity)]

theorem ratioZero_le : ratioZero ≤ 10906 / 10000 := by
  refine exp_log_two_le_of_pow (n := 8) (by norm_num) (by norm_num) ?_
  have h : ((8 : ℕ) : ℝ) * (1 / 8 : ℝ) * Real.log 2 = ((1 : ℤ) : ℝ) * Real.log 2 := by
    push_cast; ring
  rw [h, exp_two_pow_eq]
  norm_num

theorem ratioOne_le : ratioOne ≤ 8532 / 10000 := by
  refine exp_log_two_le_of_pow (n := 48) (by norm_num) (by norm_num) ?_
  have h : ((48 : ℕ) : ℝ) * (-(11 / 48 : ℝ)) * Real.log 2
      = ((-11 : ℤ) : ℝ) * Real.log 2 := by push_cast; ring
  rw [h, exp_two_pow_eq]
  norm_num

theorem ratioTwo_le : ratioTwo ≤ 5694 / 10000 := by
  refine exp_log_two_le_of_pow (n := 16) (by norm_num) (by norm_num) ?_
  have h : ((16 : ℕ) : ℝ) * (-(13 / 16 : ℝ)) * Real.log 2
      = ((-13 : ℤ) : ℝ) * Real.log 2 := by push_cast; ring
  rw [h, exp_two_pow_eq]
  norm_num

theorem ratioThree_le : ratioThree ≤ 3243 / 10000 := by
  refine exp_log_two_le_of_pow (n := 8) (by norm_num) (by norm_num) ?_
  have h : ((8 : ℕ) : ℝ) * (-(13 / 8 : ℝ)) * Real.log 2
      = ((-13 : ℤ) : ℝ) * Real.log 2 := by push_cast; ring
  rw [h, exp_two_pow_eq]
  norm_num

/-! ## The tangent points σ₀ = 2^(-1/8), σ₁ = 2^(-17/48) -/

noncomputable def sigmaZero : ℝ := Real.exp (-(1 / 8 : ℝ) * Real.log 2)
noncomputable def sigmaOne : ℝ := Real.exp (-(17 / 48 : ℝ) * Real.log 2)

theorem sigmaZero_pos : 0 < sigmaZero := Real.exp_pos _
theorem sigmaOne_pos : 0 < sigmaOne := Real.exp_pos _

theorem log_sigmaZero : Real.log sigmaZero = -(1 / 8 : ℝ) * Real.log 2 :=
  Real.log_exp _
theorem log_sigmaOne : Real.log sigmaOne = -(17 / 48 : ℝ) * Real.log 2 :=
  Real.log_exp _

private theorem exp_pow_eq (c : ℝ) (n : ℕ) :
    Real.exp (c * Real.log 2) ^ n = Real.exp ((n : ℝ) * c * Real.log 2) := by
  rw [← Real.exp_nat_mul]; ring_nf

theorem inv_sigmaZero : 1 / sigmaZero = ratioZero := by
  unfold sigmaZero ratioZero
  rw [one_div, ← Real.exp_neg]; ring_nf

theorem div_sigmaZero (x : ℝ) : x / sigmaZero = x * ratioZero := by
  rw [div_eq_mul_one_div, inv_sigmaZero]

theorem theta_div_sigmaOne : theta / sigmaOne = ratioOne := by
  unfold theta sigmaOne ratioOne
  rw [← Real.exp_sub]; ring_nf

theorem theta_sq_div_sigmaOne : theta ^ 2 / sigmaOne = ratioTwo := by
  unfold theta sigmaOne ratioTwo
  rw [exp_pow_eq, ← Real.exp_sub]; ring_nf

theorem theta_cube_div_sigmaZero : theta ^ 3 / sigmaZero = ratioThree := by
  unfold theta sigmaZero ratioThree
  rw [exp_pow_eq, ← Real.exp_sub]; ring_nf

/-! ## The two-variable Gibbs potential -/

/-- The `q`-side and `v`-side tangent coefficients.  Here
`z = √(1-v)`, `o = √v`. -/
noncomputable def czPoly (q : ℝ) : ℝ :=
  (1 - q) ^ 3 * ratioZero + 3 * q * (1 - q) ^ 2 * ratioOne +
    3 * q ^ 2 * (1 - q) * ratioTwo + q ^ 3 * ratioThree

noncomputable def coPoly (q : ℝ) : ℝ :=
  (1 - q) ^ 3 * ratioThree + 3 * q * (1 - q) ^ 2 * ratioTwo +
    3 * q ^ 2 * (1 - q) * ratioOne + q ^ 3 * ratioZero

/-- `G(q, v)` in nats, with `z = √(1-v)`, `o = √v`:
`½ h(q) + Σ_j C(3,j) q^j (1-q)^{3-j} log T_j`, `T_j = z θ^j + o θ^{3-j}`. -/
noncomputable def logPotentialThree (q z o : ℝ) : ℝ :=
  Real.binEntropy q / 2 +
    (1 - q) ^ 3 * Real.log (z + o * theta ^ 3) +
    3 * q * (1 - q) ^ 2 * Real.log (z * theta + o * theta ^ 2) +
    3 * q ^ 2 * (1 - q) * Real.log (z * theta ^ 2 + o * theta) +
    q ^ 3 * Real.log (z * theta ^ 3 + o)

private theorem pos_combo {z o a b : ℝ} (hz : 0 ≤ z) (ho : 0 ≤ o)
    (hsum : 0 < z + o) (ha : 0 < a) (hb : 0 < b) : 0 < z * a + o * b := by
  rcases lt_or_eq_of_le hz with h | h
  · nlinarith [mul_pos h ha, mul_nonneg ho hb.le]
  · nlinarith [mul_pos (show (0 : ℝ) < o by linarith) hb, mul_nonneg hz ha.le]

/-- AM-GM linearisation of `√` at the point `m = 51/50`, division-free. -/
private theorem sqrt_le_lin {x : ℝ} (hx : 0 ≤ x) :
    Real.sqrt x ≤ (25 / 51) * x + 51 / 100 := by
  nlinarith [Real.sq_sqrt hx, Real.sqrt_nonneg x,
    sq_nonneg (Real.sqrt x - 51 / 50)]

/-- Step (a) of the certificate: four tangent-line bounds on `log T_j`
followed by Cauchy–Schwarz in the `(z, o)` variables. -/
theorem logPotentialThree_tangent_bound (q z o : ℝ)
    (hqzero : 0 ≤ q) (hqone : q ≤ 1) (hz : 0 ≤ z) (ho : 0 ≤ o)
    (hzo : z ^ 2 + o ^ 2 = 1) :
    logPotentialThree q z o ≤
      Real.binEntropy q / 2 +
        (-(1 / 8 : ℝ) - (11 / 16 : ℝ) * (q * (1 - q))) * Real.log 2 +
        Real.sqrt (czPoly q ^ 2 + coPoly q ^ 2) - 1 := by
  have hsum : 0 < z + o := by nlinarith [sq_nonneg z, sq_nonneg o]
  have ht : 0 < theta := theta_pos
  have ht2 : 0 < theta ^ 2 := by positivity
  have ht3 : 0 < theta ^ 3 := by positivity
  -- positivity of the four log arguments
  have p0 : 0 < z + o * theta ^ 3 := by
    have := pos_combo hz ho hsum one_pos ht3; linarith [this]
  have p1 : 0 < z * theta + o * theta ^ 2 := pos_combo hz ho hsum ht ht2
  have p2 : 0 < z * theta ^ 2 + o * theta := pos_combo hz ho hsum ht2 ht
  have p3 : 0 < z * theta ^ 3 + o := by
    have := pos_combo hz ho hsum ht3 one_pos; linarith [this]
  -- the four tangent-line bounds, with the quotients simplified
  have e0 : (z + o * theta ^ 3) / sigmaZero = z * ratioZero + o * ratioThree := by
    rw [add_div, div_sigmaZero, mul_div_assoc, theta_cube_div_sigmaZero]
  have e1 : (z * theta + o * theta ^ 2) / sigmaOne
      = z * ratioOne + o * ratioTwo := by
    rw [add_div, mul_div_assoc, mul_div_assoc, theta_div_sigmaOne,
      theta_sq_div_sigmaOne]
  have e2 : (z * theta ^ 2 + o * theta) / sigmaOne
      = z * ratioTwo + o * ratioOne := by
    rw [add_div, mul_div_assoc, mul_div_assoc, theta_div_sigmaOne,
      theta_sq_div_sigmaOne]
  have e3 : (z * theta ^ 3 + o) / sigmaZero
      = z * ratioThree + o * ratioZero := by
    rw [add_div, mul_div_assoc, theta_cube_div_sigmaZero, div_sigmaZero]
  have t0 := log_le_tangent p0 sigmaZero_pos
  have t1 := log_le_tangent p1 sigmaOne_pos
  have t2 := log_le_tangent p2 sigmaOne_pos
  have t3 := log_le_tangent p3 sigmaZero_pos
  rw [log_sigmaZero, e0] at t0
  rw [log_sigmaOne, e1] at t1
  rw [log_sigmaOne, e2] at t2
  rw [log_sigmaZero, e3] at t3
  -- weights
  have hc : (0 : ℝ) ≤ 1 - q := by linarith
  have w0 : (0 : ℝ) ≤ (1 - q) ^ 3 := pow_nonneg hc 3
  have w1 : (0 : ℝ) ≤ 3 * q * (1 - q) ^ 2 := by positivity
  have w2 : (0 : ℝ) ≤ 3 * q ^ 2 * (1 - q) := by positivity
  have w3 : (0 : ℝ) ≤ q ^ 3 := by positivity
  have m0 := mul_le_mul_of_nonneg_left t0 w0
  have m1 := mul_le_mul_of_nonneg_left t1 w1
  have m2 := mul_le_mul_of_nonneg_left t2 w2
  have m3 := mul_le_mul_of_nonneg_left t3 w3
  -- Cauchy–Schwarz
  have hcauchy := normalized_binary_cauchy z o (czPoly q) (coPoly q) hzo
  unfold logPotentialThree czPoly at *
  unfold coPoly at *
  linarith [hcauchy, m0, m1, m2, m3]

/-! ## Step (b): the residual two-variable supremum

After the tangent/Cauchy–Schwarz step the whole `(q,v)` supremum collapses to a
single cubic in `w = q(1-q) ∈ [0, 1/4]`. -/

/-- The residual polynomial certificate.  `w = q(1-q)`. -/
theorem residual_cubic_pos (w : ℝ) (h0 : 0 ≤ w) :
    0 < 58535711 / 1700000000 - 2685304529 / 8160000000 * w +
        161696071 / 204000000 * w ^ 2 + 724201 / 102000000 * w ^ 3 := by
  nlinarith [sq_nonneg (w - 207 / 1000), sq_nonneg w, mul_nonneg h0 h0,
    sq_nonneg (w - 1 / 4)]

/-- **The certified bound on the two-variable Gibbs potential.**
`A₀ = 17/80 = 0.2125`, which sits strictly between the interval-arithmetic
certificate `0.20980` of `results_E_certified_sup.md` and the value
`C₃(τ) - λτ = 0.212852…` that the window argument needs. -/
theorem logPotentialThree_le (q z o : ℝ)
    (hqzero : 0 ≤ q) (hqone : q ≤ 1) (hz : 0 ≤ z) (ho : 0 ≤ o)
    (hzo : z ^ 2 + o ^ 2 = 1) :
    logPotentialThree q z o ≤ (17 / 80 : ℝ) * Real.log 2 := by
  have hc : (0 : ℝ) ≤ 1 - q := by linarith
  have w0 : (0 : ℝ) ≤ (1 - q) ^ 3 := pow_nonneg hc 3
  have w1 : (0 : ℝ) ≤ 3 * q * (1 - q) ^ 2 := by positivity
  have w2 : (0 : ℝ) ≤ 3 * q ^ 2 * (1 - q) := by positivity
  have w3 : (0 : ℝ) ≤ q ^ 3 := by positivity
  set Bz : ℝ := (1 - q) ^ 3 * (10906 / 10000) + 3 * q * (1 - q) ^ 2 * (8532 / 10000) +
    3 * q ^ 2 * (1 - q) * (5694 / 10000) + q ^ 3 * (3243 / 10000) with hBz
  set Bo : ℝ := (1 - q) ^ 3 * (3243 / 10000) + 3 * q * (1 - q) ^ 2 * (5694 / 10000) +
    3 * q ^ 2 * (1 - q) * (8532 / 10000) + q ^ 3 * (10906 / 10000) with hBo
  have hczlb : 0 ≤ czPoly q := by
    unfold czPoly
    have := mul_nonneg w0 ratioZero_pos.le
    have := mul_nonneg w1 ratioOne_pos.le
    have := mul_nonneg w2 ratioTwo_pos.le
    have := mul_nonneg w3 ratioThree_pos.le
    linarith
  have hcolb : 0 ≤ coPoly q := by
    unfold coPoly
    have := mul_nonneg w0 ratioThree_pos.le
    have := mul_nonneg w1 ratioTwo_pos.le
    have := mul_nonneg w2 ratioOne_pos.le
    have := mul_nonneg w3 ratioZero_pos.le
    linarith
  have hczub : czPoly q ≤ Bz := by
    unfold czPoly
    rw [hBz]
    have := mul_le_mul_of_nonneg_left ratioZero_le w0
    have := mul_le_mul_of_nonneg_left ratioOne_le w1
    have := mul_le_mul_of_nonneg_left ratioTwo_le w2
    have := mul_le_mul_of_nonneg_left ratioThree_le w3
    linarith
  have hcoub : coPoly q ≤ Bo := by
    unfold coPoly
    rw [hBo]
    have := mul_le_mul_of_nonneg_left ratioThree_le w0
    have := mul_le_mul_of_nonneg_left ratioTwo_le w1
    have := mul_le_mul_of_nonneg_left ratioOne_le w2
    have := mul_le_mul_of_nonneg_left ratioZero_le w3
    linarith
  have hBzpos : 0 ≤ Bz := le_trans hczlb hczub
  have hBopos : 0 ≤ Bo := le_trans hcolb hcoub
  -- bound the Cauchy–Schwarz square root
  have hsq : czPoly q ^ 2 + coPoly q ^ 2 ≤ Bz ^ 2 + Bo ^ 2 :=
    add_le_add (pow_le_pow_left₀ hczlb hczub 2) (pow_le_pow_left₀ hcolb hcoub 2)
  have hsqrt : Real.sqrt (czPoly q ^ 2 + coPoly q ^ 2)
      ≤ (25 / 51) * (Bz ^ 2 + Bo ^ 2) + 51 / 100 :=
    le_trans (Real.sqrt_le_sqrt hsq) (sqrt_le_lin (by positivity))
  -- the entropy majorant
  have hent := binary_quartic q hqzero hqone
  -- log 2 enclosure
  have hLlo : (6931471 / 10000000 : ℝ) ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; norm_num at this ⊢; linarith
  have hLup : Real.log 2 ≤ (6931472 / 10000000 : ℝ) := by
    have := Real.log_two_lt_d9; norm_num at this ⊢; linarith
  have hw0 : (0 : ℝ) ≤ q * (1 - q) := mul_nonneg hqzero hc
  have hlterm : ((13 / 80 : ℝ) - (11 / 16) * (q * (1 - q))) * Real.log 2
      ≤ (13 / 80 : ℝ) * (6931472 / 10000000) -
        (11 / 16) * (q * (1 - q)) * (6931471 / 10000000) := by
    nlinarith [mul_nonneg hw0 (sub_nonneg.mpr hLlo)]
  have hcubic := residual_cubic_pos (q * (1 - q)) hw0
  have hchain := logPotentialThree_tangent_bound q z o hqzero hqone hz ho hzo
  rw [hBz, hBo] at hsqrt
  linarith [hchain, hent, hsqrt, hlterm, hcubic]

/-! ## The entropy lemma (step 3 of `THEOREM_r3.md`)

`X₁, X₂, X₃` i.i.d. Bernoulli(`q`); `Z` any jointly distributed bit.  The type
`j = X₁+X₂+X₃` is a sufficient statistic for the Gibbs step, so the data is
recorded as the four conditional probabilities `pⱼ = P(Z = 1 | type = j)`,
weighted by the binomial masses `C(3,j) qʲ (1-q)³⁻ʲ`.  Then

* `v = P(Z = 1)` is the `p`-average (`hv`),
* `d = (1/3) Σₐ P(Xₐ ≠ Z)` is the average disagreement (`hd`),
* `H(Z | X₁X₂X₃) ≤ Σⱼ P(j) h(pⱼ)` (conditioning on a function of `X⃗`),

and the conclusion is the Lemma 3.2 analogue with `λ = 7/4`, `α = 1/2`. -/
theorem conditional_entropy_bound
    (q v d p₀ p₁ p₂ p₃ : ℝ)
    (hqzero : 0 ≤ q) (hqone : q ≤ 1)
    (hvzero : 0 < v) (hvone : v < 1)
    (hp₀ : 0 ≤ p₀) (hp₀' : p₀ ≤ 1) (hp₁ : 0 ≤ p₁) (hp₁' : p₁ ≤ 1)
    (hp₂ : 0 ≤ p₂) (hp₂' : p₂ ≤ 1) (hp₃ : 0 ≤ p₃) (hp₃' : p₃ ≤ 1)
    (hv : v = (1 - q) ^ 3 * p₀ + 3 * q * (1 - q) ^ 2 * p₁ +
            3 * q ^ 2 * (1 - q) * p₂ + q ^ 3 * p₃)
    (hd : 3 * d = (1 - q) ^ 3 * (3 * p₀) +
            3 * q * (1 - q) ^ 2 * ((1 - p₁) + 2 * p₁) +
            3 * q ^ 2 * (1 - q) * (2 * (1 - p₂) + p₂) +
            q ^ 3 * (3 * (1 - p₃))) :
    (1 - q) ^ 3 * Real.binEntropy p₀ +
        3 * q * (1 - q) ^ 2 * Real.binEntropy p₁ +
        3 * q ^ 2 * (1 - q) * Real.binEntropy p₂ +
        q ^ 3 * Real.binEntropy p₃ ≤
      (17 / 80 : ℝ) * Real.log 2 + (7 / 4 : ℝ) * Real.log 2 * d +
        (Real.binEntropy v - Real.binEntropy q) / 2 := by
  have hc : (0 : ℝ) ≤ 1 - q := by linarith
  have w0 : (0 : ℝ) ≤ (1 - q) ^ 3 := pow_nonneg hc 3
  have w1 : (0 : ℝ) ≤ 3 * q * (1 - q) ^ 2 := by positivity
  have w2 : (0 : ℝ) ≤ 3 * q ^ 2 * (1 - q) := by positivity
  have w3 : (0 : ℝ) ≤ q ^ 3 := by positivity
  set z : ℝ := Real.sqrt (1 - v) with hzdef
  set o : ℝ := Real.sqrt v with hodef
  have hzpos : 0 < z := Real.sqrt_pos.mpr (by linarith)
  have hopos : 0 < o := Real.sqrt_pos.mpr hvzero
  have hz2 : z ^ 2 = 1 - v := Real.sq_sqrt (by linarith)
  have ho2 : o ^ 2 = v := Real.sq_sqrt hvzero.le
  have hzo : z ^ 2 + o ^ 2 = 1 := by rw [hz2, ho2]; ring
  have hlogz : Real.log z = Real.log (1 - v) / 2 :=
    Real.log_sqrt (by linarith)
  have hlogo : Real.log o = Real.log v / 2 := Real.log_sqrt hvzero.le
  have ht : 0 < theta := theta_pos
  have hlogtheta : Real.log theta = -(7 / 12 : ℝ) * Real.log 2 := Real.log_exp _
  have hlogpow : ∀ n : ℕ, Real.log (theta ^ n) = (n : ℝ) * (-(7 / 12 : ℝ) * Real.log 2) := by
    intro n; rw [Real.log_pow, hlogtheta]
  -- the four Gibbs (log-sum) inequalities
  have g₀ := binary_log_sum_bound p₀ z (o * theta ^ 3) hp₀ hp₀' hzpos
    (by positivity)
  have g₁ := binary_log_sum_bound p₁ (z * theta) (o * theta ^ 2) hp₁ hp₁'
    (by positivity) (by positivity)
  have g₂ := binary_log_sum_bound p₂ (z * theta ^ 2) (o * theta) hp₂ hp₂'
    (by positivity) (by positivity)
  have g₃ := binary_log_sum_bound p₃ (z * theta ^ 3) o hp₃ hp₃' (by positivity)
    hopos
  rw [Real.log_mul hopos.ne' (by positivity), hlogpow 3] at g₀
  rw [Real.log_mul hzpos.ne' ht.ne', Real.log_mul hopos.ne' (by positivity),
    hlogtheta, hlogpow 2] at g₁
  rw [Real.log_mul hzpos.ne' (by positivity),
    Real.log_mul hopos.ne' ht.ne', hlogtheta, hlogpow 2] at g₂
  rw [Real.log_mul hzpos.ne' (by positivity), hlogpow 3] at g₃
  -- entropy of v in explicit form
  have hbinv : Real.binEntropy v
      = -(v * Real.log v) - (1 - v) * Real.log (1 - v) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]; ring
  -- the three aggregation identities
  have hA : (1 - q) ^ 3 * (1 - p₀) + 3 * q * (1 - q) ^ 2 * (1 - p₁) +
      3 * q ^ 2 * (1 - q) * (1 - p₂) + q ^ 3 * (1 - p₃) = 1 - v := by
    rw [hv]; ring
  have hZ : (1 - q) ^ 3 * ((1 - p₀) * Real.log z) +
      3 * q * (1 - q) ^ 2 * ((1 - p₁) * Real.log z) +
      3 * q ^ 2 * (1 - q) * ((1 - p₂) * Real.log z) +
      q ^ 3 * ((1 - p₃) * Real.log z)
      = (1 - v) * (Real.log (1 - v) / 2) := by
    rw [← hlogz]; linear_combination Real.log z * hA
  have hO : (1 - q) ^ 3 * (p₀ * Real.log o) +
      3 * q * (1 - q) ^ 2 * (p₁ * Real.log o) +
      3 * q ^ 2 * (1 - q) * (p₂ * Real.log o) +
      q ^ 3 * (p₃ * Real.log o) = v * (Real.log v / 2) := by
    rw [← hlogo]; linear_combination Real.log o * hv.symm
  have hT : ((1 - q) ^ 3 * (3 * p₀) + 3 * q * (1 - q) ^ 2 * ((1 - p₁) + 2 * p₁) +
        3 * q ^ 2 * (1 - q) * (2 * (1 - p₂) + p₂) + q ^ 3 * (3 * (1 - p₃)))
        * (-(7 / 12 : ℝ) * Real.log 2)
      = 3 * d * (-(7 / 12 : ℝ) * Real.log 2) := by
    linear_combination (-(7 / 12 : ℝ) * Real.log 2) * hd.symm
  -- assemble
  have m0 := mul_le_mul_of_nonneg_left g₀ w0
  have m1 := mul_le_mul_of_nonneg_left g₁ w1
  have m2 := mul_le_mul_of_nonneg_left g₂ w2
  have m3 := mul_le_mul_of_nonneg_left g₃ w3
  have hpot := logPotentialThree_le q z o hqzero hqone hzpos.le hopos.le hzo
  unfold logPotentialThree at hpot
  push_cast at m0 m1 m2 m3
  linarith [m0, m1, m2, m3, hpot, hZ, hO, hT, hbinv]

end ThreeDegenerateGraphs
