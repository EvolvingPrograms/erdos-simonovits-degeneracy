import LawDefs
import LemmaC
import CompactnessAndDegeneracy

/-!
# Lemma 6.1: the window upper bound `width_r ≤ W(λ)/r² (1 - 1/r)`

This file formalises Lemma 6.1 of the design notes §6.6 together with all the
ingredients it needs (the global `log cosh` lower bound of §5.1, the exact
binomial moments of §5.2, and the entropy-series lower bound of §5.3 in the
direction used by Step 2 of §6.6).
-/

namespace DegeneracyLaw

open TwoDegenerateGraphs Finset

noncomputable section

/-! ## A monotonicity helper -/

/-- If `f 0 = 0` and `f' ≥ 0` on the interior of a convex set `D ∋ 0`, then
`f ≥ 0` at every nonnegative point of `D`. -/
theorem nonneg_of_deriv_on {D : Set ℝ} (hD : Convex ℝ D) (h0D : (0:ℝ) ∈ D)
    {f f' : ℝ → ℝ} (hf : ∀ x ∈ D, HasDerivAt f (f' x) x)
    (h0 : f 0 = 0) (hp : ∀ x ∈ interior D, 0 ≤ f' x)
    {x : ℝ} (hx : x ∈ D) (hx0 : 0 ≤ x) : 0 ≤ f x := by
  have hmono : MonotoneOn f D :=
    monotoneOn_of_deriv_nonneg hD
      (fun y hy => (hf y hy).continuousAt.continuousWithinAt)
      (fun y hy => ((hf y (interior_subset hy)).differentiableAt).differentiableWithinAt)
      (fun y hy => by rw [(hf y (interior_subset hy)).deriv]; exact hp y hy)
  have := hmono h0D hx hx0
  rwa [h0] at this

/-! ## §5.1: the global `log cosh` lower bound

The two-sided Lemma 5.1 toolkit (`sinh`/`tanh` ladder, `log_cosh_le`,
`le_log_cosh`) has a single home in `LemmaC.lean`.  We only re-export the lower
half here under the name this file and its downstream users refer to. -/

/-- **Lemma 5.1 (lower half).** `t²/2 - t⁴/12 ≤ log cosh t` for every real `t`.
Alias for the canonical `DegeneracyLaw.LemmaC.le_log_cosh`. -/
theorem log_cosh_ge (t : ℝ) : t ^ 2 / 2 - t ^ 4 / 12 ≤ Real.log (Real.cosh t) :=
  LemmaC.le_log_cosh t

/-! ## §5.2: exact binomial moments

`LemmaC.lean` proves these once, for the unnormalised moment
`Mom p r = ∑_j C(r,j) (2j-r)^p` (which unfolds to exactly the sums below).
This section only restates the three instances used by §6.6 in the shape the
rest of this file consumes. -/

/-- `∑_j C(r,j) = 2^r` as reals. -/
theorem binom_M0 (r : ℕ) :
    ∑ j ∈ range (r + 1), (r.choose j : ℝ) = 2 ^ r := by
  have h := LemmaC.Mom_zero r
  simpa [LemmaC.Mom] using h

/-- Second moment: `∑_j C(r,j) (2j-r)² = r 2^r`. -/
theorem binom_M2 (r : ℕ) :
    ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 2
      = (r : ℝ) * 2 ^ r := by
  have h := LemmaC.Mom_two r
  rw [LemmaC.Mom] at h
  rw [h]; ring

/-- Fourth moment: `∑_j C(r,j) (2j-r)⁴ = (3r²-2r) 2^r`. -/
theorem binom_M4 (r : ℕ) :
    ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 4
      = (3 * (r : ℝ) ^ 2 - 2 * (r : ℝ)) * 2 ^ r := by
  have h := LemmaC.Mom_four r
  rw [LemmaC.Mom] at h
  rw [h]; ring

/-! ## §5.3: the entropy defect, lower bound (Step 2 of §6.6) -/

/-- `artanh`-type bound: `log((1/2+x)/(1/2-x)) ≥ 4x + (16/3)x³` on `[0,1/2)`. -/
theorem log_ratio_ge {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1 / 2) :
    4 * x + 16 / 3 * x ^ 3 ≤ Real.log (1 / 2 + x) - Real.log (1 / 2 - x) := by
  have main : 0 ≤ Real.log (1 / 2 + x) - Real.log (1 / 2 - x) - 4 * x - 16 / 3 * x ^ 3 := by
    refine nonneg_of_deriv_on (convex_Ico (0:ℝ) (1/2)) (by norm_num)
      (f := fun t => Real.log (1 / 2 + t) - Real.log (1 / 2 - t) - 4 * t - 16 / 3 * t ^ 3)
      (f' := fun t => 1 / (1 / 2 + t) + 1 / (1 / 2 - t) - 4 - 16 * t ^ 2)
      (fun y hy => ?_) (by norm_num) (fun y hy => ?_)
      (Set.mem_Ico.mpr ⟨hx0, hx⟩) hx0
    · obtain ⟨hy0, hy1⟩ := Set.mem_Ico.mp hy
      have hp : (1 / 2 + y : ℝ) ≠ 0 := by linarith
      have hm : (1 / 2 - y : ℝ) ≠ 0 := by linarith
      have h1 : HasDerivAt (fun t : ℝ => Real.log (1 / 2 + t)) (1 / (1 / 2 + y)) y := by
        have hb : HasDerivAt (fun t : ℝ => 1 / 2 + t) 1 y :=
          (hasDerivAt_id' (x := y)).const_add (1/2 : ℝ)
        exact (hb.log hp).congr_deriv (by ring)
      have h2 : HasDerivAt (fun t : ℝ => Real.log (1 / 2 - t)) (-(1 / (1 / 2 - y))) y := by
        have hb : HasDerivAt (fun t : ℝ => 1 / 2 - t) (-1) y :=
          ((hasDerivAt_id' (x := y)).const_sub (1/2 : ℝ)).congr_deriv (by ring)
        exact (hb.log hm).congr_deriv (by ring)
      have h3 : HasDerivAt (fun t : ℝ => 4 * t) 4 y := by
        simpa using (hasDerivAt_id' (x := y)).const_mul (4 : ℝ)
      have h4 : HasDerivAt (fun t : ℝ => 16 / 3 * t ^ 3) (16 * y ^ 2) y := by
        have h := (hasDerivAt_pow 3 y).const_mul (16 / 3 : ℝ)
        exact h.congr_deriv (by push_cast; ring)
      exact (((h1.sub h2).sub h3).sub h4).congr_deriv (by ring)
    · rw [interior_Ico] at hy
      obtain ⟨hy0, hy1⟩ := Set.mem_Ioo.mp hy
      have hd : (0:ℝ) < 1 / 4 - y ^ 2 := by nlinarith
      have hp : (1 / 2 + y : ℝ) ≠ 0 := by linarith
      have hm : (1 / 2 - y : ℝ) ≠ 0 := by linarith
      have e1 : 1 / (1 / 2 + y) + 1 / (1 / 2 - y) = 1 / (1 / 4 - y ^ 2) := by
        rw [div_add_div _ _ hp hm]
        congr 1 <;> ring
      have e2 : (4 : ℝ) + 16 * y ^ 2 ≤ 1 / (1 / 4 - y ^ 2) := by
        rw [le_div_iff₀ hd]
        nlinarith [sq_nonneg (y ^ 2)]
      rw [e1]
      linarith
  linarith

/-- **§5.3 lower bound.** `log 2 - binEntropy (1/2 - x) ≥ 2x² + (4/3)x⁴` on `[0,1/2)`.
This is the truncation-after-two-terms of the all-positive series (5.2). -/
theorem entropy_defect_ge {x : ℝ} (hx0 : 0 ≤ x) (hx : x < 1 / 2) :
    2 * x ^ 2 + 4 / 3 * x ^ 4 ≤ Real.log 2 - Real.binEntropy (1 / 2 - x) := by
  have hhalf : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
    rw [show (1:ℝ) / 2 = 2⁻¹ by norm_num]; exact Real.binEntropy_two_inv
  have main : 0 ≤ Real.log 2 - Real.binEntropy (1 / 2 - x) - 2 * x ^ 2 - 4 / 3 * x ^ 4 := by
    refine nonneg_of_deriv_on (convex_Ico (0:ℝ) (1/2)) (by norm_num)
      (f := fun t => Real.log 2 - Real.binEntropy (1 / 2 - t) - 2 * t ^ 2 - 4 / 3 * t ^ 4)
      (f' := fun t => (Real.log (1 / 2 + t) - Real.log (1 / 2 - t)) - 4 * t - 16 / 3 * t ^ 3)
      (fun y hy => ?_)
      (by norm_num [hhalf])
      (fun y hy => ?_)
      (Set.mem_Ico.mpr ⟨hx0, hx⟩) hx0
    · obtain ⟨hy0, hy1⟩ := Set.mem_Ico.mp hy
      have hne0 : (1 / 2 - y : ℝ) ≠ 0 := by linarith
      have hne1 : (1 / 2 - y : ℝ) ≠ 1 := by linarith
      have hin : HasDerivAt (fun t : ℝ => 1 / 2 - t) (-1) y :=
        ((hasDerivAt_id' (x := y)).const_sub (1/2 : ℝ)).congr_deriv (by ring)
      have hb := (Real.hasDerivAt_binEntropy hne0 hne1).comp y hin
      have hb' : HasDerivAt (fun t : ℝ => Real.binEntropy (1 / 2 - t))
          (-(Real.log (1 / 2 + y) - Real.log (1 / 2 - y))) y := by
        refine hb.congr_deriv ?_
        have : (1 : ℝ) - (1 / 2 - y) = 1 / 2 + y := by ring
        rw [this]; ring
      have h2 : HasDerivAt (fun t : ℝ => 2 * t ^ 2) (4 * y) y := by
        have h := (hasDerivAt_pow 2 y).const_mul (2 : ℝ)
        exact h.congr_deriv (by push_cast; ring)
      have h4 : HasDerivAt (fun t : ℝ => 4 / 3 * t ^ 4) (16 / 3 * y ^ 3) y := by
        have h := (hasDerivAt_pow 4 y).const_mul (4 / 3 : ℝ)
        exact h.congr_deriv (by push_cast; ring)
      exact ((((hasDerivAt_const y (Real.log 2)).sub hb').sub h2).sub h4).congr_deriv (by ring)
    · rw [interior_Ico] at hy
      obtain ⟨hy0, hy1⟩ := Set.mem_Ioo.mp hy
      have := log_ratio_ge (le_of_lt hy0) hy1
      linarith
  linarith


/-! ## Step 2 of §6.6: the exact value of `G_r` at the centre -/

/-- The two-power factorisation `2^{-λj/r} + 2^{-λ(r-j)/r} = 2^{-λ/2}·2 cosh(a(2j-r)/(2r))`. -/
theorem two_rpow_pair (r : ℕ) (lam : ℝ) (hr : (0:ℝ) < r) (j : ℕ) :
    (2:ℝ) ^ (-(lam * (j:ℝ)) / (r:ℝ)) + (2:ℝ) ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ))
      = (2:ℝ) ^ (-lam / 2 : ℝ) *
          (2 * Real.cosh (lam * Real.log 2 * (2 * (j:ℝ) - (r:ℝ)) / (2 * (r:ℝ)))) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2),
    Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2), Real.cosh_eq]
  have hrne : (r:ℝ) ≠ 0 := ne_of_gt hr
  have e1 : Real.log 2 * (-(lam * (j:ℝ)) / (r:ℝ))
      = Real.log 2 * (-lam / 2)
        + -(lam * Real.log 2 * (2 * (j:ℝ) - (r:ℝ)) / (2 * (r:ℝ))) := by
    field_simp; ring
  have e2 : Real.log 2 * (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ))
      = Real.log 2 * (-lam / 2)
        + lam * Real.log 2 * (2 * (j:ℝ) - (r:ℝ)) / (2 * (r:ℝ)) := by
    field_simp; ring
  rw [e1, e2, Real.exp_add, Real.exp_add]
  ring

/-- **Step 2.** `G_r(1/2,1/2) = centerSum r lam`. -/
theorem Gfun_center_eq (r : ℕ) (lam : ℝ) (hr : 1 ≤ r) :
    Gfun r lam (1/2) (1/2) = centerSum r lam := by
  have hrR : (0:ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hr
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hbin : binaryEntropy (1/2 : ℝ) = 1 := by
    unfold binaryEntropy
    rw [show (1:ℝ)/2 = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
    field_simp
  have hterm : ∀ j ∈ range (r + 1),
      (r.choose j : ℝ) * (1/2 : ℝ) ^ j * (1 - (1/2:ℝ)) ^ (r - j) *
          logTwo (Real.sqrt (1 - (1/2:ℝ)) * 2 ^ (-(lam * (j:ℝ)) / (r:ℝ)) +
            Real.sqrt (1/2 : ℝ) * 2 ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ)))
        = (1/2 - lam/2) * ((r.choose j : ℝ) * (2:ℝ)⁻¹ ^ r)
          + (r.choose j : ℝ) * (2:ℝ)⁻¹ ^ r *
              logTwo (Real.cosh (lam * Real.log 2 * (2 * (j:ℝ) - (r:ℝ)) / (2 * (r:ℝ)))) := by
    intro j hj
    have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hpow : (1/2 : ℝ) ^ j * (1 - (1/2:ℝ)) ^ (r - j) = (2:ℝ)⁻¹ ^ r := by
      rw [show (1 - 1/2 : ℝ) = 1/2 by norm_num, ← pow_add, Nat.add_sub_cancel' hjr,
        show (1/2 : ℝ) = 2⁻¹ by norm_num]
    set m : ℝ := lam * Real.log 2 * (2 * (j:ℝ) - (r:ℝ)) / (2 * (r:ℝ)) with hm
    have hcosh : (0:ℝ) < Real.cosh m := Real.cosh_pos m
    have hc : (0:ℝ) < Real.sqrt (1/2 : ℝ) * ((2:ℝ) ^ (-lam/2 : ℝ) * 2) := by positivity
    have harg : Real.sqrt (1 - (1/2:ℝ)) * 2 ^ (-(lam * (j:ℝ)) / (r:ℝ)) +
          Real.sqrt (1/2 : ℝ) * 2 ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ))
        = (Real.sqrt (1/2 : ℝ) * ((2:ℝ) ^ (-lam/2 : ℝ) * 2)) * Real.cosh m := by
      rw [show (1 - 1/2 : ℝ) = 1/2 by norm_num, ← mul_add, two_rpow_pair r lam hrR j, ← hm]
      ring
    have hlogc : Real.log (Real.sqrt (1/2 : ℝ) * ((2:ℝ) ^ (-lam/2 : ℝ) * 2))
        = (1/2 - lam/2) * Real.log 2 := by
      rw [Real.log_mul (by positivity) (by positivity),
        Real.log_mul (by positivity) (by norm_num),
        Real.log_sqrt (by norm_num), Real.log_rpow (by norm_num),
        show Real.log (1/2 : ℝ) = -Real.log 2 by rw [one_div, Real.log_inv]]
      ring
    have hlt : logTwo (Real.sqrt (1 - (1/2:ℝ)) * 2 ^ (-(lam * (j:ℝ)) / (r:ℝ)) +
          Real.sqrt (1/2 : ℝ) * 2 ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ)))
        = (1/2 - lam/2) + logTwo (Real.cosh m) := by
      unfold logTwo
      rw [harg, Real.log_mul (ne_of_gt hc) (ne_of_gt hcosh), hlogc]
      field_simp
    rw [hlt, mul_assoc ((r.choose j : ℝ)), hpow]
    ring
  have hsum1 : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2:ℝ)⁻¹ ^ r = 1 := by
    rw [← Finset.sum_mul, binom_M0]
    rw [← mul_pow]
    norm_num
  unfold Gfun centerSum
  rw [Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.mul_sum, hsum1, hbin]
  ring


/-! ## Step 1 of §6.6: the centre is a competitor for the supremum -/

/-- A crude but explicit bound on `G_r` over the unit box: enough for `BddAbove`. -/
theorem Gfun_le_bound (r : ℕ) (lam : ℝ) (hr : 1 ≤ r) {q v : ℝ}
    (hq : q ∈ Set.Icc (0:ℝ) 1) (hv : v ∈ Set.Icc (0:ℝ) 1) :
    Gfun r lam q v ≤ 1/2 + (|lam| + 1) := by
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨hv0, hv1⟩ := hv
  have hrR : (0:ℝ) < r := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hr
  have hlog2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  -- entropy part
  have hent : binaryEntropy q / 2 ≤ 1/2 := by
    unfold binaryEntropy
    have h := Real.binEntropy_le_log_two (p := q)
    have : Real.binEntropy q / Real.log 2 ≤ 1 := (div_le_one hlog2).mpr h
    linarith
  -- weights
  set w : ℕ → ℝ := fun j => (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) with hwdef
  have hw0 : ∀ j ∈ range (r + 1), 0 ≤ w j := by
    intro j _
    have : (0:ℝ) ≤ 1 - q := by linarith
    positivity
  have hwsum : ∑ j ∈ range (r + 1), w j = 1 := by
    have h := add_pow q (1 - q) r
    rw [show q + (1 - q) = 1 by ring, one_pow] at h
    rw [h]
    exact Finset.sum_congr rfl (fun j _ => by simp only [hwdef]; ring)
  -- log part
  have hlogbd : ∀ j ∈ range (r + 1),
      logTwo (Real.sqrt (1 - v) * 2 ^ (-(lam * (j:ℝ)) / (r:ℝ)) +
        Real.sqrt v * 2 ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ))) ≤ |lam| + 1 := by
    intro j hj
    have hjr : (j:ℝ) ≤ (r:ℝ) := by
      exact_mod_cast Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hj0 : (0:ℝ) ≤ (j:ℝ) := Nat.cast_nonneg j
    have hA : -(lam * (j:ℝ)) / (r:ℝ) ≤ |lam| := by
      rw [div_le_iff₀ hrR]
      nlinarith [neg_abs_le lam, le_abs_self lam, abs_nonneg lam]
    have hB : -(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ) ≤ |lam| := by
      rw [div_le_iff₀ hrR]
      nlinarith [neg_abs_le lam, le_abs_self lam, abs_nonneg lam]
    have hpA : (2:ℝ) ^ (-(lam * (j:ℝ)) / (r:ℝ)) ≤ (2:ℝ) ^ (|lam| : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hA
    have hpB : (2:ℝ) ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ)) ≤ (2:ℝ) ^ (|lam| : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) hB
    have hs1 : Real.sqrt (1 - v) ≤ 1 := by
      have h := Real.sqrt_le_sqrt (show (1:ℝ) - v ≤ 1 by linarith)
      rwa [Real.sqrt_one] at h
    have hs2 : Real.sqrt v ≤ 1 := by
      have h := Real.sqrt_le_sqrt (show v ≤ (1:ℝ) by linarith)
      rwa [Real.sqrt_one] at h
    have hpApos : (0:ℝ) < (2:ℝ) ^ (-(lam * (j:ℝ)) / (r:ℝ)) := Real.rpow_pos_of_pos (by norm_num) _
    have hpBpos : (0:ℝ) < (2:ℝ) ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have hTle : Real.sqrt (1 - v) * 2 ^ (-(lam * (j:ℝ)) / (r:ℝ)) +
        Real.sqrt v * 2 ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ)) ≤ (2:ℝ) ^ (|lam| + 1 : ℝ) := by
      have e : (2:ℝ) ^ (|lam| + 1 : ℝ) = (2:ℝ) ^ (|lam| : ℝ) * 2 := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]
      rw [e]
      have h1 : Real.sqrt (1 - v) * 2 ^ (-(lam * (j:ℝ)) / (r:ℝ)) ≤ (2:ℝ) ^ (|lam| : ℝ) := by
        calc Real.sqrt (1 - v) * 2 ^ (-(lam * (j:ℝ)) / (r:ℝ))
            ≤ 1 * 2 ^ (-(lam * (j:ℝ)) / (r:ℝ)) :=
              mul_le_mul_of_nonneg_right hs1 (le_of_lt hpApos)
          _ ≤ (2:ℝ) ^ (|lam| : ℝ) := by rw [one_mul]; exact hpA
      have h2 : Real.sqrt v * 2 ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ)) ≤ (2:ℝ) ^ (|lam| : ℝ) := by
        calc Real.sqrt v * 2 ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ))
            ≤ 1 * 2 ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ)) :=
              mul_le_mul_of_nonneg_right hs2 (le_of_lt hpBpos)
          _ ≤ (2:ℝ) ^ (|lam| : ℝ) := by rw [one_mul]; exact hpB
      linarith
    have hTpos : (0:ℝ) < Real.sqrt (1 - v) * 2 ^ (-(lam * (j:ℝ)) / (r:ℝ)) +
        Real.sqrt v * 2 ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ)) := by
      rcases le_or_gt v (1/2) with h | h
      · have : (0:ℝ) < Real.sqrt (1 - v) := Real.sqrt_pos.mpr (by linarith)
        have hnn : (0:ℝ) ≤ Real.sqrt v * 2 ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ)) := by positivity
        nlinarith
      · have : (0:ℝ) < Real.sqrt v := Real.sqrt_pos.mpr (by linarith)
        have hnn : (0:ℝ) ≤ Real.sqrt (1 - v) * 2 ^ (-(lam * (j:ℝ)) / (r:ℝ)) := by positivity
        nlinarith
    unfold logTwo
    rw [div_le_iff₀ hlog2]
    calc Real.log (Real.sqrt (1 - v) * 2 ^ (-(lam * (j:ℝ)) / (r:ℝ)) +
            Real.sqrt v * 2 ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ)))
        ≤ Real.log ((2:ℝ) ^ (|lam| + 1 : ℝ)) := Real.log_le_log hTpos hTle
      _ = (|lam| + 1) * Real.log 2 := Real.log_rpow (by norm_num) _
  -- assemble
  have hsum : ∑ j ∈ range (r + 1), w j *
      logTwo (Real.sqrt (1 - v) * 2 ^ (-(lam * (j:ℝ)) / (r:ℝ)) +
        Real.sqrt v * 2 ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ))) ≤ |lam| + 1 := by
    calc ∑ j ∈ range (r + 1), w j *
          logTwo (Real.sqrt (1 - v) * 2 ^ (-(lam * (j:ℝ)) / (r:ℝ)) +
            Real.sqrt v * 2 ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ)))
        ≤ ∑ j ∈ range (r + 1), w j * (|lam| + 1) :=
          Finset.sum_le_sum (fun j hj =>
            mul_le_mul_of_nonneg_left (hlogbd j hj) (hw0 j hj))
      _ = 1 * (|lam| + 1) := by rw [← Finset.sum_mul, hwsum]
      _ = |lam| + 1 := one_mul _
  unfold Gfun
  have : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) *
      logTwo (Real.sqrt (1 - v) * 2 ^ (-(lam * (j:ℝ)) / (r:ℝ)) +
        Real.sqrt v * 2 ^ (-(lam * ((r:ℝ) - (j:ℝ))) / (r:ℝ))) ≤ |lam| + 1 := hsum
  linarith

/-- The image of the unit box under `G_r` is bounded above. -/
theorem bddAbove_image2_Gfun (r : ℕ) (lam : ℝ) (hr : 1 ≤ r) :
    BddAbove (Set.image2 (Gfun r lam) (Set.Icc 0 1) (Set.Icc 0 1)) := by
  refine ⟨1/2 + (|lam| + 1), ?_⟩
  rintro z hz
  rw [Set.mem_image2] at hz
  obtain ⟨q, hq, v, hv, rfl⟩ := hz
  exact Gfun_le_bound r lam hr hq hv

/-- **Step 1.** The centre value is at most the supremum. -/
theorem centerSum_le_supG (r : ℕ) (lam : ℝ) (hr : 1 ≤ r) :
    Gfun r lam (1/2) (1/2) ≤ supG r lam :=
  le_csSup (bddAbove_image2_Gfun r lam hr)
    (Set.mem_image2_of_mem (by constructor <;> norm_num) (by constructor <;> norm_num))


/-! ## Step 3 of §6.6: the `log cosh` side -/

/-- The binomial `log₂ cosh` average is at least its two-term Taylor lower bound. -/
theorem centerSum_lower (r : ℕ) (lam : ℝ) (hr : 1 ≤ r) :
    ((lam * Real.log 2) ^ 2 / (8 * (r:ℝ)) - (lam * Real.log 2) ^ 4 / (64 * (r:ℝ) ^ 2)
        + (lam * Real.log 2) ^ 4 / (96 * (r:ℝ) ^ 3)) / Real.log 2
      ≤ ∑ j ∈ range (r + 1),
          (r.choose j : ℝ) * 2⁻¹ ^ r *
            logTwo (Real.cosh (lam * Real.log 2 * (2 * j - r : ℝ) / (2 * r))) := by
  have hL : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hr
  have hrne : (r:ℝ) ≠ 0 := ne_of_gt hr0
  have hLne : Real.log 2 ≠ 0 := ne_of_gt hL
  set A : ℝ := (lam * Real.log 2) ^ 2 / (8 * (r:ℝ) ^ 2) with hA
  set B : ℝ := (lam * Real.log 2) ^ 4 / (192 * (r:ℝ) ^ 4) with hB
  have key : ∀ j ∈ range (r + 1),
      (r.choose j : ℝ) * 2⁻¹ ^ r *
          ((A * (2 * (j:ℝ) - (r:ℝ)) ^ 2 - B * (2 * (j:ℝ) - (r:ℝ)) ^ 4) / Real.log 2)
        ≤ (r.choose j : ℝ) * 2⁻¹ ^ r *
            logTwo (Real.cosh (lam * Real.log 2 * (2 * j - r : ℝ) / (2 * r))) := by
    intro j _
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    have h := log_cosh_ge (lam * Real.log 2 * (2 * (j:ℝ) - (r:ℝ)) / (2 * (r:ℝ)))
    have hnum : A * (2 * (j:ℝ) - (r:ℝ)) ^ 2 - B * (2 * (j:ℝ) - (r:ℝ)) ^ 4
        = (lam * Real.log 2 * (2 * (j:ℝ) - (r:ℝ)) / (2 * (r:ℝ))) ^ 2 / 2
          - (lam * Real.log 2 * (2 * (j:ℝ) - (r:ℝ)) / (2 * (r:ℝ))) ^ 4 / 12 := by
      rw [hA, hB]; field_simp; ring
    rw [hnum]
    unfold logTwo
    rw [div_le_div_iff_of_pos_right hL]
    exact h
  refine le_trans (le_of_eq ?_) (Finset.sum_le_sum key)
  have heq : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * 2⁻¹ ^ r *
        ((A * (2 * (j:ℝ) - (r:ℝ)) ^ 2 - B * (2 * (j:ℝ) - (r:ℝ)) ^ 4) / Real.log 2)
      = ((2:ℝ)⁻¹ ^ r / Real.log 2) *
          (A * (∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2 * (j:ℝ) - (r:ℝ)) ^ 2)
            - B * (∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2 * (j:ℝ) - (r:ℝ)) ^ 4)) := by
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [heq, binom_M2, binom_M4]
  have h2 : (2:ℝ)⁻¹ ^ r * (2:ℝ) ^ r = 1 := by rw [← mul_pow]; norm_num
  have hrw : ((2:ℝ)⁻¹ ^ r / Real.log 2) *
        (A * ((r:ℝ) * 2 ^ r) - B * ((3 * (r:ℝ) ^ 2 - 2 * (r:ℝ)) * 2 ^ r))
      = ((2:ℝ)⁻¹ ^ r * (2:ℝ) ^ r) *
          ((1 / Real.log 2) * (A * (r:ℝ) - B * (3 * (r:ℝ) ^ 2 - 2 * (r:ℝ)))) := by
    ring
  rw [hrw, h2, one_mul, hA, hB]
  field_simp
  ring

/-! ## Step 4: assembly — Lemma 6.1 -/

/-- **Lemma 6.1 (the design notes §6.6).** For `r ≥ 2`, `λ > 0` and `λ ln 2 < 2r`
(i.e. `r > a/2`, so `τ_r ∈ (0,1/2)`),
`width_r ≤ (W(λ)/r²)(1 - 1/r)`. No hypothesis on `sup G_r` is used. -/
theorem width_le_mul (r : ℕ) (lam : ℝ) (hr : 2 ≤ r) (hlam : 0 < lam)
    (hra : lam * Real.log 2 < 2 * (r:ℝ)) :
    width r lam ≤ Wconst lam / (r:ℝ) ^ 2 * (1 - 1 / (r:ℝ)) := by
  have hL : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hr0 : (0:ℝ) < (r:ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hr1
  have hrne : (r:ℝ) ≠ 0 := ne_of_gt hr0
  have haPos : (0:ℝ) < lam * Real.log 2 := mul_pos hlam hL
  -- C-side (Step 2 of the paper): lower bound on the entropy defect
  have hC : Cside r (tauOf r lam) ≤
      1 - ((lam * Real.log 2) ^ 2 / (8 * (r:ℝ))
            + (lam * Real.log 2) ^ 4 / (192 * (r:ℝ) ^ 3)) / Real.log 2 := by
    have hx0 : (0:ℝ) ≤ lam * Real.log 2 / (4 * (r:ℝ)) :=
      div_nonneg (le_of_lt haPos) (by linarith)
    have hxlt : lam * Real.log 2 / (4 * (r:ℝ)) < 1 / 2 := by
      rw [div_lt_iff₀ (by linarith)]
      linarith
    have h := entropy_defect_ge hx0 hxlt
    have htau : tauOf r lam = 1 / 2 - lam * Real.log 2 / (4 * (r:ℝ)) := by
      unfold tauOf; ring
    unfold Cside binaryEntropy
    rw [htau]
    set x : ℝ := lam * Real.log 2 / (4 * (r:ℝ)) with hxdef
    have hdiv : Real.binEntropy (1 / 2 - x) / Real.log 2
        ≤ 1 - (2 * x ^ 2 + 4 / 3 * x ^ 4) / Real.log 2 := by
      rw [le_sub_iff_add_le, ← add_div, div_le_one hL]
      linarith
    have hmul := mul_le_mul_of_nonneg_left hdiv (le_of_lt hr0)
    have e : (r:ℝ) * (1 - (2 * x ^ 2 + 4 / 3 * x ^ 4) / Real.log 2)
        = (r:ℝ) - (r:ℝ) * (2 * x ^ 2 + 4 / 3 * x ^ 4) / Real.log 2 := by ring
    rw [e] at hmul
    have e2 : (r:ℝ) * (2 * x ^ 2 + 4 / 3 * x ^ 4) / Real.log 2
        = ((lam * Real.log 2) ^ 2 / (8 * (r:ℝ))
            + (lam * Real.log 2) ^ 4 / (192 * (r:ℝ) ^ 3)) / Real.log 2 := by
      rw [hxdef]; field_simp; ring
    linarith
  -- A-side (Steps 1 & 3): the centre is a competitor, and log cosh is bounded below
  have hA : 1 - (lam * Real.log 2) ^ 2 / (4 * (r:ℝ) * Real.log 2)
      + ((lam * Real.log 2) ^ 2 / (8 * (r:ℝ)) - (lam * Real.log 2) ^ 4 / (64 * (r:ℝ) ^ 2)
          + (lam * Real.log 2) ^ 4 / (96 * (r:ℝ) ^ 3)) / Real.log 2 ≤ Aside r lam := by
    have h1 := centerSum_le_supG r lam hr1
    rw [Gfun_center_eq r lam hr1] at h1
    have h3 := centerSum_lower r lam hr1
    have hlamtau : lam * tauOf r lam
        = lam / 2 - (lam * Real.log 2) ^ 2 / (4 * (r:ℝ) * Real.log 2) := by
      unfold tauOf
      field_simp
    unfold Aside
    unfold centerSum at h1
    rw [hlamtau]
    linarith
  have hfinal : (1 - ((lam * Real.log 2) ^ 2 / (8 * (r:ℝ))
          + (lam * Real.log 2) ^ 4 / (192 * (r:ℝ) ^ 3)) / Real.log 2)
      - (1 - (lam * Real.log 2) ^ 2 / (4 * (r:ℝ) * Real.log 2)
          + ((lam * Real.log 2) ^ 2 / (8 * (r:ℝ)) - (lam * Real.log 2) ^ 4 / (64 * (r:ℝ) ^ 2)
              + (lam * Real.log 2) ^ 4 / (96 * (r:ℝ) ^ 3)) / Real.log 2)
      = Wconst lam / (r:ℝ) ^ 2 * (1 - 1 / (r:ℝ)) := by
    unfold Wconst
    field_simp
    ring
  unfold width
  linarith

/-- **Lemma 6.1, plain form.** `width_r ≤ W(λ)/r²`. -/
theorem width_le (r : ℕ) (lam : ℝ) (hr : 2 ≤ r) (hlam : 0 < lam)
    (hra : lam * Real.log 2 < 2 * (r:ℝ)) :
    width r lam ≤ Wconst lam / (r:ℝ) ^ 2 := by
  have hr0 : (0:ℝ) < (r:ℝ) := by
    exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one (le_trans (by norm_num) hr)
  have hW : (0:ℝ) ≤ Wconst lam := by
    unfold Wconst
    have : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
    positivity
  have h := width_le_mul r lam hr hlam hra
  have hle : Wconst lam / (r:ℝ) ^ 2 * (1 - 1 / (r:ℝ)) ≤ Wconst lam / (r:ℝ) ^ 2 := by
    have h1 : (0:ℝ) ≤ Wconst lam / (r:ℝ) ^ 2 := by positivity
    nlinarith [one_div_pos.mpr hr0]
  linarith


end

end DegeneracyLaw
