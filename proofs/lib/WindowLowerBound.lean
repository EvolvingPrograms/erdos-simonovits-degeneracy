import LawDefs

/-!
# Lemma 4.4 machinery: log-cosh bounds, binomial moments, entropy series

Machinery for Lemma 4.4; the window lower bound itself is `Lemma44.lean`.

* §1 A one-sided mean-value helper.
* §2 The two-sided `log cosh` bounds (proved *globally* on `ℝ`,
  which is stronger than the paper's `|t| ≤ 1`).
* §3 The exact binomial moments `E X^2, E X^4, E X^6` for `X = 2J - r`.
* §4 The `C`-side entropy series with an explicit geometric tail.
-/

namespace DegeneracyLaw
namespace LemmaC

open Real Finset

noncomputable section

/-! ## §1 A mean-value helper -/

/-- If `f 0 ≥ 0` and `f' ≥ 0` on `[0,t]`, then `f t ≥ 0`. -/
theorem nonneg_of_deriv_nonneg {f f' : ℝ → ℝ} (hd : ∀ x : ℝ, HasDerivAt f (f' x) x)
    (h0 : 0 ≤ f 0) {t : ℝ} (ht : 0 ≤ t)
    (hf' : ∀ x ∈ Set.Icc (0 : ℝ) t, 0 ≤ f' x) : 0 ≤ f t := by
  have hmono : MonotoneOn f (Set.Icc 0 t) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 t)
      (fun x _ => (hd x).continuousAt.continuousWithinAt)
      (fun x _ => (hd x).differentiableAt.differentiableWithinAt) ?_
    intro x hx
    rw [(hd x).deriv]
    exact hf' x (interior_subset hx)
  exact h0.trans (hmono (Set.left_mem_Icc.2 ht) (Set.right_mem_Icc.2 ht) ht)

/-! ## §2 Two-sided `log cosh` bounds -/

theorem hasDerivAt_cube (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 3 / 3) (x ^ 2) x := by
  have h := (hasDerivAt_pow 3 x).div_const 3
  have e : ((3 : ℕ) : ℝ) * x ^ (3 - 1) / 3 = x ^ 2 := by norm_num
  rwa [e] at h

theorem hasDerivAt_quartic (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 4 / 12) (x ^ 3 / 3) x := by
  have h := (hasDerivAt_pow 4 x).div_const 12
  have e : ((4 : ℕ) : ℝ) * x ^ (4 - 1) / 12 = x ^ 3 / 3 := by norm_num; ring
  rwa [e] at h

theorem hasDerivAt_sextic (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 6 / 45) (2 * x ^ 5 / 15) x := by
  have h := (hasDerivAt_pow 6 x).div_const 45
  have e : ((6 : ℕ) : ℝ) * x ^ (6 - 1) / 45 = 2 * x ^ 5 / 15 := by norm_num; ring
  rwa [e] at h

theorem hasDerivAt_sq_half (x : ℝ) : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
  have h := (hasDerivAt_pow 2 x).div_const 2
  have e : ((2 : ℕ) : ℝ) * x ^ (2 - 1) / 2 = x := by norm_num
  rwa [e] at h

theorem hasDerivAt_quintTerm (x : ℝ) :
    HasDerivAt (fun y : ℝ => 2 * y ^ 5 / 15) (2 * x ^ 4 / 3) x := by
  have h := (HasDerivAt.const_mul (2 : ℝ) (hasDerivAt_pow 5 x)).div_const 15
  have e : (2 : ℝ) * (((5 : ℕ) : ℝ) * x ^ (5 - 1)) / 15 = 2 * x ^ 4 / 3 := by norm_num; ring
  rwa [e] at h

/-- The cubic Taylor polynomial of `tanh`. -/
theorem hasDerivAt_cubicPoly (x : ℝ) :
    HasDerivAt (fun y : ℝ => y - y ^ 3 / 3) (1 - x ^ 2) x := by
  exact (hasDerivAt_id' (x := x)).sub (hasDerivAt_cube x)

/-- The quintic Taylor polynomial of `tanh`. -/
theorem hasDerivAt_quintPoly (x : ℝ) :
    HasDerivAt (fun y : ℝ => y - y ^ 3 / 3 + 2 * y ^ 5 / 15) (1 - x ^ 2 + 2 * x ^ 4 / 3) x :=
  (hasDerivAt_cubicPoly x).add (hasDerivAt_quintTerm x)

/-- `tanh t ≤ t` in the multiplied-out form `sinh t ≤ t · cosh t`, for `t ≥ 0`. -/
theorem sinh_le_mul_cosh {t : ℝ} (ht : 0 ≤ t) : sinh t ≤ t * cosh t := by
  have key : 0 ≤ t * cosh t - sinh t := by
    refine nonneg_of_deriv_nonneg
      (f' := fun x => (1 * cosh x + x * sinh x) - cosh x)
      (fun x => ((hasDerivAt_id x).mul (Real.hasDerivAt_cosh x)).sub (Real.hasDerivAt_sinh x))
      (by simp) ht ?_
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have : 0 ≤ sinh x := Real.sinh_nonneg_iff.2 hx0
    nlinarith
  linarith

/-- `tanh t ≥ t - t³/3`, multiplied out, for `t ≥ 0`. -/
theorem lower_tanh {t : ℝ} (ht : 0 ≤ t) :
    (t - t ^ 3 / 3) * cosh t ≤ sinh t := by
  have key : 0 ≤ sinh t - (t - t ^ 3 / 3) * cosh t := by
    refine nonneg_of_deriv_nonneg
      (f' := fun x => cosh x - ((1 - x ^ 2) * cosh x + (x - x ^ 3 / 3) * sinh x))
      (fun x => (Real.hasDerivAt_sinh x).sub
        ((hasDerivAt_cubicPoly x).mul (Real.hasDerivAt_cosh x)))
      (by simp) ht ?_
    intro x hx
    have hx0 : 0 ≤ x := hx.1
    have hs : 0 ≤ sinh x := Real.sinh_nonneg_iff.2 hx0
    have hc : 0 < cosh x := Real.cosh_pos x
    have hsc : sinh x ≤ x * cosh x := sinh_le_mul_cosh hx0
    rcases le_or_gt 0 (x - x ^ 3 / 3) with hp | hp
    · have h1 : (x - x ^ 3 / 3) * sinh x ≤ (x - x ^ 3 / 3) * (x * cosh x) :=
        mul_le_mul_of_nonneg_left hsc hp
      nlinarith [mul_nonneg (pow_nonneg hx0 4) hc.le]
    · have h1 : (x - x ^ 3 / 3) * sinh x ≤ 0 := mul_nonpos_of_nonpos_of_nonneg hp.le hs
      nlinarith [mul_nonneg (sq_nonneg x) hc.le]
  linarith

/-- `p t = t - t³/3 + 2t⁵/15` is nonnegative for `t ≥ 0`. -/
theorem quintic_nonneg {t : ℝ} (ht : 0 ≤ t) : 0 ≤ t - t ^ 3 / 3 + 2 * t ^ 5 / 15 := by
  nlinarith [sq_nonneg (t ^ 2 - 5 / 4), sq_nonneg t, sq_nonneg (t ^ 2 - 1), pow_nonneg ht 3]

/-- `tanh t ≤ t - t³/3 + 2t⁵/15`, multiplied out, for `t ≥ 0`. -/
theorem upper_tanh {t : ℝ} (ht : 0 ≤ t) :
    sinh t ≤ (t - t ^ 3 / 3 + 2 * t ^ 5 / 15) * cosh t := by
  -- For `t ≥ 2` the polynomial already exceeds `1 ≥ tanh t`.
  rcases le_or_gt t 2 with hle | hgt
  · have key : 0 ≤ (t - t ^ 3 / 3 + 2 * t ^ 5 / 15) * cosh t - sinh t := by
      refine nonneg_of_deriv_nonneg
        (f' := fun x =>
          ((1 - x ^ 2 + 2 * x ^ 4 / 3) * cosh x
            + (x - x ^ 3 / 3 + 2 * x ^ 5 / 15) * sinh x) - cosh x)
        (fun x => ((hasDerivAt_quintPoly x).mul (Real.hasDerivAt_cosh x)).sub
          (Real.hasDerivAt_sinh x))
        (by simp) ht ?_
      intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hx2 : x ≤ 2 := hx.2.trans hle
      have hc : 0 < cosh x := Real.cosh_pos x
      have hlow : (x - x ^ 3 / 3) * cosh x ≤ sinh x := lower_tanh hx0
      have hp : 0 ≤ x - x ^ 3 / 3 + 2 * x ^ 5 / 15 := quintic_nonneg hx0
      -- `p x * sinh x ≥ p x * (x - x³/3) * cosh x ≥ (x² - 2x⁴/3) * cosh x` for `x² ≤ 11/2`.
      have h1 : (x - x ^ 3 / 3 + 2 * x ^ 5 / 15) * ((x - x ^ 3 / 3) * cosh x)
          ≤ (x - x ^ 3 / 3 + 2 * x ^ 5 / 15) * sinh x := by
        exact mul_le_mul_of_nonneg_left hlow hp
      have hnn : 0 ≤ x ^ 6 * (11 - 2 * x ^ 2) * cosh x :=
        mul_nonneg (mul_nonneg (pow_nonneg hx0 6) (by nlinarith)) hc.le
      nlinarith [h1, hnn]
    linarith
  · have hc : 0 < cosh t := Real.cosh_pos t
    have hsc : sinh t ≤ cosh t := by
      have h : cosh t - sinh t = Real.exp (-t) := by
        rw [Real.cosh_eq, Real.sinh_eq]; ring
      nlinarith [Real.exp_pos (-t), h]
    have ht0 : (0:ℝ) ≤ t := by linarith
    have ht3 : (8:ℝ) ≤ t ^ 3 := by
      nlinarith [mul_nonneg (sub_nonneg.2 hgt.le) (by nlinarith [sq_nonneg (t + 1)] :
        (0:ℝ) ≤ t ^ 2 + 2 * t + 4)]
    have h54 : 4 * t ^ 3 ≤ t ^ 5 := by
      nlinarith [mul_nonneg (pow_nonneg ht0 3) (by nlinarith : (0:ℝ) ≤ t ^ 2 - 4)]
    have hp : (1 : ℝ) ≤ t - t ^ 3 / 3 + 2 * t ^ 5 / 15 := by linarith
    calc sinh t ≤ cosh t := hsc
      _ ≤ (t - t ^ 3 / 3 + 2 * t ^ 5 / 15) * cosh t := by nlinarith

/-- **The two-sided log cosh bound, upper branch** — valid on all of `ℝ`. -/
theorem log_cosh_le (t : ℝ) :
    Real.log (Real.cosh t) ≤ t ^ 2 / 2 - t ^ 4 / 12 + t ^ 6 / 45 := by
  have main : ∀ s : ℝ, 0 ≤ s →
      Real.log (Real.cosh s) ≤ s ^ 2 / 2 - s ^ 4 / 12 + s ^ 6 / 45 := by
    intro s hs
    have key : 0 ≤ s ^ 2 / 2 - s ^ 4 / 12 + s ^ 6 / 45 - Real.log (Real.cosh s) := by
      refine nonneg_of_deriv_nonneg
        (f' := fun x => (x - x ^ 3 / 3 + 2 * x ^ 5 / 15) - sinh x / cosh x)
        (fun x => (((hasDerivAt_sq_half x).sub (hasDerivAt_quartic x)).add
            (hasDerivAt_sextic x)).sub
          ((Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne'))
        (by simp) hs ?_
      intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hc : 0 < cosh x := Real.cosh_pos x
      have h := upper_tanh hx0
      have hdiv : sinh x / cosh x ≤ x - x ^ 3 / 3 + 2 * x ^ 5 / 15 := by
        rw [div_le_iff₀ hc]; exact h
      linarith [hdiv]
    linarith
  rcases le_or_gt 0 t with h | h
  · exact main t h
  · have := main (-t) (by linarith)
    rwa [Real.cosh_neg, show (-t) ^ 2 = t ^ 2 by ring, show (-t) ^ 4 = t ^ 4 by ring,
      show (-t) ^ 6 = t ^ 6 by ring] at this

/-- **The two-sided log cosh bound, lower branch** — valid on all of `ℝ`. -/
theorem le_log_cosh (t : ℝ) :
    t ^ 2 / 2 - t ^ 4 / 12 ≤ Real.log (Real.cosh t) := by
  have main : ∀ s : ℝ, 0 ≤ s → s ^ 2 / 2 - s ^ 4 / 12 ≤ Real.log (Real.cosh s) := by
    intro s hs
    have key : 0 ≤ Real.log (Real.cosh s) - (s ^ 2 / 2 - s ^ 4 / 12) := by
      refine nonneg_of_deriv_nonneg
        (f' := fun x => sinh x / cosh x - (x - x ^ 3 / 3))
        (fun x => ((Real.hasDerivAt_cosh x).log (Real.cosh_pos x).ne').sub
          ((hasDerivAt_sq_half x).sub (hasDerivAt_quartic x)))
        (by simp) hs ?_
      intro x hx
      have hx0 : 0 ≤ x := hx.1
      have hc : 0 < cosh x := Real.cosh_pos x
      have h := lower_tanh hx0
      have : x - x ^ 3 / 3 ≤ sinh x / cosh x := by
        rw [le_div_iff₀ hc]; exact h
      linarith
    linarith
  rcases le_or_gt 0 t with h | h
  · exact main t h
  · have := main (-t) (by linarith)
    rwa [Real.cosh_neg, show (-t) ^ 2 = t ^ 2 by ring, show (-t) ^ 4 = t ^ 4 by ring] at this

/-! ## §3 Exact binomial moments (paper (5.1))

`X_r = 2J - r` with `J ~ Bin(r, 1/2)`.  We work with the *unnormalised* moments
`Mom p r = ∑_j C(r,j) (2j-r)^p`; the normalized statement divides by `2^r`. -/

/-- Unnormalised `p`-th moment of `X_r = 2J - r`. -/
def Mom (p r : ℕ) : ℝ := ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ p

/-- Pascal's rule, in the `X = 2j - r` parametrisation:
`E_{r+1} f(X) = E_r [f(X+1) + f(X-1)]` (unnormalised). -/
theorem pascal_sum (r : ℕ) (f : ℝ → ℝ) :
    ∑ j ∈ range (r + 1 + 1), ((r + 1).choose j : ℝ) * f (2 * (j : ℝ) - ((r : ℝ) + 1))
      = (∑ j ∈ range (r + 1), (r.choose j : ℝ) * f (2 * (j : ℝ) - (r : ℝ) + 1))
        + ∑ j ∈ range (r + 1), (r.choose j : ℝ) * f (2 * (j : ℝ) - (r : ℝ) - 1) := by
  classical
  rw [Finset.sum_range_succ' (fun j => ((r + 1).choose j : ℝ) * f (2 * (j : ℝ) - ((r : ℝ) + 1)))
    (r + 1)]
  have step1 : ∀ j ∈ range (r + 1),
      ((r + 1).choose (j + 1) : ℝ) * f (2 * ((j : ℕ) + 1 : ℕ) - ((r : ℝ) + 1))
        = (r.choose j : ℝ) * f (2 * (j : ℝ) - (r : ℝ) + 1)
          + (r.choose (j + 1) : ℝ) * f (2 * ((j : ℕ) + 1 : ℕ) - ((r : ℝ) + 1)) := by
    intro j _
    rw [Nat.choose_succ_succ]
    have harg : (2 : ℝ) * ((j : ℕ) + 1 : ℕ) - ((r : ℝ) + 1) = 2 * (j : ℝ) - (r : ℝ) + 1 := by
      push_cast; ring
    rw [harg]
    push_cast
    ring
  rw [Finset.sum_congr rfl step1, Finset.sum_add_distrib]
  have last : (∑ j ∈ range (r + 1), (r.choose (j + 1) : ℝ) *
        f (2 * ((j : ℕ) + 1 : ℕ) - ((r : ℝ) + 1)))
      + ((r + 1).choose 0 : ℝ) * f (2 * ((0 : ℕ) : ℝ) - ((r : ℝ) + 1))
      = ∑ j ∈ range (r + 1), (r.choose j : ℝ) * f (2 * (j : ℝ) - (r : ℝ) - 1) := by
    have h0 : ((r + 1).choose 0 : ℝ) * f (2 * ((0 : ℕ) : ℝ) - ((r : ℝ) + 1))
        = (r.choose 0 : ℝ) * f (2 * ((0 : ℕ) : ℝ) - (r : ℝ) - 1) := by
      have : (2 : ℝ) * ((0 : ℕ) : ℝ) - ((r : ℝ) + 1) = 2 * ((0 : ℕ) : ℝ) - (r : ℝ) - 1 := by
        push_cast; ring
      rw [this]; simp
    have hcong : ∀ j ∈ range (r + 1),
        (r.choose (j + 1) : ℝ) * f (2 * ((j : ℕ) + 1 : ℕ) - ((r : ℝ) + 1))
          = (r.choose (j + 1) : ℝ) * f (2 * ((j + 1 : ℕ) : ℝ) - (r : ℝ) - 1) := by
      intro j _
      congr 1
      push_cast; ring_nf
    rw [Finset.sum_congr rfl hcong, h0,
      ← Finset.sum_range_succ' (fun j => (r.choose j : ℝ) * f (2 * (j : ℝ) - (r : ℝ) - 1)) (r + 1),
      Finset.sum_range_succ]
    have hz : (r.choose (r + 1) : ℝ) = 0 := by simp
    rw [hz]; ring
  rw [add_assoc, last]

theorem Mom_zero (r : ℕ) : Mom 0 r = 2 ^ r := by
  simp only [Mom, pow_zero, mul_one]
  rw [← Nat.cast_sum, Nat.sum_range_choose]
  push_cast; ring

theorem Mom_succ (p r : ℕ) :
    Mom p (r + 1) = ∑ j ∈ range (r + 1), (r.choose j : ℝ) *
      ((2 * (j : ℝ) - (r : ℝ) + 1) ^ p + (2 * (j : ℝ) - (r : ℝ) - 1) ^ p) := by
  have h := pascal_sum r (fun x => x ^ p)
  simp only [Mom]
  rw [show ((r : ℝ) + 1) = ((r + 1 : ℕ) : ℝ) by push_cast; ring] at h
  rw [h, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring

theorem Mom_two (r : ℕ) : Mom 2 r = 2 ^ r * r := by
  induction r with
  | zero => simp [Mom]
  | succ r ih =>
    rw [Mom_succ]
    have expand : ∀ j ∈ range (r + 1), (r.choose j : ℝ) *
        ((2 * (j : ℝ) - (r : ℝ) + 1) ^ 2 + (2 * (j : ℝ) - (r : ℝ) - 1) ^ 2)
        = 2 * ((r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 2)
          + 2 * ((r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 0) := by
      intro j _; ring
    rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
    have h2 : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 2 = Mom 2 r := rfl
    have h0 : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 0 = Mom 0 r := rfl
    rw [h2, h0, ih, Mom_zero]
    push_cast; ring

theorem Mom_four (r : ℕ) : Mom 4 r = 2 ^ r * (3 * r ^ 2 - 2 * r) := by
  induction r with
  | zero => simp [Mom]
  | succ r ih =>
    rw [Mom_succ]
    have expand : ∀ j ∈ range (r + 1), (r.choose j : ℝ) *
        ((2 * (j : ℝ) - (r : ℝ) + 1) ^ 4 + (2 * (j : ℝ) - (r : ℝ) - 1) ^ 4)
        = 2 * ((r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 4)
          + (12 * ((r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 2)
            + 2 * ((r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 0)) := by
      intro j _; ring
    rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum]
    have h4 : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 4 = Mom 4 r := rfl
    have h2 : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 2 = Mom 2 r := rfl
    have h0 : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 0 = Mom 0 r := rfl
    rw [h4, h2, h0, ih, Mom_two, Mom_zero]
    push_cast; ring

/-- **Paper (5.1), sixth moment**: `E X_r^6 = 15r³ - 30r² + 16r`, unnormalised. -/
theorem Mom_six (r : ℕ) : Mom 6 r = 2 ^ r * (15 * r ^ 3 - 30 * r ^ 2 + 16 * r) := by
  induction r with
  | zero => simp [Mom]
  | succ r ih =>
    rw [Mom_succ]
    have expand : ∀ j ∈ range (r + 1), (r.choose j : ℝ) *
        ((2 * (j : ℝ) - (r : ℝ) + 1) ^ 6 + (2 * (j : ℝ) - (r : ℝ) - 1) ^ 6)
        = 2 * ((r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 6)
          + (30 * ((r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 4)
            + (30 * ((r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 2)
              + 2 * ((r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 0))) := by
      intro j _; ring
    rw [Finset.sum_congr rfl expand, Finset.sum_add_distrib, Finset.sum_add_distrib,
      Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum, ← Finset.mul_sum,
      ← Finset.mul_sum]
    have h6 : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 6 = Mom 6 r := rfl
    have h4 : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 4 = Mom 4 r := rfl
    have h2 : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 2 = Mom 2 r := rfl
    have h0 : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2 * (j : ℝ) - (r : ℝ)) ^ 0 = Mom 0 r := rfl
    rw [h6, h4, h2, h0, ih, Mom_four, Mom_two, Mom_zero]
    push_cast; ring

/-- Normalized sixth moment, the form used in the paper. -/
theorem sixth_moment (r : ℕ) :
    ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r * (2 * (j : ℝ) - (r : ℝ)) ^ 6
      = 15 * (r : ℝ) ^ 3 - 30 * (r : ℝ) ^ 2 + 16 * (r : ℝ) := by
  have h : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r * (2 * (j : ℝ) - (r : ℝ)) ^ 6
      = (2⁻¹ : ℝ) ^ r * Mom 6 r := by
    rw [Mom, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (2⁻¹ : ℝ) ^ r * (2 : ℝ) ^ r = 1 := by
    rw [← mul_pow]; norm_num
  rw [h, Mom_six, ← mul_assoc, h2, one_mul]

/-- Normalized second moment. -/
theorem second_moment (r : ℕ) :
    ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r * (2 * (j : ℝ) - (r : ℝ)) ^ 2
      = (r : ℝ) := by
  have h : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r * (2 * (j : ℝ) - (r : ℝ)) ^ 2
      = (2⁻¹ : ℝ) ^ r * Mom 2 r := by
    rw [Mom, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (2⁻¹ : ℝ) ^ r * (2 : ℝ) ^ r = 1 := by
    rw [← mul_pow]; norm_num
  rw [h, Mom_two, ← mul_assoc, h2, one_mul]

/-- Normalized fourth moment. -/
theorem fourth_moment (r : ℕ) :
    ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r * (2 * (j : ℝ) - (r : ℝ)) ^ 4
      = 3 * (r : ℝ) ^ 2 - 2 * (r : ℝ) := by
  have h : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r * (2 * (j : ℝ) - (r : ℝ)) ^ 4
      = (2⁻¹ : ℝ) ^ r * Mom 4 r := by
    rw [Mom, Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  have h2 : (2⁻¹ : ℝ) ^ r * (2 : ℝ) ^ r = 1 := by
    rw [← mul_pow]; norm_num
  rw [h, Mom_four, ← mul_assoc, h2, one_mul]

/-! ## §4 The `C`-side entropy series (paper (5.2)–(5.3))

With `u = 2x`, `1 - h(1/2 - x)` in *nats* is
`entGap u = ∑_{k ≥ 1} u^{2k} / (2k(2k-1))`, all terms positive. -/

/-- `log 2 - binEntropy ((1-u)/2)`, the entropy deficit in nats. -/
def entGap (u : ℝ) : ℝ := Real.log 2 - Real.binEntropy ((1 - u) / 2)

theorem entGap_eq {u : ℝ} (h : |u| < 1) :
    entGap u = (1 - u) / 2 * Real.log (1 - u) + (1 + u) / 2 * Real.log (1 + u) := by
  have hu := abs_lt.1 h
  have h1 : (0 : ℝ) < 1 - u := by linarith [hu.2]
  have h2 : (0 : ℝ) < 1 + u := by linarith [hu.1]
  have e1 : Real.log ((1 - u) / 2) = Real.log (1 - u) - Real.log 2 := by
    rw [Real.log_div h1.ne' (by norm_num)]
  have e2 : Real.log (1 - (1 - u) / 2) = Real.log (1 + u) - Real.log 2 := by
    rw [show (1 : ℝ) - (1 - u) / 2 = (1 + u) / 2 by ring, Real.log_div h2.ne' (by norm_num)]
  simp only [entGap, Real.binEntropy, Real.log_inv, e1, e2]
  ring

/-- The all-positive power series of the entropy deficit (paper (5.2)). -/
theorem hasSum_entGap {u : ℝ} (h : |u| < 1) :
    HasSum (fun k : ℕ => u ^ (2 * k + 2) / ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)))
      (entGap u) := by
  have hu := abs_lt.1 h
  have h1 : (0 : ℝ) < 1 - u := by linarith [hu.2]
  have h2 : (0 : ℝ) < 1 + u := by linarith [hu.1]
  have hsq : |u ^ 2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg u) h (by norm_num)
  have hodd := (Real.hasSum_log_sub_log_of_abs_lt_one h).mul_left (u / 2)
  have heven := (Real.hasSum_pow_div_log_of_abs_lt_one hsq).mul_left (-(1 / 2) : ℝ)
  have hsum := hodd.add heven
  have hval : (u / 2) * (Real.log (1 + u) - Real.log (1 - u))
      + (-(1 / 2) : ℝ) * (-Real.log (1 - u ^ 2)) = entGap u := by
    rw [entGap_eq h, show (1 : ℝ) - u ^ 2 = (1 - u) * (1 + u) by ring,
      Real.log_mul h1.ne' h2.ne']
    ring
  rw [hval] at hsum
  have hfun : (fun k : ℕ => u ^ (2 * k + 2) / ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)))
      = fun k : ℕ => (u / 2) * ((2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * u ^ (2 * k + 1))
          + (-(1 / 2) : ℝ) * ((u ^ 2) ^ (k + 1) / ((k : ℝ) + 1)) := by
    funext k
    have hk1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have hk2 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hp : (u ^ 2) ^ (k + 1) = u ^ (2 * k + 2) := by
      rw [← pow_mul]; ring_nf
    rw [hp]
    have hq : u ^ (2 * k + 2) = u ^ (2 * k + 1) * u := by rw [← pow_succ]
    rw [hq]
    field_simp
    ring
  rw [hfun]
  exact hsum

/-- Lower bound: the leading term (paper (5.2), all terms positive). -/
theorem entGap_lower {u : ℝ} (h : |u| < 1) : u ^ 2 / 2 ≤ entGap u := by
  have hs := hasSum_entGap h
  have := le_hasSum hs 0 (fun j _ => by
    have : (0 : ℝ) ≤ u ^ (2 * j + 2) := by
      rw [show 2 * j + 2 = 2 * (j + 1) by ring, pow_mul]
      positivity
    positivity)
  simpa using this

/-- Upper bound with the explicit geometric tail (paper (5.3)). -/
theorem entGap_upper {u : ℝ} (h : |u| < 1) :
    entGap u ≤ u ^ 2 / 2 + u ^ 4 / 12 + u ^ 6 / (30 * (1 - u ^ 2)) := by
  have hs := hasSum_entGap h
  have hu2 : u ^ 2 < 1 := by
    have : |u| ^ 2 < 1 := pow_lt_one₀ (abs_nonneg u) h (by norm_num)
    rwa [← abs_pow, abs_of_nonneg (sq_nonneg u)] at this
  have hu2' : (0 : ℝ) ≤ u ^ 2 := sq_nonneg u
  set f : ℕ → ℝ := fun k => u ^ (2 * k + 2) / ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)) with hf
  have hsplit := hs.summable.sum_add_tsum_nat_add 2
  rw [hs.tsum_eq] at hsplit
  -- geometric majorant for the tail
  have hgeo : HasSum (fun k : ℕ => u ^ 6 / 30 * (u ^ 2) ^ k) (u ^ 6 / 30 * (1 - u ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one hu2' hu2).mul_left _
  have hle : ∀ k : ℕ, f (k + 2) ≤ u ^ 6 / 30 * (u ^ 2) ^ k := by
    intro k
    have hpow : u ^ (2 * (k + 2) + 2) = u ^ 6 * (u ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; ring_nf
    have hpos : (0 : ℝ) ≤ u ^ 6 * (u ^ 2) ^ k := by positivity
    have hd : (30 : ℝ) ≤ (2 * ((k : ℕ) + 2 : ℕ) + 1) * (2 * ((k : ℕ) + 2 : ℕ) + 2) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    simp only [hf]
    rw [hpow]
    rw [div_le_iff₀ (by push_cast; positivity)]
    nlinarith [hpos, hd]
  have htail : ∑' k : ℕ, f (k + 2) ≤ u ^ 6 / 30 * (1 - u ^ 2)⁻¹ := by
    refine le_trans (Summable.tsum_le_tsum hle ((summable_nat_add_iff 2).2 hs.summable)
      hgeo.summable) ?_
    exact le_of_eq hgeo.tsum_eq
  have hfin : ∑ k ∈ range 2, f k = u ^ 2 / 2 + u ^ 4 / 12 := by
    simp [hf, Finset.sum_range_succ]
    ring
  have : entGap u = ∑ k ∈ range 2, f k + ∑' k : ℕ, f (k + 2) := hsplit.symm
  rw [this, hfin]
  have : u ^ 6 / (30 * (1 - u ^ 2)) = u ^ 6 / 30 * (1 - u ^ 2)⁻¹ := by
    rw [div_mul_eq_div_div]
    ring
  rw [this]
  linarith [htail]

open TwoDegenerateGraphs in
/-- The two-sided `C`-side bound in **bits**, for `|x| ≤ 1/4` (paper §5.3). -/
theorem binaryEntropy_gap_bounds {x : ℝ} (hx : |x| ≤ 1 / 4) :
    2 / Real.log 2 * x ^ 2 ≤ 1 - binaryEntropy (1 / 2 - x) ∧
      1 - binaryEntropy (1 / 2 - x) ≤ 2 / Real.log 2 * x ^ 2 + 3 / Real.log 2 * x ^ 4 := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have habs : |2 * x| < 1 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith [hx]
  have hhalf : (1 : ℝ) / 2 - x = (1 - 2 * x) / 2 := by ring
  have hgap : 1 - binaryEntropy (1 / 2 - x) = entGap (2 * x) / Real.log 2 := by
    rw [hhalf]
    simp only [binaryEntropy, entGap]
    field_simp
  have hx2 : x ^ 2 ≤ 1 / 16 := by
    have := abs_le.1 hx
    nlinarith [this.1, this.2]
  have hu2 : (2 * x) ^ 2 ≤ 1 / 4 := by nlinarith [hx2]
  constructor
  · rw [hgap, le_div_iff₀ hlog]
    have := entGap_lower habs
    have hx' : (2 * x) ^ 2 / 2 = 2 * x ^ 2 := by ring
    rw [hx'] at this
    calc 2 / Real.log 2 * x ^ 2 * Real.log 2 = 2 * x ^ 2 := by field_simp
      _ ≤ entGap (2 * x) := this
  · rw [hgap, div_le_iff₀ hlog]
    have hub := entGap_upper habs
    have hden : (0 : ℝ) < 1 - (2 * x) ^ 2 := by nlinarith [hu2]
    have htail : (2 * x) ^ 6 / (30 * (1 - (2 * x) ^ 2)) ≤ 4 * x ^ 4 / 3 := by
      rw [div_le_div_iff₀ (by nlinarith [hden]) (by norm_num)]
      nlinarith [hx2, hden, sq_nonneg x, pow_nonneg (sq_nonneg x) 2,
        mul_nonneg (pow_nonneg (sq_nonneg x) 2) (sq_nonneg x)]
    have : entGap (2 * x) ≤ 2 * x ^ 2 + 4 * x ^ 4 / 3 + 4 * x ^ 4 / 3 := by
      have e1 : (2 * x) ^ 2 / 2 = 2 * x ^ 2 := by ring
      have e2 : (2 * x) ^ 4 / 12 = 4 * x ^ 4 / 3 := by ring
      rw [e1, e2] at hub
      linarith [hub, htail]
    calc entGap (2 * x) ≤ 2 * x ^ 2 + 4 * x ^ 4 / 3 + 4 * x ^ 4 / 3 := this
      _ ≤ (2 / Real.log 2 * x ^ 2 + 3 / Real.log 2 * x ^ 4) * Real.log 2 := by
          field_simp
          nlinarith [pow_nonneg (sq_nonneg x) 2, sq_nonneg x]

/-! ## §5 Assembly (paper §5.4, bound (5.6)) -/

open TwoDegenerateGraphs

/-- The binomial weights sum to one. -/
theorem weights_sum (r : ℕ) : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r = 1 := by
  rw [← Finset.sum_mul, ← Nat.cast_sum, Nat.sum_range_choose]
  push_cast
  rw [← mul_pow]
  norm_num

/-- **Center value identity** (paper (4.13)/(6.6)):
`G_r(1/2,1/2) = 1 - λ/2 + E log₂ cosh(a X_r /(2r))`. -/
theorem Gfun_center_eq (r : ℕ) (hr : 1 ≤ r) (lam : ℝ) :
    Gfun r lam (1 / 2) (1 / 2) = centerSum r lam := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hsqrt : Real.sqrt (1 / 2 : ℝ) > 0 := Real.sqrt_pos.2 (by norm_num)
  have hterm : ∀ j ∈ range (r + 1),
      (r.choose j : ℝ) * (1 / 2 : ℝ) ^ j * (1 - 1 / 2 : ℝ) ^ (r - j) *
          logTwo (Real.sqrt (1 - 1 / 2) * 2 ^ (-(lam * j) / r) +
            Real.sqrt (1 / 2) * 2 ^ (-(lam * (r - j : ℝ)) / r))
        = (r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r * (1 / 2 - lam / 2)
          + (r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r *
              logTwo (Real.cosh (lam * Real.log 2 * (2 * j - r : ℝ) / (2 * r))) := by
    intro j hj
    have hjr : j ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
    have hw : (1 / 2 : ℝ) ^ j * (1 - 1 / 2 : ℝ) ^ (r - j) = (2⁻¹ : ℝ) ^ r := by
      rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, ← pow_add, Nat.add_sub_cancel' hjr]
      norm_num
    -- rewrite the bracket as `√(1/2) * (2 * exp (-a/2)) * cosh t`
    set A : ℝ := lam * Real.log 2 with hA
    set t : ℝ := A * (2 * (j : ℝ) - r) / (2 * r) with ht
    have hrpow : ∀ y : ℝ, (2 : ℝ) ^ y = Real.exp (Real.log 2 * y) := fun y =>
      Real.rpow_def_of_pos (by norm_num) y
    have hbr : Real.sqrt (1 - 1 / 2 : ℝ) * 2 ^ (-(lam * j) / r) +
        Real.sqrt (1 / 2 : ℝ) * 2 ^ (-(lam * (r - j : ℝ)) / r)
        = Real.sqrt (1 / 2 : ℝ) * (2 * Real.exp (-(A / 2))) * Real.cosh t := by
      rw [show (1 - 1 / 2 : ℝ) = 1 / 2 by norm_num, hrpow, hrpow, Real.cosh_eq]
      have e1 : Real.log 2 * (-(lam * j) / r) = -(A / 2) + -t := by
        rw [hA, ht]; field_simp; ring
      have e2 : Real.log 2 * (-(lam * ((r : ℝ) - j)) / r) = -(A / 2) + t := by
        rw [hA, ht]; field_simp; ring
      rw [e1, e2, Real.exp_add, Real.exp_add]
      ring
    rw [hbr, mul_assoc ((r.choose j : ℝ)), hw]
    have hc : (0 : ℝ) < Real.cosh t := Real.cosh_pos t
    have hfac : (0 : ℝ) < 2 * Real.exp (-(A / 2)) := by positivity
    have hlogexp : Real.log (Real.sqrt (1 / 2 : ℝ) * (2 * Real.exp (-(A / 2))))
        = Real.log 2 / 2 - A / 2 := by
      rw [Real.log_mul hsqrt.ne' hfac.ne', Real.log_mul (by norm_num) (Real.exp_pos _).ne',
        Real.log_exp, Real.log_sqrt (by norm_num)]
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.log_inv]
      ring
    rw [logTwo, Real.log_mul (by positivity) hc.ne', hlogexp, logTwo]
    field_simp
    ring
  rw [Gfun, centerSum, Finset.sum_congr rfl hterm, Finset.sum_add_distrib, ← Finset.sum_mul]
  rw [weights_sum]
  have hbe : binaryEntropy (1 / 2 : ℝ) = 1 := by
    rw [binaryEntropy, show (1 / 2 : ℝ) = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
    field_simp
  rw [hbe]
  ring

/-- The `A`-side, under Lemma 4.2. -/
theorem Aside_eq (r : ℕ) (hr : 1 ≤ r) (lam : ℝ)
    (hB : supG r lam = Gfun r lam (1 / 2) (1 / 2)) :
    Aside r lam = 1 - (lam * Real.log 2) ^ 2 / (4 * r * Real.log 2)
      + ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r *
          logTwo (Real.cosh (lam * Real.log 2 * (2 * j - r : ℝ) / (2 * r))) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have haux : lam * (1 / 2 - lam * Real.log 2 / (4 * r))
      = lam / 2 - (lam * Real.log 2) ^ 2 / (4 * r * Real.log 2) := by
    field_simp
  rw [Aside, hB, Gfun_center_eq r hr lam, centerSum, tauOf, haux]
  ring_nf

/-- Bound on the `log cosh` average, via the two-sided log cosh bounds and the exact moments. -/
theorem centerSum_le (r : ℕ) (hr : 1 ≤ r) (lam : ℝ) :
    ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r *
        logTwo (Real.cosh (lam * Real.log 2 * (2 * j - r : ℝ) / (2 * r)))
      ≤ (1 / Real.log 2) * ((lam * Real.log 2) ^ 2 / (8 * r)
          - (lam * Real.log 2) ^ 4 * (3 * (r : ℝ) ^ 2 - 2 * r) / (192 * (r : ℝ) ^ 4)
          + (lam * Real.log 2) ^ 6 * (15 * (r : ℝ) ^ 3 - 30 * (r : ℝ) ^ 2 + 16 * r) /
              (2880 * (r : ℝ) ^ 6)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set A : ℝ := lam * Real.log 2 with hA
  -- termwise bound
  have hstep : ∀ j ∈ range (r + 1),
      (r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r * logTwo (Real.cosh (A * (2 * (j : ℝ) - r) / (2 * r)))
        ≤ (1 / Real.log 2) *
            ((A / (2 * r)) ^ 2 / 2 * ((r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r * (2 * (j : ℝ) - r) ^ 2)
              - (A / (2 * r)) ^ 4 / 12 *
                  ((r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r * (2 * (j : ℝ) - r) ^ 4)
              + (A / (2 * r)) ^ 6 / 45 *
                  ((r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r * (2 * (j : ℝ) - r) ^ 6)) := by
    intro j _
    have hw : (0 : ℝ) ≤ (r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r := by positivity
    have hbound := log_cosh_le (A * (2 * (j : ℝ) - r) / (2 * r))
    have hkey : logTwo (Real.cosh (A * (2 * (j : ℝ) - r) / (2 * r)))
        ≤ (1 / Real.log 2) * ((A * (2 * (j : ℝ) - r) / (2 * r)) ^ 2 / 2
          - (A * (2 * (j : ℝ) - r) / (2 * r)) ^ 4 / 12
          + (A * (2 * (j : ℝ) - r) / (2 * r)) ^ 6 / 45) := by
      rw [logTwo, div_le_iff₀ hlog]
      calc Real.log (Real.cosh (A * (2 * (j : ℝ) - r) / (2 * r)))
          ≤ (A * (2 * (j : ℝ) - r) / (2 * r)) ^ 2 / 2
            - (A * (2 * (j : ℝ) - r) / (2 * r)) ^ 4 / 12
            + (A * (2 * (j : ℝ) - r) / (2 * r)) ^ 6 / 45 := hbound
        _ = _ := by field_simp
    have := mul_le_mul_of_nonneg_left hkey hw
    refine this.trans (le_of_eq ?_)
    field_simp
    try ring
  refine (Finset.sum_le_sum hstep).trans (le_of_eq ?_)
  rw [← Finset.mul_sum]
  congr 1
  rw [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum, ← Finset.mul_sum,
    ← Finset.mul_sum, second_moment, fourth_moment, sixth_moment]
  field_simp
  ring

/-- The `C`-side upper bound (paper (5.3)). -/
theorem Cside_gap_le (r : ℕ) (hr : 1 ≤ r) (lam : ℝ) (hlam : 0 < lam)
    (hlam' : lam * Real.log 2 < 1) :
    (r : ℝ) * (1 - binaryEntropy (tauOf r lam))
      ≤ (1 / Real.log 2) * ((lam * Real.log 2) ^ 2 / (8 * r)
          + (lam * Real.log 2) ^ 4 / (192 * (r : ℝ) ^ 3))
        + (lam * Real.log 2) ^ 6 /
            (1920 * Real.log 2 * (r : ℝ) ^ 5 * (1 - (lam * Real.log 2) ^ 2 / 4)) := by
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set A : ℝ := lam * Real.log 2 with hA
  have hApos : 0 < A := by positivity
  set x : ℝ := A / (4 * r) with hx
  have hxpos : 0 < x := by positivity
  have hxle : x ≤ 1 / 4 := by
    rw [hx, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hlam'.le, hr1]
  have habs : |2 * x| < 1 := by
    rw [abs_of_pos (by positivity)]
    nlinarith [hxle]
  have htau : tauOf r lam = 1 / 2 - x := by rw [tauOf, hx, hA]; try ring
  have hgap : 1 - binaryEntropy (tauOf r lam) = entGap (2 * x) / Real.log 2 := by
    rw [htau, show (1 : ℝ) / 2 - x = (1 - 2 * x) / 2 by ring]
    simp only [binaryEntropy, entGap]
    field_simp
  rw [hgap]
  have hub := entGap_upper habs
  have hden : (0 : ℝ) < 1 - (2 * x) ^ 2 := by nlinarith [hxle, hxpos]
  have hden2 : (0 : ℝ) < 1 - A ^ 2 / 4 := by nlinarith [hlam', hApos]
  -- the tail is monotone in `r`
  have htail : (2 * x) ^ 6 / (30 * (1 - (2 * x) ^ 2))
      ≤ A ^ 6 / (1920 * (r : ℝ) ^ 6 * (1 - A ^ 2 / 4)) := by
    have e : (2 * x) ^ 6 = A ^ 6 / (64 * (r : ℝ) ^ 6) := by
      rw [hx]; field_simp; ring
    have hle : (1 : ℝ) - A ^ 2 / 4 ≤ 1 - (2 * x) ^ 2 := by
      have : (2 * x) ^ 2 = A ^ 2 / (4 * (r : ℝ) ^ 2) := by rw [hx]; field_simp; ring
      rw [this]
      have : A ^ 2 / (4 * (r : ℝ) ^ 2) ≤ A ^ 2 / 4 := by
        apply div_le_div_of_nonneg_left (by positivity) (by norm_num)
        nlinarith [hr1]
      linarith
    rw [e]
    rw [div_div, div_le_div_iff₀ (by positivity) (by positivity)]
    have hA6 : (0 : ℝ) ≤ A ^ 6 := by positivity
    nlinarith [mul_nonneg (mul_nonneg hA6 (pow_nonneg hr0.le 6)) (sub_nonneg.2 hle)]
  have hmain : entGap (2 * x) ≤ (2 * x) ^ 2 / 2 + (2 * x) ^ 4 / 12
      + A ^ 6 / (1920 * (r : ℝ) ^ 6 * (1 - A ^ 2 / 4)) := by linarith [hub, htail]

  have e2 : (2 * x) ^ 2 / 2 = A ^ 2 / (8 * (r : ℝ) ^ 2) := by rw [hx]; field_simp; ring
  have e4 : (2 * x) ^ 4 / 12 = A ^ 4 / (192 * (r : ℝ) ^ 4) := by rw [hx]; field_simp; ring
  rw [e2, e4] at hmain
  have hfinal : (r : ℝ) * (entGap (2 * x) / Real.log 2)
      ≤ (1 / Real.log 2) * (A ^ 2 / (8 * r) + A ^ 4 / (192 * (r : ℝ) ^ 3))
        + A ^ 6 / (1920 * Real.log 2 * (r : ℝ) ^ 5 * (1 - A ^ 2 / 4)) := by
    rw [mul_div_assoc']
    rw [div_le_iff₀ hlog]
    have hmul := mul_le_mul_of_nonneg_left hmain hr0.le
    refine hmul.trans (le_of_eq ?_)
    field_simp
    try ring
  exact hfinal


end

end LemmaC
end DegeneracyLaw
