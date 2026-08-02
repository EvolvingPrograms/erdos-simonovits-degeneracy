import LedgerR
import LedgerAsym

/-!
# The sharp ledger: r-aware `K₁` and the `(θ, η)`-parametric constant

`LedgerR` freezes its numeric bounds at their `r = 2` worst case *and* uses
the loosened entropy-defect coefficient `3/ln 2` on `x⁴`, which is what
limits Theorem 2's explicit constant to `1/(110 r²)` at the midpoint with
slack `η = ½`.  This file sharpens each ingredient atomically:

* `binEntropy_defect_upper_sharp` — the true quartic coefficient
  `4/(3 ln 2)`, keeping the sextic tail as a separate `x⁶` term (a direct
  reassembly of `entGap_upper`, which already carries the sharp series);
* `r_one_sub_Cside_sharp` — the r-aware entropy-defect side of (W3):
  `r(1 - C_r) ≤ λ²ln2/8 + λ⁴ln³2/(192 r²) + λ⁶ln⁵2/(1280 r⁴)`;
* `r_width_term_le` and `inv_sub_inv_sq_le_quarter` — the window side, from
  `width_le_mul`, with `1/r - 1/r² ≤ 1/4` for `r ≥ 2` (that is `(r-2)² ≥ 0`);
* `one_sub_betaTheta` and `K1_theta_bound` — `K₁` for the whole in-window
  family `β_θ = A + θ·width`, assembled from the two sides;
* `epsR_theta_lower` — the `(θ, η)`-parametric Lemma 8.3:
  `ε ≥ (1-η)(1-θ) w / (K₁ r²)`;
* numeric instantiations at `λ = 27/20`:
  `K1_quarter_le` (`≤ 0.1627`), `K1_half_le` (`≤ 0.1616`), and the two
  constants they certify with `w = 0.00603` —
  `1/(48 r²)` at `(θ, η) = (¼, ¼)` and `1/(108 r²)` at the midpoint.

The `1/(48 r²)` beats the paper's midpoint constant `1/(107 r²)`; the
midpoint checkpoint here is `1/(108 r²)` (reaching `107` exactly needs the
per-`r` interval evaluation of `width(2)`, kept as separate work).
-/

namespace DegeneracyLedgerSharp

open TwoDegenerateGraphs DegeneracyLaw DegeneracyLedger DegeneracyLawB Finset

/-! ## §1 The sharp entropy-defect upper bound -/

/-- The sharp quartic: `1 - h(½ - x) ≤ (2x² + (4/3)x⁴ + (16/5)x⁶)/ln 2` for
`|x| ≤ ¼`.  Direct from `entGap_upper` (which carries the exact series
coefficients `u²/2 + u⁴/12 + tail`); the only estimate is the geometric
tail `64x⁶/(30(1-4x²)) ≤ (128/45)x⁶ ≤ (16/5)x⁶`. -/
theorem binEntropy_defect_upper_sharp {x : ℝ} (hx : |x| ≤ 1 / 4) :
    1 - binaryEntropy (1 / 2 - x) ≤
      (2 * x ^ 2 + 4 / 3 * x ^ 4 + 16 / 5 * x ^ 6) / Real.log 2 := by
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
  rw [hgap, div_le_div_iff_of_pos_right hlog]
  have hub := entGap_upper habs
  have hden : (3 : ℝ) / 4 ≤ 1 - (2 * x) ^ 2 := by nlinarith [hx2]
  have htail : (2 * x) ^ 6 / (30 * (1 - (2 * x) ^ 2)) ≤ 16 / 5 * x ^ 6 := by
    have hpos : (0 : ℝ) < 30 * (1 - (2 * x) ^ 2) := by nlinarith [hden]
    rw [div_le_iff₀ hpos]
    have hx6 : (0 : ℝ) ≤ x ^ 6 := by positivity
    nlinarith [hx6, hden]
  have e1 : (2 * x) ^ 2 / 2 = 2 * x ^ 2 := by ring
  have e2 : (2 * x) ^ 4 / 12 = 4 / 3 * x ^ 4 := by ring
  rw [e1, e2] at hub
  linarith [hub, htail]

/-! ## §2 The r-aware entropy-defect side of (W3) -/

/-- `r (1 - C_r) ≤ λ²ln2/8 + λ⁴ln³2/(192 r²) + λ⁶ln⁵2/(1280 r⁴)`.
Sharp counterpart of `DegeneracyLedger.r_mul_one_sub_Cside_le`
(whose quartic coefficient is `3/256` instead of `1/192·(with x⁶ split)`;
at `r = 2` this bound is tight to `2·10⁻⁵`). -/
theorem r_one_sub_Cside_sharp (r : ℕ) (lam : ℝ) (hr : 2 ≤ r)
    (hlam0 : 0 ≤ lam) (hlam : lam * Real.log 2 ≤ 1) :
    (r : ℝ) * (1 - Cside r (tauOf r lam))
      ≤ lam ^ 2 * Real.log 2 / 8 + lam ^ 4 * Real.log 2 ^ 3 / (192 * (r : ℝ) ^ 2)
          + lam ^ 6 * Real.log 2 ^ 5 / (1280 * (r : ℝ) ^ 4) := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  set x : ℝ := lam * Real.log 2 / (4 * (r : ℝ)) with hxdef
  have hx0 : 0 ≤ x := by
    have : 0 ≤ lam * Real.log 2 := mul_nonneg hlam0 hlog.le
    positivity
  have hxle : x ≤ 1 / 8 := by
    rw [hxdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hlam, hr0]
  have hxabs : |x| ≤ 1 / 4 := by
    rw [abs_of_nonneg hx0]; linarith
  have htau : tauOf r lam = 1 / 2 - x := by
    simp only [tauOf, hxdef]; try ring
  have hb := binEntropy_defect_upper_sharp hxabs
  have hmul : (r : ℝ) * ((r : ℝ) * (1 - binaryEntropy (1 / 2 - x)))
      ≤ (r : ℝ) ^ 2 * ((2 * x ^ 2 + 4 / 3 * x ^ 4 + 16 / 5 * x ^ 6) / Real.log 2) := by
    have := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ (r:ℝ) ^ 2)
    nlinarith [this]
  have hxsq : x ^ 2 = lam ^ 2 * Real.log 2 ^ 2 / (16 * (r : ℝ) ^ 2) := by
    rw [hxdef]; field_simp; ring
  have hx4 : x ^ 4 = lam ^ 4 * Real.log 2 ^ 4 / (256 * (r : ℝ) ^ 4) := by
    rw [hxdef]; field_simp; ring
  have hx6 : x ^ 6 = lam ^ 6 * Real.log 2 ^ 6 / (4096 * (r : ℝ) ^ 6) := by
    rw [hxdef]; field_simp; ring
  have hrhs : (r : ℝ) ^ 2 * ((2 * x ^ 2 + 4 / 3 * x ^ 4 + 16 / 5 * x ^ 6) / Real.log 2)
      = lam ^ 2 * Real.log 2 / 8 + lam ^ 4 * Real.log 2 ^ 3 / (192 * (r : ℝ) ^ 2)
          + lam ^ 6 * Real.log 2 ^ 5 / (1280 * (r : ℝ) ^ 4) := by
    rw [hxsq, hx4, hx6]; field_simp; try ring
  calc (r : ℝ) * (1 - Cside r (tauOf r lam))
      = (r : ℝ) * ((r : ℝ) * (1 - binaryEntropy (1 / 2 - x))) := by
        rw [one_sub_Cside, htau]
    _ ≤ (r : ℝ) ^ 2 * ((2 * x ^ 2 + 4 / 3 * x ^ 4 + 16 / 5 * x ^ 6) / Real.log 2) := hmul
    _ = _ := hrhs

/-! ## §3 The window side of (W3) -/

/-- `r · width_r ≤ W(λ)·(1/r - 1/r²)`, from `width_le_mul`. -/
theorem r_width_term_le (r : ℕ) (lam : ℝ) (hr : 2 ≤ r) (hlam : 0 < lam)
    (hra : lam * Real.log 2 < 2 * (r : ℝ)) :
    (r : ℝ) * width r lam ≤ Wconst lam * (1 / (r : ℝ) - 1 / (r : ℝ) ^ 2) := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have h := width_le_mul r lam hr hlam hra
  have := mul_le_mul_of_nonneg_left h hrpos.le
  refine this.trans (le_of_eq ?_)
  field_simp
  try ring

/-- `1/r - 1/r² ≤ 1/4` for `r ≥ 2` — i.e. `(r - 2)² ≥ 0`. -/
theorem inv_sub_inv_sq_le_quarter {r : ℕ} (hr : 2 ≤ r) :
    1 / (r : ℝ) - 1 / (r : ℝ) ^ 2 ≤ 1 / 4 := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  rw [div_sub_div _ _ (ne_of_gt hrpos) (by positivity), div_le_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [sq_nonneg ((r : ℝ) - 2)]

/-! ## §4 `K₁` for the whole in-window family -/

/-- The decomposition `1 - β_θ = (1 - C_r) + (1 - θ)·width_r`. -/
theorem one_sub_betaTheta (r : ℕ) (lam theta : ℝ) :
    1 - betaTheta r lam theta =
      (1 - Cside r (tauOf r lam)) + (1 - theta) * width r lam := by
  simp only [betaTheta, Aside, width]
  ring

/-- **(W3) for the family**: an r-aware `K₁(θ)`.  For `r ≥ 2`, `0 ≤ θ ≤ 1`,
`0 < λ` with `λ ln 2 ≤ 1`,
`r(1-β_θ) ≤ λ²ln2/8 + λ⁴ln³2/(192r²) + λ⁶ln⁵2/(1280r⁴) + (1-θ)W(λ)(1/r - 1/r²)`. -/
theorem K1_theta_bound (r : ℕ) (lam theta : ℝ) (hr : 2 ≤ r)
    (hlam : 0 < lam) (hlamL : lam * Real.log 2 ≤ 1)
    (htheta1 : theta ≤ 1) :
    (r : ℝ) * (1 - betaTheta r lam theta)
      ≤ lam ^ 2 * Real.log 2 / 8 + lam ^ 4 * Real.log 2 ^ 3 / (192 * (r : ℝ) ^ 2)
          + lam ^ 6 * Real.log 2 ^ 5 / (1280 * (r : ℝ) ^ 4)
          + (1 - theta) * (Wconst lam * (1 / (r : ℝ) - 1 / (r : ℝ) ^ 2)) := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hra : lam * Real.log 2 < 2 * (r : ℝ) := by linarith
  have hC := r_one_sub_Cside_sharp r lam hr hlam.le hlamL
  have hW := r_width_term_le r lam hr hlam hra
  have hθ : (0 : ℝ) ≤ 1 - theta := by linarith
  have hWθ : (1 - theta) * ((r : ℝ) * width r lam)
      ≤ (1 - theta) * (Wconst lam * (1 / (r : ℝ) - 1 / (r : ℝ) ^ 2)) :=
    mul_le_mul_of_nonneg_left hW hθ
  have hsplit : (r : ℝ) * (1 - betaTheta r lam theta)
      = (r : ℝ) * (1 - Cside r (tauOf r lam)) + (1 - theta) * ((r : ℝ) * width r lam) := by
    rw [one_sub_betaTheta]; ring
  rw [hsplit]
  linarith [hC, hWθ]

/-! ## §5 The `(θ, η)`-parametric Lemma 8.3 -/

/-- `ε_r(β_θ, η) ≥ (1-η)(1-θ)·w/(K₁ r²)`, given the window lower bound
`w/r² ≤ width_r` and the `K₁` bound `r(1-β_θ) ≤ K₁`.  Generalizes
`DegeneracyLedger.epsMax_lower`/`epsR_lower_half` off the midpoint and away
from `η = ½`. -/
theorem epsR_theta_lower (r : ℕ) (lam w K1 theta eta : ℝ) (hr : 2 ≤ r)
    (hw : 0 ≤ w) (hK1 : 0 < K1) (hbpos : betaTheta r lam theta < 1)
    (_htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) (_heta0 : 0 ≤ eta) (heta1 : eta ≤ 1)
    (hwidth : w / (r : ℝ) ^ 2 ≤ width r lam)
    (hK : (r : ℝ) * (1 - betaTheta r lam theta) ≤ K1) :
    (1 - eta) * (1 - theta) * w / (K1 * (r : ℝ) ^ 2)
      ≤ epsR r lam (betaTheta r lam theta) eta := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hden : (0 : ℝ) < (r : ℝ) * (1 - betaTheta r lam theta) := by
    have : (0 : ℝ) < 1 - betaTheta r lam theta := by linarith
    positivity
  -- numerator: `C - β_θ = (1-θ)·width ≥ (1-θ)·w/r²`
  have hnum : (1 - theta) * w / (r : ℝ) ^ 2
      ≤ Cside r (tauOf r lam) - betaTheta r lam theta := by
    rw [Cside_sub_betaTheta]
    have h1 : (1 - theta) * (w / (r : ℝ) ^ 2) ≤ (1 - theta) * width r lam :=
      mul_le_mul_of_nonneg_left hwidth (by linarith)
    calc (1 - theta) * w / (r : ℝ) ^ 2 = (1 - theta) * (w / (r : ℝ) ^ 2) := by ring
      _ ≤ (1 - theta) * width r lam := h1
  -- the `ε^max` bound
  have hmax : (1 - theta) * w / (K1 * (r : ℝ) ^ 2)
      ≤ epsMaxR r lam (betaTheta r lam theta) := by
    rw [epsMaxR, le_div_iff₀ hden]
    have hfac : (0 : ℝ) ≤ (1 - theta) * w / (K1 * (r : ℝ) ^ 2) := by
      have : (0 : ℝ) ≤ 1 - theta := by linarith
      positivity
    calc (1 - theta) * w / (K1 * (r : ℝ) ^ 2) * ((r : ℝ) * (1 - betaTheta r lam theta))
        ≤ (1 - theta) * w / (K1 * (r : ℝ) ^ 2) * K1 := mul_le_mul_of_nonneg_left hK hfac
      _ = (1 - theta) * w / (r : ℝ) ^ 2 := by field_simp
      _ ≤ _ := hnum
  -- apply the `(1-η)` slack once
  simp only [epsR]
  have h1eta : (0 : ℝ) ≤ 1 - eta := by linarith
  calc (1 - eta) * (1 - theta) * w / (K1 * (r : ℝ) ^ 2)
      = (1 - eta) * ((1 - theta) * w / (K1 * (r : ℝ) ^ 2)) := by ring
    _ ≤ (1 - eta) * epsMaxR r lam (betaTheta r lam theta) :=
        mul_le_mul_of_nonneg_left hmax h1eta

/-! ## §6 Numeric instantiations at `λ = 27/20` -/

section Numeric

private theorem log2_pow_bounds :
    Real.log 2 ^ 3 ≤ 0.33302498 ∧ Real.log 2 ^ 5 ≤ 0.1600030 := by
  have hL : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hL0 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hL2 : Real.log 2 ^ 2 ≤ 0.48045302 := by nlinarith
  have hL3 : Real.log 2 ^ 3 ≤ 0.33302498 := by nlinarith [hL2, hL0.le]
  refine ⟨hL3, ?_⟩
  have h5 : Real.log 2 ^ 5 = Real.log 2 ^ 3 * Real.log 2 ^ 2 := by ring
  rw [h5]
  have h3pos : (0 : ℝ) ≤ Real.log 2 ^ 3 := by positivity
  have h2pos : (0 : ℝ) ≤ Real.log 2 ^ 2 := by positivity
  calc Real.log 2 ^ 3 * Real.log 2 ^ 2 ≤ 0.33302498 * 0.48045302 :=
        mul_le_mul hL3 hL2 h2pos (by norm_num)
    _ ≤ 0.1600030 := by norm_num

/-- The generic numeric assembly: at `λ = 27/20`, for `r ≥ 2` and
`0 ≤ θ ≤ 1`, `K₁(θ) ≤ 0.158003 + (1 - θ) · 0.00432085`.
(θ = ¼ gives `≤ 0.16125`... see the two corollaries for the values used.) -/
theorem K1_theta_le (r : ℕ) (theta : ℝ) (hr : 2 ≤ r)
    (htheta0 : 0 ≤ theta) (htheta1 : theta ≤ 1) :
    (r : ℝ) * (1 - betaTheta r (27 / 20) theta)
      ≤ 0.1593953 + (1 - theta) * 0.0043209 := by
  have hL : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hL0 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hlamL : (27 / 20 : ℝ) * Real.log 2 ≤ 1 := by nlinarith
  have h := K1_theta_bound r (27 / 20) theta hr (by norm_num) hlamL htheta1
  obtain ⟨hL3, hL5⟩ := log2_pow_bounds
  have hrsq : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
  have hr4 : (16 : ℝ) ≤ (r : ℝ) ^ 4 := by nlinarith [hrsq]
  -- term 1: `λ² ln2 / 8 ≤ 0.1579076`
  have h1 : (27 / 20 : ℝ) ^ 2 * Real.log 2 / 8 ≤ 0.1579076 := by nlinarith
  -- term 2: `λ⁴ ln³2 / (192 r²) ≤ 0.0014404`
  have h2 : (27 / 20 : ℝ) ^ 4 * Real.log 2 ^ 3 / (192 * (r : ℝ) ^ 2) ≤ 0.0014404 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hL3, hrsq, pow_pos hL0 3]
  -- term 3: `λ⁶ ln⁵2 / (1280 r⁴) ≤ 0.0000473`
  have h3 : (27 / 20 : ℝ) ^ 6 * Real.log 2 ^ 5 / (1280 * (r : ℝ) ^ 4) ≤ 0.0000473 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hL5, hr4, pow_pos hL0 5]
  -- term 4: `(1-θ) · W(λ) · (1/r - 1/r²) ≤ (1-θ) · 0.0043209`
  have hW : Wconst (27 / 20) ≤ 0.0172836 := by
    rw [Wconst, div_le_iff₀ (by norm_num : (0:ℝ) < 64)]
    calc (27 / 20 : ℝ) ^ 4 * Real.log 2 ^ 3
        ≤ (27 / 20 : ℝ) ^ 4 * 0.33302498 :=
          mul_le_mul_of_nonneg_left hL3 (by positivity)
      _ ≤ 0.0172836 * 64 := by norm_num
  have hW0 : (0 : ℝ) ≤ Wconst (27 / 20) := by
    rw [Wconst]; positivity
  have hq := inv_sub_inv_sq_le_quarter hr
  have hq0 : (0 : ℝ) ≤ 1 / (r : ℝ) - 1 / (r : ℝ) ^ 2 := by
    have hle : (r : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have h1 : 1 / (r : ℝ) ^ 2 ≤ 1 / (r : ℝ) := one_div_le_one_div_of_le hrpos hle
    linarith
  have h4 : (1 - theta) * (Wconst (27 / 20) * (1 / (r : ℝ) - 1 / (r : ℝ) ^ 2))
      ≤ (1 - theta) * 0.0043209 := by
    have hinner : Wconst (27 / 20) * (1 / (r : ℝ) - 1 / (r : ℝ) ^ 2) ≤ 0.0043209 := by
      nlinarith [hW, hq, hq0, hW0]
    exact mul_le_mul_of_nonneg_left hinner (by linarith)
  linarith [h, h1, h2, h3, h4]

/-- `K₁(¼) ≤ 0.1627` for every `r ≥ 2` (true max `0.162360` at `r = 2`). -/
theorem K1_quarter_le (r : ℕ) (hr : 2 ≤ r) :
    (r : ℝ) * (1 - betaTheta r (27 / 20) (1 / 4)) ≤ 0.1627 := by
  have h := K1_theta_le r (1 / 4) hr (by norm_num) (by norm_num)
  linarith

/-- `K₁(½) ≤ 0.1616` for every `r ≥ 2` (true max `0.161367` at `r = 2` —
the paper's sharp `K₁ = 0.1614`, up to the `x⁶` tail and the window bound). -/
theorem K1_half_le (r : ℕ) (hr : 2 ≤ r) :
    (r : ℝ) * (1 - betaTheta r (27 / 20) (1 / 2)) ≤ 0.1616 := by
  have h := K1_theta_le r (1 / 2) hr (by norm_num) (by norm_num)
  linarith

/-- **The sharpened explicit constant.**  With the certified window bound
`0.00603/r² ≤ width_r` (Theorem 2's `width_ge`), the `(θ, η) = (¼, ¼)`
ledger certifies `ε ≥ 1/(48 r²)` — beating the paper's midpoint `1/(107 r²)`.
Rational check: `(3/4)² · 0.00603 · 48 = 0.16281 ≥ 0.1627`. -/
theorem eps_quarter_48 (r : ℕ) (hr : 2 ≤ r)
    (hbpos : betaTheta r (27 / 20) (1 / 4) < 1)
    (hwidth : (0.00603 : ℝ) / (r : ℝ) ^ 2 ≤ width r (27 / 20)) :
    1 / (48 * (r : ℝ) ^ 2) ≤ epsR r (27 / 20) (betaTheta r (27 / 20) (1 / 4)) (1 / 4) := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h := epsR_theta_lower r (27 / 20) 0.00603 0.1627 (1 / 4) (1 / 4) hr
    (by norm_num) (by norm_num) hbpos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hwidth (K1_quarter_le r hr)
  refine le_trans ?_ h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ((r : ℝ))]

/-- **The midpoint checkpoint.**  Same machinery at `(θ, η) = (½, ½)`
certifies `ε ≥ 1/(108 r²)` — the paper's `1/107` needs, in addition, the
per-`r` interval value of `width(2)` (Lemma C's uniform `0.00603` is what
limits this to `108`).  Rational check: `(1/4) · 0.00603 · 108 = 0.16281 ≥ 0.1616`. -/
theorem eps_half_108 (r : ℕ) (hr : 2 ≤ r)
    (hbpos : betaTheta r (27 / 20) (1 / 2) < 1)
    (hwidth : (0.00603 : ℝ) / (r : ℝ) ^ 2 ≤ width r (27 / 20)) :
    1 / (108 * (r : ℝ) ^ 2) ≤ epsR r (27 / 20) (betaTheta r (27 / 20) (1 / 2)) (1 / 2) := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h := epsR_theta_lower r (27 / 20) 0.00603 0.1616 (1 / 2) (1 / 2) hr
    (by norm_num) (by norm_num) hbpos (by norm_num) (by norm_num) (by norm_num)
    (by norm_num) hwidth (K1_half_le r hr)
  refine le_trans ?_ h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [sq_nonneg ((r : ℝ))]

end Numeric

end DegeneracyLedgerSharp
