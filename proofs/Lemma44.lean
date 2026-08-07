import WindowLowerBound

/-!
# Lemma 4.4: the window lower bound (paper §4)

The center value `G_r(1/2,1/2)` is a binomially weighted `log cosh` sum, and
the elementary sandwich `t²/2 - t⁴/12 ≤ log cosh t ≤ t²/2 - t⁴/12 + t⁶/45`,
combined with the exact moments of `2 Bin(r,1/2) - r`, yields

  `C_r - A_r = (λ⁴ ln³2 / 64 r²)(1 + O(1/r))`.

The surviving `1/r²` term is positive for exactly one reason: `log cosh t` lies
below its parabola `t²/2`. That discrepancy is the entire source of the
counterexample.

The bounds and moments this rests on are `proofs/lib/WindowLowerBound.lean`.
-/

namespace DegeneracyLaw
namespace LemmaC

open Real Finset

noncomputable section

open TwoDegenerateGraphs

/-- **Lemma 4.4**: the window lower bound. -/
theorem width_ge (r : ℕ) (lam : ℝ) (hr : 2 ≤ r) (hlam : 0 < lam)
    (hlam' : lam * Real.log 2 < 1)
    (hB : supG r lam = Gfun r lam (1 / 2) (1 / 2)) :
    Wconst lam / (r : ℝ) ^ 2 * (1 - (1 + (lam * Real.log 2) ^ 2 / 3) / r)
        - (lam * Real.log 2) ^ 6 /
            (1920 * Real.log 2 * (r : ℝ) ^ 5 * (1 - (lam * Real.log 2) ^ 2 / 4))
      ≤ width r lam := by
  have hr1 : 1 ≤ r := le_trans (by norm_num) hr
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr1
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set A : ℝ := lam * Real.log 2 with hA
  have hApos : 0 < A := by positivity
  have hE := centerSum_le r hr1 lam
  have hC := Cside_gap_le r hr1 lam hlam hlam'
  have hAs := Aside_eq r hr1 lam hB
  -- the sixth moment is at most `15 r³`
  have hmom : (lam * Real.log 2) ^ 6 * (15 * (r : ℝ) ^ 3 - 30 * (r : ℝ) ^ 2 + 16 * r) /
      (2880 * (r : ℝ) ^ 6) ≤ A ^ 6 / (192 * (r : ℝ) ^ 3) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    have h6 : (0 : ℝ) ≤ A ^ 6 := by positivity
    have hq : (0 : ℝ) ≤ A ^ 6 * ((r : ℝ) ^ 3 * (30 * (r : ℝ) ^ 2 - 16 * r)) :=
      mul_nonneg h6 (mul_nonneg (by positivity) (by nlinarith [hr2, hr0.le]))
    nlinarith [hq]
  have hE' : ∑ j ∈ range (r + 1), (r.choose j : ℝ) * (2⁻¹ : ℝ) ^ r *
      logTwo (Real.cosh (lam * Real.log 2 * (2 * j - r : ℝ) / (2 * r)))
      ≤ (1 / Real.log 2) * (A ^ 2 / (8 * r)
          - A ^ 4 * (3 * (r : ℝ) ^ 2 - 2 * r) / (192 * (r : ℝ) ^ 4) + A ^ 6 / (192 * (r : ℝ) ^ 3))
        := by
    refine hE.trans ?_
    have : (0 : ℝ) < 1 / Real.log 2 := by positivity
    apply mul_le_mul_of_nonneg_left _ this.le
    linarith [hmom]
  -- assemble
  have hCside : Cside r (tauOf r lam) = 1 - (r : ℝ) * (1 - binaryEntropy (tauOf r lam)) := by
    rw [Cside]; ring
  rw [width, hCside, hAs]
  have hW : Wconst lam = A ^ 4 / (64 * Real.log 2) := by
    rw [Wconst, hA]; field_simp; try ring
  rw [hW]
  have hid : A ^ 4 / (64 * Real.log 2) / (r : ℝ) ^ 2 * (1 - (1 + A ^ 2 / 3) / r)
      = A ^ 2 / (4 * r * Real.log 2)
        - (1 / Real.log 2) * (A ^ 2 / (8 * r) + A ^ 4 / (192 * (r : ℝ) ^ 3))
        - (1 / Real.log 2) * (A ^ 2 / (8 * r)
            - A ^ 4 * (3 * (r : ℝ) ^ 2 - 2 * r) / (192 * (r : ℝ) ^ 4) + A ^ 6 / (192 * (r : ℝ) ^ 3))
      := by
    field_simp
    ring
  rw [hid]
  linarith [hC, hE']

set_option maxHeartbeats 1000000 in
/-- **Corollary**: the window is positive at `λ = 27/20 = 1.35`, for every `r ≥ 2`. -/
theorem width_pos_at_135 (r : ℕ) (hr : 2 ≤ r)
    (hB : supG r (27 / 20) = Gfun r (27 / 20) (1 / 2) (1 / 2)) :
    0 < width r (27 / 20) := by
  have hr2 : (2 : ℝ) ≤ r := by exact_mod_cast hr
  have hr0 : (0 : ℝ) < r := by linarith
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hlog_lt : Real.log 2 < 0.6932 := by
    have := Real.log_two_lt_d9
    linarith
  have hlog_gt : (0.6931 : ℝ) < Real.log 2 := by
    have := Real.log_two_gt_d9
    linarith
  set A : ℝ := (27 / 20 : ℝ) * Real.log 2 with hA
  have hApos : 0 < A := by positivity
  have hA1 : A < 1 := by rw [hA]; nlinarith [hlog_lt]
  have hAgt : (0.93 : ℝ) < A := by rw [hA]; nlinarith [hlog_gt]
  have hmain := width_ge r (27 / 20) hr (by norm_num) hA1 hB
  refine lt_of_lt_of_le ?_ hmain
  have hW : Wconst (27 / 20 : ℝ) = A ^ 4 / (64 * Real.log 2) := by
    rw [Wconst, hA]; field_simp; try ring
  rw [hW, sub_pos]
  have hden : (0 : ℝ) < 1 - A ^ 2 / 4 := by nlinarith [hA1, hApos]
  have hA2 : A ^ 2 < 1 := by nlinarith [hA1, hApos]
  have hbr : (1 : ℝ) / 3 ≤ 1 - (1 + A ^ 2 / 3) / r := by
    have h1 : (1 + A ^ 2 / 3) / (r : ℝ) ≤ (4 / 3) / 2 := by
      rw [div_le_div_iff₀ hr0 (by norm_num)]
      nlinarith [hA2, hr2]
    linarith
  have hpos : (0 : ℝ) < A ^ 4 / (64 * Real.log 2) / (r : ℝ) ^ 2 := by positivity
  have hM : A ^ 4 / (64 * Real.log 2) / (r : ℝ) ^ 2 * (1 / 3)
      ≤ A ^ 4 / (64 * Real.log 2) / (r : ℝ) ^ 2 * (1 - (1 + A ^ 2 / 3) / r) :=
    mul_le_mul_of_nonneg_left hbr hpos.le
  have e : A ^ 4 / (64 * Real.log 2) / (r : ℝ) ^ 2 * (1 / 3)
      = A ^ 4 / (192 * Real.log 2 * (r : ℝ) ^ 2) := by field_simp; try ring
  have hTlt : A ^ 6 / (1920 * Real.log 2 * (r : ℝ) ^ 5 * (1 - A ^ 2 / 4))
      < A ^ 4 / (192 * Real.log 2 * (r : ℝ) ^ 2) := by
    rw [div_lt_div_iff₀ (by positivity) (by positivity)]
    have hA4 : (0 : ℝ) < A ^ 4 := by positivity
    have hr2sq : (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 5 :=
      pow_le_pow_right₀ (by linarith) (by norm_num)
    have hx1 : A ^ 2 * (r : ℝ) ^ 2 ≤ (r : ℝ) ^ 5 := by
      nlinarith [hA2.le, hr2sq, pow_pos hr0 2, sq_nonneg A]
    have hP : (0 : ℝ) < A ^ 4 * (192 * Real.log 2) := by positivity
    have hd1 : A ^ 6 * (192 * Real.log 2 * (r : ℝ) ^ 2)
        ≤ A ^ 4 * (192 * Real.log 2 * (r : ℝ) ^ 5) := by
      nlinarith [mul_le_mul_of_nonneg_left hx1 hP.le]
    have h34 : (3 : ℝ) / 4 < 1 - A ^ 2 / 4 := by nlinarith [hA2]
    have hQ : (0 : ℝ) < A ^ 4 * (Real.log 2 * (r : ℝ) ^ 5) := by positivity
    have hd2 : A ^ 4 * (192 * Real.log 2 * (r : ℝ) ^ 5)
        < A ^ 4 * (1920 * Real.log 2 * (r : ℝ) ^ 5 * (1 - A ^ 2 / 4)) := by
      nlinarith [mul_lt_mul_of_pos_left h34 hQ]
    linarith [hd1, hd2]
  rw [e] at hM
  linarith [hM, hTlt]

end

end LemmaC
end DegeneracyLaw
