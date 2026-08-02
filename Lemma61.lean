import WindowUpperBound

/-!
# Lemma 6.1: the window upper bound `width_r ≤ W(λ)/r² (1 - 1/r)`

The unconditional half of the Theorem 3(a) sandwich: no choice of parameters
makes the feasibility window wider than `W(λ)/r²` to leading order.

Its ingredients -- the global `log cosh` lower bound, the binomial moments and
the entropy-series bound -- are `lib/WindowUpperBound.lean`.
-/

namespace DegeneracyLaw

open TwoDegenerateGraphs Finset

noncomputable section

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
