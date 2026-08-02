import EntropyConcavity

/-!
# Lemma A: far field / concavity of `F_a`

Design-notes reference (notes not shipped in this repository): §4.1.

Main results:
* `Ffun_symm` : `F_a(q) = F_a(1-q)`.
* `Ffun_second_deriv` : the exact second-derivative identity
  `F_a''(q) ln 2 = -1/(q(1-q)) + 4a² sech²(a(1-2q)) ≤ 4(a²-1)`,
  stated as a pair of `HasDerivAt` facts for `ln 2 · F_a` plus the bound.
  The margin vanishes exactly at `a = 1`, i.e. at Gibbs weight `2^λ = e`,
  which is the source of the phase transition in Theorem 3(a).
* `Ffun_le_center` : the downstream consequence, strict concavity with an
  explicit quadratic margin,
  `F_a(q) ≤ F_a(1/2) - (2(1-a²)/ln 2)(q - 1/2)²` for `q ∈ [0,1]`, `0 < a < 1`.

The derivative computations behind these are `lib/EntropyConcavity.lean`.
-/

namespace DegeneracyLaw

open TwoDegenerateGraphs

noncomputable section

/-- `F_a` is symmetric about `q = 1/2`. -/
theorem Ffun_symm (a q : ℝ) : Ffun a q = Ffun a (1 - q) := by
  unfold Ffun binaryEntropy
  rw [Real.binEntropy_one_sub]
  congr 2
  rw [show (1 : ℝ) - (1 - q) = q by ring]
  ring_nf

/-- **Lemma A (derivative identity).** For `q ∈ (0,1)`, the function `ln 2 · F_a` has first
derivative `log(1-q) - log q - 2a tanh(a(1-2q))` at `q`, that first derivative in turn has
derivative `-1/(q(1-q)) + 4a² sech²(a(1-2q))` at `q`, and this value is `≤ 4(a² - 1)`. -/
theorem Ffun_second_deriv (a q : ℝ) (hq : q ∈ Set.Ioo (0 : ℝ) 1) :
    HasDerivAt (fun x : ℝ => Real.log 2 * Ffun a x)
        (Real.log (1 - q) - Real.log q - 2 * a * Real.tanh (a * (1 - 2 * q))) q ∧
      HasDerivAt
        (fun x : ℝ =>
          Real.log (1 - x) - Real.log x - 2 * a * Real.tanh (a * (1 - 2 * x)))
        (-(1 / (q * (1 - q))) + 4 * a ^ 2 * (1 / Real.cosh (a * (1 - 2 * q)) ^ 2)) q ∧
      -(1 / (q * (1 - q))) + 4 * a ^ 2 * (1 / Real.cosh (a * (1 - 2 * q)) ^ 2)
        ≤ 4 * (a ^ 2 - 1) := by
  obtain ⟨hq0, hq1⟩ := hq
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨?_, ?_, ?_⟩
  · -- `ln 2 · F_a x = Gaux a x + (ln 2 - a)`
    have hfun : (fun x : ℝ => Real.log 2 * Ffun a x)
        = fun x : ℝ => Gaux a x + (Real.log 2 - a) := by
      funext x
      rw [Ffun_eq_Gaux]
      field_simp
    rw [hfun]
    exact (hasDerivAt_Gaux a (ne_of_gt hq0) (ne_of_lt hq1)).add_const _
  · exact HDA_congr (hasDerivAt_Gaux' a hq0 hq1) (by ring)
  · have hcosh : (1 : ℝ) ≤ Real.cosh (a * (1 - 2 * q)) := Real.one_le_cosh _
    have hc2 : (1 : ℝ) ≤ Real.cosh (a * (1 - 2 * q)) ^ 2 := by nlinarith
    have hsech : 1 / Real.cosh (a * (1 - 2 * q)) ^ 2 ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    have hsech0 : (0 : ℝ) < 1 / Real.cosh (a * (1 - 2 * q)) ^ 2 := by positivity
    have hprod : 4 * a ^ 2 * (1 / Real.cosh (a * (1 - 2 * q)) ^ 2) ≤ 4 * a ^ 2 := by
      nlinarith [sq_nonneg a]
    have hqq : (0 : ℝ) < q * (1 - q) := by nlinarith
    have hqq4 : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
    have hinv : (4 : ℝ) ≤ 1 / (q * (1 - q)) := by
      rw [le_div_iff₀ hqq]; linarith
    linarith

/-! ### The quadratic-margin consequence -/

/-- **Lemma A (downstream form).** For `0 < a < 1` and `q ∈ [0,1]`,
`F_a(q) ≤ F_a(1/2) - (2(1-a²)/ln 2)(q - 1/2)²`. -/
theorem Ffun_le_center (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) (q : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    Ffun a q ≤ Ffun a (1 / 2) - (2 * (1 - a ^ 2) / Real.log 2) * (q - 1 / 2) ^ 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have h := Gaux_le_center a ha0 ha1 hq
  have hnum : 0 ≤ Gaux a (1 / 2) - (Gaux a q + 2 * (1 - a ^ 2) * (q - 1 / 2) ^ 2) := by linarith
  rw [Ffun_eq_Gaux, Ffun_eq_Gaux, ← sub_nonneg]
  have hEq : (Gaux a (1 / 2) + (Real.log 2 - a)) / Real.log 2
        - 2 * (1 - a ^ 2) / Real.log 2 * (q - 1 / 2) ^ 2
        - (Gaux a q + (Real.log 2 - a)) / Real.log 2
      = (Gaux a (1 / 2) - (Gaux a q + 2 * (1 - a ^ 2) * (q - 1 / 2) ^ 2)) / Real.log 2 := by
    field_simp
    ring
  rw [hEq]
  exact div_nonneg hnum hlog2.le

end

end DegeneracyLaw
