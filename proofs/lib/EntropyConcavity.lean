import LawDefs

/-!
# The one-parent entropy functional `F_a`: log-cosh form and derivatives

Machinery for Lemma 4.1; the lemma itself -- the second-derivative identity and
its quadratic-margin consequence -- is `Lemma41.lean`.

Develops the auxiliary form `Gaux a q = ln 2 · F_a(q) - (ln 2 - a)`, its first
and second derivatives, and the concavity witness `Haux` behind the margin.
-/

namespace DegeneracyLaw

open TwoDegenerateGraphs

noncomputable section

/-! ### An auxiliary log-cosh form of `Ffun` -/

/-- `F_a(q) · ln 2 = Gaux a q + (ln 2 - a)`; the log-cosh normal form of `Ffun`. -/
def Gaux (a q : ℝ) : ℝ := Real.binEntropy q + Real.log (Real.cosh (a * (1 - 2 * q)))

lemma exp_sum_eq_cosh (a q : ℝ) :
    Real.exp (-(2 * a * q)) + Real.exp (-(2 * a * (1 - q)))
      = 2 * Real.exp (-a) * Real.cosh (a * (1 - 2 * q)) := by
  have e1 : Real.exp (a * (1 - 2 * q)) = Real.exp (-(2 * a * q)) * Real.exp a := by
    rw [← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-(a * (1 - 2 * q))) = Real.exp (-(2 * a * (1 - q))) * Real.exp a := by
    rw [← Real.exp_add]; congr 1; ring
  have e3 : Real.exp (-a) * Real.exp a = 1 := by
    rw [← Real.exp_add]; simp
  rw [Real.cosh_eq, e1, e2]
  linear_combination (-(Real.exp (-(2 * a * q)) + Real.exp (-(2 * a * (1 - q))))) * e3

lemma Ffun_eq_Gaux (a q : ℝ) :
    Ffun a q = (Gaux a q + (Real.log 2 - a)) / Real.log 2 := by
  have hcosh : (0 : ℝ) < Real.cosh (a * (1 - 2 * q)) := Real.cosh_pos _
  have hE : Real.exp (-(2 * a * q)) + Real.exp (-(2 * a * (1 - q)))
      = 2 * Real.exp (-a) * Real.cosh (a * (1 - 2 * q)) := exp_sum_eq_cosh a q
  have hlog : Real.log (Real.exp (-(2 * a * q)) + Real.exp (-(2 * a * (1 - q))))
      = Real.log 2 - a + Real.log (Real.cosh (a * (1 - 2 * q))) := by
    rw [hE, Real.log_mul (by positivity) (ne_of_gt hcosh),
      Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
    ring
  unfold Ffun binaryEntropy logTwo Gaux
  rw [hlog]
  ring

/-! ### Symmetry -/

lemma Gaux_symm (a q : ℝ) : Gaux a (1 - q) = Gaux a q := by
  unfold Gaux
  rw [Real.binEntropy_one_sub]
  congr 2
  rw [show a * (1 - 2 * (1 - q)) = -(a * (1 - 2 * q)) by ring, Real.cosh_neg]

/-! ### Derivatives -/

/-- Rewrite the derivative value of a `HasDerivAt` statement. -/
lemma HDA_congr {f : ℝ → ℝ} {c d x : ℝ} (h : HasDerivAt f c x) (hcd : c = d) :
    HasDerivAt f d x := hcd ▸ h

/-- Inner affine map `x ↦ a(1 - 2x)`. -/
lemma hasDerivAt_inner (a q : ℝ) :
    HasDerivAt (fun x : ℝ => a * (1 - 2 * x)) (a * (-2)) q := by
  have h1 : HasDerivAt (fun x : ℝ => 1 - 2 * x) (-2 : ℝ) q := by
    simpa using ((hasDerivAt_id q).const_mul (2 : ℝ)).const_sub 1
  exact h1.const_mul a

/-- Derivative of `x ↦ log cosh (a(1-2x))`. -/
lemma hasDerivAt_logCosh (a q : ℝ) :
    HasDerivAt (fun x : ℝ => Real.log (Real.cosh (a * (1 - 2 * x))))
      (-(2 * a) * Real.tanh (a * (1 - 2 * q))) q := by
  have hu := hasDerivAt_inner a q
  have hc : HasDerivAt (fun x : ℝ => Real.cosh (a * (1 - 2 * x)))
      (Real.sinh (a * (1 - 2 * q)) * (a * (-2))) q :=
    (Real.hasDerivAt_cosh _).comp q hu
  have hcpos : (0 : ℝ) < Real.cosh (a * (1 - 2 * q)) := Real.cosh_pos _
  refine HDA_congr (hc.log (ne_of_gt hcpos)) ?_
  rw [Real.tanh_eq_sinh_div_cosh]
  ring

/-- Derivative of `x ↦ sinh(a(1-2x)) / cosh(a(1-2x))`, i.e. of `tanh(a(1-2x))`. -/
lemma hasDerivAt_tanhComp (a q : ℝ) :
    HasDerivAt (fun x : ℝ => Real.tanh (a * (1 - 2 * x)))
      (-(2 * a) / Real.cosh (a * (1 - 2 * q)) ^ 2) q := by
  have hu := hasDerivAt_inner a q
  have hc : HasDerivAt (fun x : ℝ => Real.cosh (a * (1 - 2 * x)))
      (Real.sinh (a * (1 - 2 * q)) * (a * (-2))) q :=
    (Real.hasDerivAt_cosh _).comp q hu
  have hs : HasDerivAt (fun x : ℝ => Real.sinh (a * (1 - 2 * x)))
      (Real.cosh (a * (1 - 2 * q)) * (a * (-2))) q :=
    (Real.hasDerivAt_sinh _).comp q hu
  have hcpos : (0 : ℝ) < Real.cosh (a * (1 - 2 * q)) := Real.cosh_pos _
  have hdiv := hs.div hc (ne_of_gt hcpos)
  have hfun : (fun x : ℝ => Real.tanh (a * (1 - 2 * x)))
      = fun x : ℝ => Real.sinh (a * (1 - 2 * x)) / Real.cosh (a * (1 - 2 * x)) := by
    funext x; exact Real.tanh_eq_sinh_div_cosh _
  rw [hfun]
  refine HDA_congr hdiv ?_
  have hpyth : Real.cosh (a * (1 - 2 * q)) ^ 2 - Real.sinh (a * (1 - 2 * q)) ^ 2 = 1 :=
    Real.cosh_sq_sub_sinh_sq _
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination (-(2 * a) * Real.cosh (a * (1 - 2 * q)) ^ 2) * hpyth

/-- First derivative of `Gaux a`. -/
lemma hasDerivAt_Gaux (a : ℝ) {q : ℝ} (hq0 : q ≠ 0) (hq1 : q ≠ 1) :
    HasDerivAt (Gaux a)
      (Real.log (1 - q) - Real.log q - 2 * a * Real.tanh (a * (1 - 2 * q))) q := by
  have hb := Real.hasDerivAt_binEntropy hq0 hq1
  have hl := hasDerivAt_logCosh a q
  unfold Gaux
  refine HDA_congr (hb.add hl) ?_
  ring

/-- Second derivative of `Gaux a`, i.e. the derivative of its first derivative. -/
lemma hasDerivAt_Gaux' (a : ℝ) {q : ℝ} (hq0 : 0 < q) (hq1 : q < 1) :
    HasDerivAt (fun x : ℝ => Real.log (1 - x) - Real.log x - 2 * a * Real.tanh (a * (1 - 2 * x)))
      (-(1 / (q * (1 - q))) + 4 * a ^ 2 / Real.cosh (a * (1 - 2 * q)) ^ 2) q := by
  have h1 : HasDerivAt (fun x : ℝ => Real.log (1 - x)) (-(1 - q)⁻¹) q := by
    have hs : HasDerivAt (fun x : ℝ => 1 - x) (-1 : ℝ) q := by
      simpa using (hasDerivAt_id q).const_sub 1
    exact HDA_congr (hs.log (by linarith)) (by ring)
  have h2 : HasDerivAt Real.log q⁻¹ q := Real.hasDerivAt_log (ne_of_gt hq0)
  have h3 := (hasDerivAt_tanhComp a q).const_mul (2 * a)
  refine HDA_congr ((h1.sub h2).sub h3) ?_
  have hcpos : (0 : ℝ) < Real.cosh (a * (1 - 2 * q)) := Real.cosh_pos _
  have hc2 : (0 : ℝ) < Real.cosh (a * (1 - 2 * q)) ^ 2 := by positivity
  have hne0 : q ≠ 0 := ne_of_gt hq0
  have hne1 : (1 : ℝ) - q ≠ 0 := sub_ne_zero_of_ne (ne_of_gt hq1)
  field_simp
  ring

/-! ### The second-derivative identity and bound (Lemma 4.1) -/

/-- The concavity witness `H(q) = Gaux a q + 2(1-a²)(q - 1/2)²`. -/
private def Haux (a q : ℝ) : ℝ := Gaux a q + 2 * (1 - a ^ 2) * (q - 1 / 2) ^ 2

private lemma Haux_symm (a q : ℝ) : Haux a (1 - q) = Haux a q := by
  unfold Haux
  rw [Gaux_symm]
  congr 2
  ring

private lemma continuous_Gaux (a : ℝ) : Continuous (Gaux a) := by
  unfold Gaux
  have : Continuous fun x : ℝ => Real.log (Real.cosh (a * (1 - 2 * x))) := by
    apply Real.continuousOn_log.comp_continuous (by fun_prop)
    intro x
    exact ne_of_gt (Real.cosh_pos _)
  exact Real.binEntropy_continuous.add this

private lemma concaveOn_Haux (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) :
    ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) (Haux a) := by
  set f' : ℝ → ℝ := fun x =>
    Real.log (1 - x) - Real.log x - 2 * a * Real.tanh (a * (1 - 2 * x))
      + 4 * (1 - a ^ 2) * (x - 1 / 2) with hf'def
  set f'' : ℝ → ℝ := fun x =>
    (-(1 / (x * (1 - x))) + 4 * a ^ 2 / Real.cosh (a * (1 - 2 * x)) ^ 2) + 4 * (1 - a ^ 2)
    with hf''def
  have hint : interior (Set.Icc (0 : ℝ) 1) = Set.Ioo (0 : ℝ) 1 := interior_Icc
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc 0 1)
    (f' := f') (f'' := f'') ?_ ?_ ?_ ?_
  · exact ((continuous_Gaux a).add (by fun_prop)).continuousOn
  · intro x hx
    rw [hint] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have hG := hasDerivAt_Gaux a (ne_of_gt hx0) (ne_of_lt hx1)
    have hq : HasDerivAt (fun y : ℝ => 2 * (1 - a ^ 2) * (y - 1 / 2) ^ 2)
        (4 * (1 - a ^ 2) * (x - 1 / 2)) x := by
      have hs : HasDerivAt (fun y : ℝ => y - (1 : ℝ) / 2) 1 x :=
        (hasDerivAt_id x).sub_const _
      have h1 : HasDerivAt (fun y : ℝ => (y - 1 / 2) ^ 2) (2 * (x - 1 / 2)) x := by
        simp only [pow_two]
        exact HDA_congr (hs.mul hs) (by ring)
      exact HDA_congr (h1.const_mul (2 * (1 - a ^ 2))) (by ring)
    have := (hG.add hq).hasDerivWithinAt (s := interior (Set.Icc (0 : ℝ) 1))
    exact this
  · intro x hx
    rw [hint] at hx
    obtain ⟨hx0, hx1⟩ := hx
    have h1 := hasDerivAt_Gaux' a hx0 hx1
    have h2 : HasDerivAt (fun y : ℝ => 4 * (1 - a ^ 2) * (y - 1 / 2)) (4 * (1 - a ^ 2)) x := by
      exact HDA_congr (((hasDerivAt_id x).sub_const (1 / 2 : ℝ)).const_mul (4 * (1 - a ^ 2)))
        (by ring)
    exact (h1.add h2).hasDerivWithinAt
  · intro x hx
    rw [hint] at hx
    obtain ⟨hx0, hx1⟩ := hx
    simp only [hf''def]
    have hcosh : (1 : ℝ) ≤ Real.cosh (a * (1 - 2 * x)) := Real.one_le_cosh _
    have hc2 : (1 : ℝ) ≤ Real.cosh (a * (1 - 2 * x)) ^ 2 := by nlinarith
    have hprod : 4 * a ^ 2 / Real.cosh (a * (1 - 2 * x)) ^ 2 ≤ 4 * a ^ 2 := by
      rw [div_le_iff₀ (by linarith)]
      nlinarith [sq_nonneg a]
    have hqq : (0 : ℝ) < x * (1 - x) := by nlinarith
    have hqq4 : x * (1 - x) ≤ 1 / 4 := by nlinarith [sq_nonneg (x - 1 / 2)]
    have hinv : (4 : ℝ) ≤ 1 / (x * (1 - x)) := by
      rw [le_div_iff₀ hqq]; linarith
    linarith

lemma Gaux_le_center (a : ℝ) (ha0 : 0 < a) (ha1 : a < 1) {q : ℝ}
    (hq : q ∈ Set.Icc (0 : ℝ) 1) :
    Gaux a q + 2 * (1 - a ^ 2) * (q - 1 / 2) ^ 2 ≤ Gaux a (1 / 2) := by
  obtain ⟨hq0, hq1⟩ := hq
  have hc := concaveOn_Haux a ha0 ha1
  have hmem : q ∈ Set.Icc (0 : ℝ) 1 := ⟨hq0, hq1⟩
  have hmem' : (1 - q) ∈ Set.Icc (0 : ℝ) 1 := ⟨by linarith, by linarith⟩
  have h := hc.2 hmem hmem' (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2)
    (by norm_num)
  simp only [smul_eq_mul, Haux_symm] at h
  have hpt : (1 : ℝ) / 2 * q + 1 / 2 * (1 - q) = 1 / 2 := by ring
  rw [hpt] at h
  have hle : Haux a q ≤ Haux a (1 / 2) := by linarith
  have e : Haux a (1 / 2) = Gaux a (1 / 2) := by unfold Haux; norm_num
  rw [e] at hle
  unfold Haux at hle
  linarith


end

end DegeneracyLaw
