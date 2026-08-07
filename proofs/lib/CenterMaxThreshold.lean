import LawDefs
import Lemma41
import Lemma42

/-!
# Lemma 4.2, quantified (paper Remark 4.3): the explicit threshold `R(a)`

Design-notes reference (notes not shipped in this repository): §4.4–4.7 and §10.1–10.3.

This file formalises the *quantitative* half of Lemma 4.2 — the closed-form
threshold `R(a)` of Cor. 10.2 that makes Prop. 10.3 (and hence Theorem 1.3(b))
possible.  The qualitative Lemma 4.2 lives in `Lemma42.lean`, which is now `sorry`-free; this
file imports it and *instantiates* its machinery with the `a`-dependent strip
half-width `ρ(a)` in place of the fixed-`λ ≤ 27/20` constants.  Small helpers
are still duplicated into the `DegeneracyLawQuant` namespace so the file reads
standalone; the bridge lemmas of §4' are all `rfl`.

**This file is `sorry`-free.**

## The DAG

1. **Definitions** (§10.1): `uOf`, `rhoCrit`, `rho = 0.99 ρ_crit`, the deficit
   integrand `deficit a d`, the Lemma-10.1 lower bound `DeltaLB a`, the real
   threshold `Rreal a` and the `ℕ`-valued `R_of lam = max 2 ⌈Rreal (λ ln 2)⌉₊`.
   *Sorry-free.*
2. **Lemma 10.1** — `DeltaLB_le_deficit` : `Δ_min(a) ≥ u ρ² / (ln2 (a²+2u))`,
   via
   * `log_cos_le_neg_sq_half` : `log (cos x) ≤ -x²/2` on `[0, π/2)`
     (equivalently `cos x ≤ e^{-x²/2}`), proved by the derivative ladder
     `d/dx (-log cos x - x²/2) = tan x - x ≥ 0`; and
   * `quad_min_key` : the exact quadratic-minimization identity
     `(2u d² + (ρ-ad)²)(a²+2u) - 2uρ² = ((a²+2u)d - aρ)²`.
   *Sorry-free.*
3. **The threshold algebra** — `pert_le_DeltaLB` :
   `r ≥ Rreal a → a⁴/(64 r² ln2) ≤ DeltaLB a`, and its `ℕ` form
   `pert_le_DeltaLB_nat`.  This is exactly Cor. 10.2 (`R(a)` is the solution of
   `a⁴/(64r²ln2) = DeltaLB a`).  *Sorry-free.*
4. **The two analytic inputs** — the Bernstein/center gap (4.12)–(4.14) and the
   strip bound (4.10)
   (`Gfun_le_offstrip_quant`, `center_ge_quant`, `Gfun_le_center_strip_quant`).
5. **Assembly** — `Gfun_le_center_quant` and `supG_eq_center_quant`, derived
   from 3 + 4 with no further gaps.

## Numerical validation

All inequalities were checked numerically before formalisation
(`a = 0.5, 0.9, 0.99, 0.999, 0.99999`, `2·10⁵`-point grid in `d`); see
`research/results_W_lean_bquant.md`.  E.g. at `a = 0.99`,
`DeltaLB = 2.727330e−4` versus the true `min_d deficit = 2.727331e−4`, and
`Rreal = 8.9104`, `R = 9`.
-/

namespace DegeneracyLawQuant

open TwoDegenerateGraphs DegeneracyLaw

noncomputable section

lemma log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-! ## 1. Definitions (paper §4.4, §10.1) -/

/-- `u = 1 - a²`. -/
def uOf (a : ℝ) : ℝ := 1 - a ^ 2

/-- `ρ_crit(a) = ½ arccos √(a²/(2-a²))` (paper §4.4). -/
def rhoCrit (a : ℝ) : ℝ := Real.arccos (Real.sqrt (a ^ 2 / (2 - a ^ 2))) / 2

/-- The shrunken strip half-width `ρ = 0.99 ρ_crit` (paper §4.4). -/
def rho (a : ℝ) : ℝ := (99 / 100) * rhoCrit a

/-- The integrand of `Δ_min` (Prop. 4.2):
`(1-a²)/ln2 · d² - log₂ cos(max(0, ρ - a d))`. -/
def deficit (a d : ℝ) : ℝ :=
  uOf a / Real.log 2 * d ^ 2 - logTwo (Real.cos (max 0 (rho a - a * d)))

/-- **Lemma 10.1's bound** `u ρ² / (ln2 (a² + 2u))`, a lower bound for
`Δ_min(a) = min_{0≤d≤1/2} deficit a d`. -/
def DeltaLB (a : ℝ) : ℝ := uOf a * rho a ^ 2 / (Real.log 2 * (a ^ 2 + 2 * uOf a))

/-- The real-valued threshold `a²√(a²+2u) / (8 ρ(a) √u)` of Cor. 10.2. -/
def Rreal (a : ℝ) : ℝ :=
  a ^ 2 * Real.sqrt (a ^ 2 + 2 * uOf a) / (8 * rho a * Real.sqrt (uOf a))

/-- **`R(a)` of Cor. 10.2**, as a natural number: `⌈Rreal(λ ln2)⌉ ∨ 2`. -/
def R_of (lam : ℝ) : ℕ := max 2 ⌈Rreal (lam * Real.log 2)⌉₊

/-! ## 1'. Basic positivity facts for `ρ` -/

lemma kappa_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    Real.sqrt (a ^ 2 / (2 - a ^ 2)) < 1 := by
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  apply Real.sqrt_lt_sqrt (div_nonneg (sq_nonneg a) (by nlinarith))
  rw [div_lt_one (by nlinarith)]
  nlinarith

lemma kappa_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    0 < Real.sqrt (a ^ 2 / (2 - a ^ 2)) := by
  apply Real.sqrt_pos.2
  apply div_pos (pow_pos ha0 2)
  nlinarith

lemma rho_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < rho a := by
  unfold rho rhoCrit
  have := Real.arccos_pos.2 (kappa_lt_one ha0 ha1)
  linarith

/-- `ρ(a) < π/4`: the strip is well inside a quarter turn. -/
lemma rho_lt_pi_div_four {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    rho a < Real.pi / 4 := by
  unfold rho rhoCrit
  have h1 : Real.arccos (Real.sqrt (a ^ 2 / (2 - a ^ 2))) < Real.pi / 2 :=
    Real.arccos_lt_pi_div_two.2 (kappa_pos ha0 ha1)
  have h2 : (0 : ℝ) < Real.arccos (Real.sqrt (a ^ 2 / (2 - a ^ 2))) :=
    Real.arccos_pos.2 (kappa_lt_one ha0 ha1)
  linarith

lemma rho_lt_pi_div_two {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    rho a < Real.pi / 2 := by
  have := rho_lt_pi_div_four ha0 ha1
  have := Real.pi_pos
  linarith

/-! ## 2a. `log (cos x) ≤ -x²/2` on `[0, π/2)` -/

/-- The derivative of `x ↦ -log (cos x) - x²/2` is `tan x - x`. -/
lemma hasDerivAt_logCosAux {x : ℝ} (hx : Real.cos x ≠ 0) :
    HasDerivAt (fun y : ℝ => -Real.log (Real.cos y) - y ^ 2 / 2)
      (Real.tan x - x) x := by
  have hlog : HasDerivAt (fun y : ℝ => Real.log (Real.cos y))
      (-Real.sin x / Real.cos x) x := (Real.hasDerivAt_cos x).log hx
  have hsq : HasDerivAt (fun y : ℝ => y ^ 2 / 2) x x := by
    have := (hasDerivAt_pow 2 x).div_const 2
    simpa using this
  have := hlog.neg.sub hsq
  refine this.congr_deriv ?_
  rw [Real.tan_eq_sin_div_cos]
  field_simp

/-- **The single-variable engine of Lemma 10.1.**
`log (cos x) ≤ -x²/2` for `0 ≤ x < π/2` — equivalently `cos x ≤ e^{-x²/2}`. -/
theorem log_cos_le_neg_sq_half {x : ℝ} (hx0 : 0 ≤ x) (hx : x < Real.pi / 2) :
    Real.log (Real.cos x) ≤ -(x ^ 2 / 2) := by
  set f : ℝ → ℝ := fun y => -Real.log (Real.cos y) - y ^ 2 / 2 with hf
  -- `cos > 0` on `[0, x]`
  have hcospos : ∀ y ∈ Set.Icc (0 : ℝ) x, 0 < Real.cos y := by
    intro y hy
    refine Real.cos_pos_of_mem_Ioo ⟨?_, ?_⟩
    · have := Real.pi_pos; linarith [hy.1]
    · linarith [hy.2]
  have hcont : ContinuousOn f (Set.Icc (0 : ℝ) x) := by
    apply ContinuousOn.sub
    · apply ContinuousOn.neg
      apply Real.continuousOn_log.comp (Real.continuous_cos.continuousOn)
      intro y hy
      exact ne_of_gt (hcospos y hy)
    · fun_prop
  have hint : interior (Set.Icc (0 : ℝ) x) = Set.Ioo (0 : ℝ) x := interior_Icc
  have hderiv : ∀ y ∈ interior (Set.Icc (0 : ℝ) x),
      HasDerivAt f (Real.tan y - y) y := by
    intro y hy
    rw [hint] at hy
    exact hasDerivAt_logCosAux (ne_of_gt (hcospos y ⟨le_of_lt hy.1, le_of_lt hy.2⟩))
  have hmono : MonotoneOn f (Set.Icc (0 : ℝ) x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 x) hcont ?_ ?_
    · intro y hy
      exact (hderiv y hy).differentiableAt.differentiableWithinAt
    · intro y hy
      rw [(hderiv y hy).deriv]
      rw [hint] at hy
      have := Real.lt_tan hy.1 (lt_trans hy.2 hx)
      linarith
  have h := hmono (Set.left_mem_Icc.2 hx0) (Set.right_mem_Icc.2 hx0) hx0
  simp only [hf] at h
  norm_num at h
  linarith

/-- The `log₂` form used in Prop. 4.2: `-log₂ cos x ≥ x²/(2 ln 2)`. -/
theorem logTwo_cos_le {x : ℝ} (hx0 : 0 ≤ x) (hx : x < Real.pi / 2) :
    logTwo (Real.cos x) ≤ -(x ^ 2 / (2 * Real.log 2)) := by
  have hlog2 := log_two_pos
  have h := log_cos_le_neg_sq_half hx0 hx
  unfold logTwo
  rw [div_le_iff₀ hlog2]
  have e : -(x ^ 2 / (2 * Real.log 2)) * Real.log 2 = -(x ^ 2 / 2) := by
    field_simp
  rw [e]
  exact h

/-! ## 2b. The quadratic minimization (paper Lemma 10.1) -/

/-- The exact identity behind the quadratic minimization of Lemma 10.1:
with `u = 1-a²`, `s = a²+2u = 2-a²`,
`(2u d² + (ρ - a d)²) s - 2 u ρ² = (s d - a ρ)²`. -/
theorem quad_min_key (a d p : ℝ) :
    (2 * (1 - a ^ 2) * d ^ 2 + (p - a * d) ^ 2) * (a ^ 2 + 2 * (1 - a ^ 2))
        - 2 * (1 - a ^ 2) * p ^ 2
      = ((a ^ 2 + 2 * (1 - a ^ 2)) * d - a * p) ^ 2 := by
  ring

/-- The quadratic minimization of Lemma 10.1, in raw algebraic form:
with `t = max(0, p - a d)`, `2(1-a²)p² ≤ (2(1-a²)d² + t²)(2 - a²)`.
Equality holds at `d = a p/(2-a²)`, the paper's `d_*`. -/
theorem quad_min_ineq {a p d t : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hp : 0 < p)
    (_hd : 0 ≤ d) (ht : t = max 0 (p - a * d)) :
    2 * ((1 - a ^ 2) * p ^ 2) ≤ (2 * (1 - a ^ 2) * d ^ 2 + t ^ 2) * (2 - a ^ 2) := by
  rcases le_or_gt 0 (p - a * d) with hc | hc
  · -- interior branch: `t = p - a d`, the exact square identity
    have hteq : t = p - a * d := by rw [ht, max_eq_right hc]
    rw [hteq]
    nlinarith [sq_nonneg ((2 - a ^ 2) * d - a * p)]
  · -- outer branch: `t = 0` and `a d > p`
    have hteq : t = 0 := by rw [ht]; exact max_eq_left (by linarith)
    rw [hteq]
    have had : p < a * d := by linarith
    have hu : (0 : ℝ) < 1 - a ^ 2 := by nlinarith
    have hd2 : p ^ 2 < a ^ 2 * d ^ 2 := by nlinarith
    have e1 : 2 * (1 - a ^ 2) * p ^ 2 < 2 * (1 - a ^ 2) * (a ^ 2 * d ^ 2) := by nlinarith
    have e2 : 2 * (1 - a ^ 2) * (a ^ 2 * d ^ 2) ≤ (2 * (1 - a ^ 2) * d ^ 2) * (2 - a ^ 2) := by
      nlinarith [mul_nonneg (mul_nonneg (by linarith : (0 : ℝ) ≤ 2 * (1 - a ^ 2))
        (sq_nonneg d)) (by nlinarith : (0 : ℝ) ≤ 2 - 2 * a ^ 2)]
    nlinarith

/-- **Lemma 10.1.** For `0 < a < 1` and `d ≥ 0`,
`deficit a d ≥ u ρ(a)² / (ln 2 (a² + 2u))`.  Since `Δ_min(a)` is the infimum of
`deficit a ·` over `d ∈ [0,1/2]`, this is exactly the paper's
`Δ_min(a) ≥ u ρ²/(ln2 (a²+2u))`. -/
theorem DeltaLB_le_deficit {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) {d : ℝ} (hd : 0 ≤ d) :
    DeltaLB a ≤ deficit a d := by
  have hlog2 := log_two_pos
  have hrho := rho_pos ha0 ha1
  have hkey := quad_min_ineq ha0 ha1 hrho hd (rfl : max 0 (rho a - a * d) = _)
  obtain ⟨T, hT⟩ : ∃ T : ℝ, T = max 0 (rho a - a * d) := ⟨_, rfl⟩
  rw [← hT] at hkey
  have ht0 : (0 : ℝ) ≤ T := hT ▸ le_max_left _ _
  have htr : T ≤ rho a := hT ▸ max_le hrho.le (by nlinarith)
  have htpi : T < Real.pi / 2 := lt_of_le_of_lt htr (rho_lt_pi_div_two ha0 ha1)
  have hstep1 := logTwo_cos_le ht0 htpi
  have hpos : (0 : ℝ) < Real.log 2 * (a ^ 2 + 2 * (1 - a ^ 2)) :=
    mul_pos hlog2 (by nlinarith)
  unfold deficit DeltaLB uOf
  rw [← hT]
  have hlow : (1 - a ^ 2) * rho a ^ 2 / (Real.log 2 * (a ^ 2 + 2 * (1 - a ^ 2)))
      ≤ (1 - a ^ 2) / Real.log 2 * d ^ 2 + T ^ 2 / (2 * Real.log 2) := by
    rw [div_le_iff₀ hpos]
    have hexp : ((1 - a ^ 2) / Real.log 2 * d ^ 2 + T ^ 2 / (2 * Real.log 2)) *
        (Real.log 2 * (a ^ 2 + 2 * (1 - a ^ 2)))
        = (2 * (1 - a ^ 2) * d ^ 2 + T ^ 2) * (2 - a ^ 2) / 2 := by
      field_simp; ring
    rw [hexp]
    linarith
  linarith

/-! ## 3. The threshold: `r ≥ R(a)` kills the Bernstein perturbation -/

lemma Rreal_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < Rreal a := by
  have hrho := rho_pos ha0 ha1
  have hu0 : 0 < uOf a := by unfold uOf; nlinarith
  have hs : 0 < a ^ 2 + 2 * uOf a := by unfold uOf; nlinarith
  unfold Rreal
  apply div_pos
  · exact mul_pos (by positivity) (Real.sqrt_pos.2 hs)
  · exact mul_pos (by linarith) (Real.sqrt_pos.2 hu0)

/-- **Corollary 10.2 (the algebraic content).**  If `r ≥ Rreal a` then the
Bernstein excess `a⁴/(64 r² ln 2)` is at most the off-strip deficit bound
`DeltaLB a`.  This is the defining property of `R(a)`: `Rreal a` is exactly the
positive root of `a⁴/(64 r² ln2) = u ρ²/(ln2 (a²+2u))`. -/
theorem pert_le_DeltaLB {a r : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hr : Rreal a ≤ r) :
    a ^ 4 / (64 * r ^ 2 * Real.log 2) ≤ DeltaLB a := by
  have hlog2 := log_two_pos
  have hrho := rho_pos ha0 ha1
  have hu0 : 0 < uOf a := by unfold uOf; nlinarith
  have hs : 0 < a ^ 2 + 2 * uOf a := by unfold uOf; nlinarith
  have hrpos : 0 < r := lt_of_lt_of_le (Rreal_pos ha0 ha1) hr
  set su : ℝ := Real.sqrt (uOf a) with hsu
  set ss : ℝ := Real.sqrt (a ^ 2 + 2 * uOf a) with hss
  have hsu0 : 0 < su := Real.sqrt_pos.2 hu0
  have hss0 : 0 < ss := Real.sqrt_pos.2 hs
  have hsu2 : su ^ 2 = uOf a := Real.sq_sqrt hu0.le
  have hss2 : ss ^ 2 = a ^ 2 + 2 * uOf a := Real.sq_sqrt hs.le
  -- unfold the hypothesis
  have h1 : a ^ 2 * ss ≤ 8 * rho a * su * r := by
    have := hr
    unfold Rreal at this
    rw [← hsu, ← hss] at this
    rw [div_le_iff₀ (by positivity)] at this
    linarith
  have h1nn : 0 ≤ a ^ 2 * ss := by positivity
  have hsq : (a ^ 2 * ss) ^ 2 ≤ (8 * rho a * su * r) ^ 2 := by
    exact pow_le_pow_left₀ h1nn h1 2
  have hexp : a ^ 4 * (a ^ 2 + 2 * uOf a) ≤ 64 * r ^ 2 * (uOf a * rho a ^ 2) := by
    have e1 : (a ^ 2 * ss) ^ 2 = a ^ 4 * (a ^ 2 + 2 * uOf a) := by
      rw [mul_pow, hss2]; ring
    have e2 : (8 * rho a * su * r) ^ 2 = 64 * r ^ 2 * (uOf a * rho a ^ 2) := by
      have : (8 * rho a * su * r) ^ 2 = 64 * rho a ^ 2 * su ^ 2 * r ^ 2 := by ring
      rw [this, hsu2]; ring
    rw [e1, e2] at hsq
    exact hsq
  unfold DeltaLB
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hexp, hlog2, sq_nonneg r]

/-- The `ℕ`-indexed form: `R_of lam ≤ r` implies the perturbation bound. -/
theorem pert_le_DeltaLB_nat {lam : ℝ} {r : ℕ} (ha0 : 0 < lam * Real.log 2)
    (ha1 : lam * Real.log 2 < 1) (hR : R_of lam ≤ r) :
    (lam * Real.log 2) ^ 4 / (64 * (r : ℝ) ^ 2 * Real.log 2)
      ≤ DeltaLB (lam * Real.log 2) := by
  apply pert_le_DeltaLB ha0 ha1
  have h1 : Rreal (lam * Real.log 2) ≤ (⌈Rreal (lam * Real.log 2)⌉₊ : ℝ) := Nat.le_ceil _
  have h2 : (⌈Rreal (lam * Real.log 2)⌉₊ : ℕ) ≤ r := le_trans (le_max_right _ _) hR
  have h3 : ((⌈Rreal (lam * Real.log 2)⌉₊ : ℕ) : ℝ) ≤ (r : ℝ) := Nat.cast_le.2 h2
  linarith

/-- `R_of` always demands `r ≥ 2`, as Lemma 4.2's Bernstein step needs. -/
lemma two_le_R_of (lam : ℝ) : 2 ≤ R_of lam := le_max_left _ _

/-! ## 3'. The two-sided log cosh bound: `log cosh t ≥ t²/2 - t⁴/12`

This is the single-variable ingredient of the Bernstein/center gap (4.14).
Once combined with the binomial moments `E X_r² = r`, `E X_r⁴ = 3r² - 2r` it
yields `μ_r ≤ a⁴(3r²-2r)/(192 r⁴ ln2) ≤ a⁴/(64 r² ln2)`, i.e. `center_ge_quant`
below.

The bound itself is *not* reproved here: `DegeneracyLaw.log_cosh_ge`
(`WindowUpper.lean`, an alias for the canonical `DegeneracyLaw.LemmaC.le_log_cosh`)
is the single home for the whole `log cosh` / `tanh` toolkit.  Only the `log₂`
rescaling actually used by (4.14) lives in this file.
-/

/-- The `log₂` form used in (4.14). -/
theorem logTwo_cosh_ge (t : ℝ) :
    (t ^ 2 / 2 - t ^ 4 / 12) / Real.log 2 ≤ logTwo (Real.cosh t) := by
  have hlog2 := log_two_pos
  unfold logTwo
  rw [div_le_div_iff₀ hlog2 hlog2]
  nlinarith [log_cosh_ge t, hlog2]

/-! ## 4. The two analytic inputs

These are the parts of the paper's §4.6 whose *analytic* content lives in
`Lemma42.lean` (now sorry-free).  This section instantiates that machinery with
the `a`-dependent strip half-width `ρ(a)` in place of the fixed-`λ` constants,
and adds the one genuinely new ingredient, `DeltaLB_le_quad`.
-/

/-- The angular coordinate `θ` with `v = sin²θ`. -/
def thetaOf (v : ℝ) : ℝ := Real.arcsin (Real.sqrt v)

/-- The strip `|θ - π/4| ≤ ρ(a)` in `v`-coordinates. -/
def inStripQ (lam v : ℝ) : Prop :=
  |thetaOf v - Real.pi / 4| ≤ rho (lam * Real.log 2)

/-! ### 4'. The bridge to `LemmaB`

`DegeneracyLawQuant.rhoCrit/rho/thetaOf/inStripQ` are *syntactically* the same
definitions as `DegeneracyLaw.LemmaB.rhoCrit/rho/thetaOf/inStrip`, so the bridge
is `rfl` in every case.  Keeping the two copies means this file still reads
standalone, while the proofs below can call `LemmaB` directly. -/

lemma thetaOf_eq (v : ℝ) : thetaOf v = DegeneracyLaw.LemmaB.thetaOf v := rfl
lemma inStripQ_iff (lam v : ℝ) : inStripQ lam v ↔ DegeneracyLaw.LemmaB.inStrip lam v :=
  Iff.rfl

/-! ### 4''. The quadratic margin versus `DeltaLB`

The single new inequality this file needs on top of `LemmaB`: the quadratic
margin `(1-a²)D² + E²/2` produced by `LemmaB.Gfun_le_center_margin` dominates
`ln2 · DeltaLB a` as soon as `E ≥ ρ(a) - a D` — which is exactly what being off
the strip provides, via the triangle inequality with `|θ* - π/4| ≤ a D`. -/

theorem DeltaLB_le_quad {a D E : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hD : 0 ≤ D) (hE : 0 ≤ E) (hDE : rho a - a * D ≤ E) :
    DeltaLB a ≤ ((1 - a ^ 2) * D ^ 2 + E ^ 2 / 2) / Real.log 2 := by
  have hlog2 := log_two_pos
  have hrho := rho_pos ha0 ha1
  have hkey := quad_min_ineq ha0 ha1 hrho hD (rfl : max 0 (rho a - a * D) = _)
  set T : ℝ := max 0 (rho a - a * D) with hT
  have hT0 : (0 : ℝ) ≤ T := le_max_left _ _
  have hTE : T ≤ E := max_le hE hDE
  have hTsq : T ^ 2 ≤ E ^ 2 := by nlinarith
  have hs2 : (0 : ℝ) < 2 - a ^ 2 := by nlinarith
  have hkey' : 2 * ((1 - a ^ 2) * rho a ^ 2)
      ≤ (2 * (1 - a ^ 2) * D ^ 2 + E ^ 2) * (2 - a ^ 2) := by nlinarith
  unfold DeltaLB uOf
  rw [div_le_div_iff₀ (by nlinarith : (0:ℝ) < Real.log 2 * (a ^ 2 + 2 * (1 - a ^ 2)))
    hlog2]
  nlinarith [hkey', hlog2, sq_nonneg D, sq_nonneg E]

/-- **(4.12) + Prop. 4.2, quantified.**  Off the strip, `G_r` falls below the
unperturbed center value by the full deficit, up to the Bernstein excess
`a²/(8 r ln 2)`.

Proof sketch (paper §4.5–4.6(i)): write
`g₀(q,θ) = F_a(q)/2 + log₂ cos(θ - θ*(q))` with `θ*(q) = arctan e^{a(2q-1)}`;
`LemmaA.Ffun_le_center` gives `½(F_a(½) - F_a(q)) ≥ (1-a²)d²/ln2` with
`d = |q-½|`, and `|θ*(q) - π/4| ≤ a d` gives
`-log₂ cos(θ-θ*) ≥ -log₂ cos(max(0, ρ - a d))`; adding is `deficit a d`, which
`DeltaLB_le_deficit` bounds below by `DeltaLB a`.  The `a²/(8r ln2)` is (4.12),
from `ψ_yy ≤ a²/ln2` and `B_r[(y-q)²] = q(1-q)/r ≤ 1/(4r)`.

**Proved** by `DegeneracyLaw.LemmaB.Gfun_le_center_margin` — which packages all
of the above into the `λ`-free bound
`G_r ≤ 1-λ/2-((1-a²)(q-½)²+(θ-θ*)²/2)/ln2 + a²/(8r ln2)`, together with
`|θ* - π/4| ≤ a|q-½|` — followed by `DeltaLB_le_quad`, which turns the off-strip
hypothesis `|θ-π/4| > ρ(a)` into `|θ-θ*| ≥ ρ(a) - a|q-½|` and hence into
`DeltaLB a ≤ (quadratic margin)/ln2`. -/
theorem Gfun_le_offstrip_quant (r : ℕ) (lam q v : ℝ) (hr : 2 ≤ r)
    (ha0 : 0 < lam * Real.log 2) (ha1 : lam * Real.log 2 < 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hoff : ¬ inStripQ lam v) :
    Gfun r lam q v
      ≤ 1 - lam / 2 - DeltaLB (lam * Real.log 2)
          + (lam * Real.log 2) ^ 2 / (8 * (r : ℝ) * Real.log 2) := by
  have hlog2 := log_two_pos
  have hR2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hRpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hoff0 : rho (lam * Real.log 2) < |DegeneracyLaw.LemmaB.thetaOf v - Real.pi / 4| := by
    have h : ¬ inStripQ lam v := hoff
    unfold inStripQ at h
    rw [thetaOf_eq] at h
    exact not_le.1 h
  obtain ⟨ts, hstarbd, hup⟩ :=
    DegeneracyLaw.LemmaB.Gfun_le_center_margin r lam q v hr ha0 ha1 hq hv
  set a : ℝ := lam * Real.log 2 with hadef
  set θ : ℝ := DegeneracyLaw.LemmaB.thetaOf v with hθdef
  clear_value a θ
  have hoff' : rho a < |θ - Real.pi / 4| := hoff0
  have htri : |θ - Real.pi / 4| ≤ |θ - ts| + |ts - Real.pi / 4| :=
    abs_sub_le θ ts (Real.pi / 4)
  have hDE : rho a - a * |q - 1 / 2| ≤ |θ - ts| := by linarith
  have hquad := DeltaLB_le_quad ha0 ha1 (abs_nonneg (q - 1 / 2)) (abs_nonneg (θ - ts)) hDE
  rw [sq_abs, sq_abs] at hquad
  have hfin : ((1 - a ^ 2) * (q - 1 / 2) ^ 2 + (θ - ts) ^ 2 / 2) / Real.log 2
      = -(-((1 - a ^ 2) * (q - 1 / 2) ^ 2 + (θ - ts) ^ 2 / 2) / Real.log 2) := by ring
  have hpert : (a ^ 2 / (8 * (r : ℝ))) / Real.log 2
      = a ^ 2 / (8 * (r : ℝ) * Real.log 2) := by
    field_simp
  linarith [hup, hquad, hpert.le, hpert.ge]

/-- **(4.13) + (4.14), quantified.**  The center value exceeds
`1 - λ/2 + a²/(8 r ln2)` minus the fourth-order defect `μ_r ≤ a⁴/(64 r² ln2)`.

Proof sketch (paper §4.6(ii)–(iii)): `G_r(½,½) = 1 - λ/2 + E log₂ cosh(aX_r/2r)`
with `X_r = 2J - r`, `J ~ Bin(r,½)`; then `logTwo_cosh_ge` (proved above,
sorry-free) plus the binomial moments `E X_r² = r`, `E X_r⁴ = 3r² - 2r`
give `μ_r ≤ a⁴(3r²-2r)/(192 r⁴ ln2) ≤ a⁴/(64 r² ln2)` for `r ≥ 2`.

**Proved** by `DegeneracyLaw.Gfun_center_eq` (identity (4.13)) plus
`DegeneracyLaw.centerSum_lower` (`WindowUpper`'s Taylor bound, which already carries
the binomial moments `E X_r² = r`, `E X_r⁴ = 3r² - 2r`): the latter gives the
stronger `… + a⁴/(96 r³ ln2)`, and we simply discard that positive term. -/
theorem center_ge_quant (r : ℕ) (lam : ℝ) (hr : 2 ≤ r)
    (ha0 : 0 < lam * Real.log 2) (ha1 : lam * Real.log 2 < 1) :
    1 - lam / 2 + (lam * Real.log 2) ^ 2 / (8 * (r : ℝ) * Real.log 2)
        - (lam * Real.log 2) ^ 4 / (64 * (r : ℝ) ^ 2 * Real.log 2)
      ≤ Gfun r lam (1 / 2) (1 / 2) := by
  have hlog2 := log_two_pos
  have hR2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hRpos : (0 : ℝ) < (r : ℝ) := by linarith
  rw [DegeneracyLaw.Gfun_center_eq r lam (by omega)]
  unfold centerSum
  have h := DegeneracyLaw.centerSum_lower r lam (by omega)
  set a : ℝ := lam * Real.log 2 with hadef
  have hnn : (0 : ℝ) ≤ a ^ 4 / (96 * (r : ℝ) ^ 3) := by positivity
  have e1 : a ^ 2 / (8 * (r : ℝ) * Real.log 2) = (a ^ 2 / (8 * (r : ℝ))) / Real.log 2 := by
    field_simp
  have e2 : a ^ 4 / (64 * (r : ℝ) ^ 2 * Real.log 2)
      = (a ^ 4 / (64 * (r : ℝ) ^ 2)) / Real.log 2 := by field_simp
  have e3 : (a ^ 2 / (8 * (r : ℝ)) - a ^ 4 / (64 * (r : ℝ) ^ 2)
        + a ^ 4 / (96 * (r : ℝ) ^ 3)) / Real.log 2
      = (a ^ 2 / (8 * (r : ℝ))) / Real.log 2 - (a ^ 4 / (64 * (r : ℝ) ^ 2)) / Real.log 2
        + (a ^ 4 / (96 * (r : ℝ) ^ 3)) / Real.log 2 := by ring
  have hnn2 : (0 : ℝ) ≤ (a ^ 4 / (96 * (r : ℝ) ^ 3)) / Real.log 2 :=
    div_nonneg hnn hlog2.le
  rw [e1, e2]
  linarith [h, e3.le, e3.ge]

/-- **(4.10).**  Inside the strip the Hessian of `G_r` is negative definite
(Prop. 4.1) and the strip is invariant under `(q,θ) ↦ (1-q, π/2-θ)` whose unique
fixed point is the center, so the center dominates.  No `r₀` is needed here. -/
theorem Gfun_le_center_strip_quant (r : ℕ) (lam q v : ℝ) (hr : 2 ≤ r)
    (ha0 : 0 < lam * Real.log 2) (ha1 : lam * Real.log 2 < 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hin : inStripQ lam v) :
    Gfun r lam q v ≤ Gfun r lam (1 / 2) (1 / 2) :=
  DegeneracyLaw.LemmaB.Gfun_le_center_strip r lam q v hr ha0 ha1 hq hv
    ((inStripQ_iff lam v).1 hin)

/-! ## 5. Assembly (Lemma 4.2 with the explicit threshold `R_of`) -/

/-- **Lemma 4.2, quantified, pointwise form.**  For every subcritical `λ` and
every `r ≥ R_of λ`, the center dominates `G_r` on `[0,1]²`. -/
theorem Gfun_le_center_quant (r : ℕ) (lam : ℝ)
    (ha0 : 0 < lam * Real.log 2) (ha1 : lam * Real.log 2 < 1)
    (hR : R_of lam ≤ r) (q v : ℝ)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    Gfun r lam q v ≤ Gfun r lam (1 / 2) (1 / 2) := by
  have hr : 2 ≤ r := le_trans (two_le_R_of lam) hR
  by_cases hin : inStripQ lam v
  · exact Gfun_le_center_strip_quant r lam q v hr ha0 ha1 hq hv hin
  · have hoff := Gfun_le_offstrip_quant r lam q v hr ha0 ha1 hq hv hin
    have hcen := center_ge_quant r lam hr ha0 ha1
    have hpert := pert_le_DeltaLB_nat ha0 ha1 hR
    linarith

/-- Turning a pointwise bound into a statement about `sSup`. -/
theorem supG_eq_center_of_le (r : ℕ) (lam : ℝ)
    (hle : ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      Gfun r lam q v ≤ Gfun r lam (1 / 2) (1 / 2)) :
    supG r lam = Gfun r lam (1 / 2) (1 / 2) := by
  have hmemq : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hmem : Gfun r lam (1 / 2) (1 / 2) ∈
      Set.image2 (Gfun r lam) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) :=
    Set.mem_image2_of_mem hmemq hmemq
  have hub : ∀ x ∈ Set.image2 (Gfun r lam) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1),
      x ≤ Gfun r lam (1 / 2) (1 / 2) := by
    rintro x ⟨q, hq, v, hv, rfl⟩
    exact hle q hq v hv
  unfold supG
  exact le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨_, hub⟩ hmem)

/-- **Lemma 4.2 with the explicit threshold (Prop. 10.3's engine).**
For every subcritical `λ` (`λ ln 2 < 1`) and every `r ≥ R_of λ`,
`sup_{[0,1]²} G_r = G_r(½,½)`.  Combined with Prop. 10.3's estimate
`R_of λ_r ≤ ⌈0.2406 r / ln r⌉ ≤ r` along the tuned sequence, this is what makes
Theorem 1.3(b) available at every `r ≥ 2` with no unproved finite checks. -/
theorem supG_eq_center_quant (r : ℕ) (lam : ℝ)
    (ha0 : 0 < lam * Real.log 2) (ha1 : lam * Real.log 2 < 1)
    (hR : R_of lam ≤ r) :
    supG r lam = Gfun r lam (1 / 2) (1 / 2) :=
  supG_eq_center_of_le r lam fun q hq v hv =>
    Gfun_le_center_quant r lam ha0 ha1 hR q v hq hv

end

end DegeneracyLawQuant
