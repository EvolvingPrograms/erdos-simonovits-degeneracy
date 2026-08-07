import Lemma41
import Lemma42
import WindowUpper
import LedgerAsym

/-!
# Supercritical blow-up of `G_r`

Machinery for the supercritical sharpness of Theorem 1.3(a); the statement itself is
`DegeneracyLawSuper.threshold_sharp` in `WindowSharp.lean`.

Design-notes reference (notes not shipped in this repository): §6.7 (supercritical sharpness), verified numerically in §6.8.

Above the Gibbs threshold — `a = λ ln 2 > 1` — the center `(½,½)` stops being
the maximizer of `G_r`, and it loses by a **constant**, not by an `O(r^{-2})`
amount.  One explicit competitor suffices:

  `q = ½ + t`,  `v = e^{-2a(1-q)}/(e^{-2aq} + e^{-2a(1-q)})`.

The proof has four steps, mirroring the paper.

* **(i) Jensen removes `r`.**  `ψ(·,θ) = log₂ T(·,θ)` is convex in `y`
  (`psi_y2_nonneg`, the `≥ 0` half of (4.3a)), so the Bernstein operator — an
  expectation over `J/r` with mean `q` — only increases it:
  `bern_psi_ge`, giving `G_r(q,v) ≥ h(q)/2 + ψ(q,θ)` for **every** `r`.
* **(ii) The `v`-supremum is `F_a/2`.**  At the competitor's `v`,
  `T(q,θ) = √(e^{-2aq} + e^{-2a(1-q)})` (the polar identity `Tang_eq_polar` at
  `θ = θ*(q)`), hence `h(q)/2 + ψ(q,θ) = F_a(q)/2`: `Gfun_ge_Ffun_half`.
* **(iii) Above threshold the center is a strict local minimum of `F_a`.**  The
  Lemma 4.1 identity `F_a''(q) ln2 = -1/(q(1-q)) + 4a² sech²(a(1-2q))` is an
  identity for every `a > 0`; only its *sign* conclusion needed `a < 1`.  With
  `sech²x ≥ 1 - x²` and `-1/(q(1-q)) ≥ -4 - 32s²` one gets
  `F_a''(½+s) ln2 ≥ 4(a²-1) - 16s²(2+a⁴) ≥ 2(a²-1) > 0`, so
  `F_a(½+t) - F_a(½) ≥ (a²-1)t²/ln2 = 2δ(a)`: `Ffun_ge_center_super`.
* **(iv) The `C`-side, crudely.**  The `k = 1` term of the positive series (5.2)
  gives `r(1 - h(τ_r)) ≥ a²/(8r ln2)` (`DegeneracyLedger.le_r_mul_one_sub_Cside`).

Assembling: `width_le_super`, then `width_le_super'` with the explicit
`t(a) = √(min(⅛, (a²-1)/(8(2+a⁴))))`, and finally `rsq_width_tendsto_atBot`:

  `r² · width_r ⟶ -∞`,  i.e. `W(λ) = -∞` for `λ > 1/ln 2`.

Together with Theorem 1.3(a) (`W(λ) = λ⁴ln³2/64 > 0` for `λ < 1/ln 2`) and
Theorem 1.3(b) (the endpoint `λ*` is attained along the drifting schedule), this
makes the threshold `λ* = 1/ln 2` **sharp**: `threshold_sharp`.

**This file is `sorry`-free.**
-/

namespace DegeneracyLawSuper

open DegeneracyLaw DegeneracyLaw.LemmaB TwoDegenerateGraphs Filter Topology

noncomputable section

lemma logTwo_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

private lemma HDA {f : ℝ → ℝ} {c d x : ℝ} (h : HasDerivAt f c x) (hcd : c = d) :
    HasDerivAt f d x := hcd ▸ h

/-! ## §0 `sech² y ≥ 1 - y²` -/

/-- `d/dy tanh y = 1 / cosh²y`. -/
lemma hasDerivAt_tanh (y : ℝ) : HasDerivAt Real.tanh (1 / Real.cosh y ^ 2) y := by
  have hc : (0 : ℝ) < Real.cosh y := Real.cosh_pos y
  have h := (Real.hasDerivAt_sinh y).div (Real.hasDerivAt_cosh y) (ne_of_gt hc)
  have hfun : Real.tanh = fun x : ℝ => Real.sinh x / Real.cosh x := by
    funext x; exact Real.tanh_eq_sinh_div_cosh x
  rw [hfun]
  refine HDA h ?_
  have hp := Real.cosh_sq_sub_sinh_sq y
  field_simp
  linarith [hp]

/-- `tanh y ≤ y` for `y ≥ 0`. -/
lemma tanh_le_self {y : ℝ} (hy : 0 ≤ y) : Real.tanh y ≤ y := by
  have hd : ∀ x : ℝ, HasDerivAt (fun z : ℝ => z - Real.tanh z)
      (1 - 1 / Real.cosh x ^ 2) x := fun x =>
    (hasDerivAt_id x).sub (hasDerivAt_tanh x)
  have hmono : Monotone (fun z : ℝ => z - Real.tanh z) := by
    refine monotone_of_deriv_nonneg (fun x => (hd x).differentiableAt) ?_
    intro x
    rw [(hd x).deriv]
    have hc : (1 : ℝ) ≤ Real.cosh x := Real.one_le_cosh x
    have hc2 : (1 : ℝ) ≤ Real.cosh x ^ 2 := by nlinarith
    have : 1 / Real.cosh x ^ 2 ≤ 1 := by
      rw [div_le_one (by linarith)]; linarith
    linarith
  have h := hmono hy
  simp only [Real.tanh_zero, sub_zero] at h
  linarith

/-- `tanh²y ≤ y²` for every real `y`. -/
lemma tanh_sq_le_sq (y : ℝ) : Real.tanh y ^ 2 ≤ y ^ 2 := by
  rcases le_total 0 y with hy | hy
  · have h1 := tanh_le_self hy
    have h2 : 0 ≤ Real.tanh y := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.2 hy) (Real.cosh_pos y).le
    nlinarith
  · have hy' : (0 : ℝ) ≤ -y := by linarith
    have h1 := tanh_le_self hy'
    have h2 : 0 ≤ Real.tanh (-y) := by
      rw [Real.tanh_eq_sinh_div_cosh]
      exact div_nonneg (Real.sinh_nonneg_iff.2 hy') (Real.cosh_pos _).le
    rw [Real.tanh_neg] at h1 h2
    nlinarith

/-- **`sech² y ≥ 1 - y²`** — step (iii)'s second ingredient. -/
lemma one_sub_sq_le_sech_sq (y : ℝ) : 1 - y ^ 2 ≤ 1 / Real.cosh y ^ 2 := by
  have hc : (0 : ℝ) < Real.cosh y := Real.cosh_pos y
  have hid : 1 / Real.cosh y ^ 2 = 1 - Real.tanh y ^ 2 := by
    rw [Real.tanh_eq_sinh_div_cosh]
    have hp := Real.cosh_sq_sub_sinh_sq y
    field_simp
    linarith [hp]
  rw [hid]
  linarith [tanh_sq_le_sq y]

/-! ## §1 Step (iii): `F_a(½+t) - F_a(½) ≥ (a²-1)t²/ln 2` -/

/-- **Supercritical sharpness, step (iii).**  Above threshold (`a > 1`) the center is a strict
local *minimum* of `F_a`: for any `t` with `t² ≤ ⅛` and
`16t²(2+a⁴) ≤ 2(a²-1)`,

  `F_a(½ + t) ≥ F_a(½) + (a²-1)t²/ln 2`.

The Lemma 4.1 identity `F_a'' ln2 = -1/(q(1-q)) + 4a²sech²(a(1-2q))` is used with
the *opposite* sign to Lemma 4.1's own use of it. -/
theorem Ffun_ge_center_super (a t : ℝ) (ha : 1 < a) (ht0 : 0 < t) (hts : t ^ 2 ≤ 1 / 8)
    (hcond : 16 * t ^ 2 * (2 + a ^ 4) ≤ 2 * (a ^ 2 - 1)) :
    Ffun a (1 / 2) + (a ^ 2 - 1) * t ^ 2 / Real.log 2 ≤ Ffun a (1 / 2 + t) := by
  have hL := logTwo_pos
  have ht : t < 1 / 2 := by nlinarith
  set D : ℝ → ℝ := fun x =>
    Real.log (1 - x) - Real.log x - 2 * a * Real.tanh (a * (1 - 2 * x)) with hD
  set f : ℝ → ℝ := fun x =>
    Real.log 2 * Ffun a x - Real.log 2 * Ffun a (1 / 2) - (a ^ 2 - 1) * (x - 1 / 2) ^ 2 with hf
  set f1 : ℝ → ℝ := fun x => D x - 2 * (a ^ 2 - 1) * (x - 1 / 2) with hf1
  set f2 : ℝ → ℝ := fun x =>
    (-(1 / (x * (1 - x))) + 4 * a ^ 2 * (1 / Real.cosh (a * (1 - 2 * x)) ^ 2))
      - 2 * (a ^ 2 - 1) with hf2
  have hmem : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (1 / 2 + t), x ∈ Set.Ioo (0 : ℝ) 1 := by
    rintro x ⟨hx0, hx1⟩; exact ⟨by linarith, by linarith⟩
  have hderf : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (1 / 2 + t), HasDerivAt f (f1 x) x := by
    intro x hx
    obtain ⟨h1, h2, _⟩ := Ffun_second_deriv a x (hmem x hx)
    have hq : HasDerivAt (fun y : ℝ => (a ^ 2 - 1) * (y - 1 / 2) ^ 2)
        (2 * (a ^ 2 - 1) * (x - 1 / 2)) x := by
      have hs : HasDerivAt (fun y : ℝ => y - (1 : ℝ) / 2) 1 x := (hasDerivAt_id x).sub_const _
      have hp : HasDerivAt (fun y : ℝ => (y - 1 / 2) ^ 2) (2 * (x - 1 / 2)) x := by
        simp only [pow_two]; exact HDA (hs.mul hs) (by ring)
      exact HDA (hp.const_mul (a ^ 2 - 1)) (by ring)
    exact HDA ((h1.sub_const _).sub hq) (by simp [hf1, hD])
  have hderf1 : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (1 / 2 + t), HasDerivAt f1 (f2 x) x := by
    intro x hx
    obtain ⟨_, h2, _⟩ := Ffun_second_deriv a x (hmem x hx)
    have hlin : HasDerivAt (fun y : ℝ => 2 * (a ^ 2 - 1) * (y - 1 / 2))
        (2 * (a ^ 2 - 1)) x :=
      HDA (((hasDerivAt_id x).sub_const (1 / 2 : ℝ)).const_mul (2 * (a ^ 2 - 1))) (by ring)
    exact HDA (h2.sub hlin) (by simp [hf2])
  have hf2nn : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (1 / 2 + t), 0 ≤ f2 x := by
    rintro x ⟨hx0, hx1⟩
    set s : ℝ := x - 1 / 2 with hs
    have hs0 : 0 ≤ s := by simp only [hs]; linarith
    have hst : s ≤ t := by simp only [hs]; linarith
    have hssq : s ^ 2 ≤ t ^ 2 := by nlinarith
    have hs8 : s ^ 2 ≤ 1 / 8 := le_trans hssq hts
    have hxx : x * (1 - x) = 1 / 4 - s ^ 2 := by simp only [hs]; ring
    have hxxpos : (0 : ℝ) < x * (1 - x) := by rw [hxx]; nlinarith
    have hd : (0 : ℝ) < 1 / 4 - s ^ 2 := by rw [← hxx]; exact hxxpos
    have hent : -(4 : ℝ) - 32 * s ^ 2 ≤ -(1 / (x * (1 - x))) := by
      have hinv : 1 / (1 / 4 - s ^ 2) ≤ 4 + 32 * s ^ 2 := by
        rw [div_le_iff₀ hd]
        nlinarith [sq_nonneg s, sq_nonneg (s ^ 2)]
      rw [hxx]; linarith
    have hsech := one_sub_sq_le_sech_sq (a * (1 - 2 * x))
    have harg : a * (1 - 2 * x) = -(2 * a * s) := by simp only [hs]; ring
    have hsech' : 4 * a ^ 2 - 16 * a ^ 4 * s ^ 2
        ≤ 4 * a ^ 2 * (1 / Real.cosh (a * (1 - 2 * x)) ^ 2) := by
      rw [harg] at hsech ⊢
      nlinarith [hsech, sq_nonneg a]
    have ha4 : (0 : ℝ) ≤ 2 + a ^ 4 := by positivity
    have hstep : 16 * s ^ 2 * (2 + a ^ 4) ≤ 16 * t ^ 2 * (2 + a ^ 4) := by
      nlinarith [hssq, ha4]
    simp only [hf2]
    linarith [hent, hsech', hcond, hstep]
  have hf1half : f1 (1 / 2) = 0 := by
    simp only [hf1, hD]
    norm_num
  have hf1nn : ∀ x ∈ Set.Icc (1 / 2 : ℝ) (1 / 2 + t), 0 ≤ f1 x := by
    intro x hx
    rcases eq_or_lt_of_le hx.1 with heq | hlt
    · rw [← heq, hf1half]
    · have hsub : Set.Icc (1 / 2 : ℝ) x ⊆ Set.Icc (1 / 2 : ℝ) (1 / 2 + t) :=
        Set.Icc_subset_Icc le_rfl hx.2
      obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f1 f2 hlt
        (fun y hy => ((hderf1 y (hsub hy)).continuousAt).continuousWithinAt)
        (fun y hy => hderf1 y (hsub (Set.mem_Icc_of_Ioo hy)))
      have hξmem : ξ ∈ Set.Icc (1 / 2 : ℝ) (1 / 2 + t) :=
        hsub (Set.mem_Icc_of_Ioo hξ)
      have h0 := hf2nn ξ hξmem
      rw [hslope, hf1half, sub_zero, le_div_iff₀ (by linarith)] at h0
      linarith
  have hfhalf : f (1 / 2) = 0 := by simp [hf]
  have hlt : (1 / 2 : ℝ) < 1 / 2 + t := by linarith
  obtain ⟨ξ, hξ, hslope⟩ := exists_hasDerivAt_eq_slope f f1 hlt
    (fun y hy => ((hderf y hy).continuousAt).continuousWithinAt)
    (fun y hy => hderf y (Set.mem_Icc_of_Ioo hy))
  have h0 := hf1nn ξ (Set.mem_Icc_of_Ioo hξ)
  rw [hslope, hfhalf, sub_zero, le_div_iff₀ (by linarith)] at h0
  simp only [hf] at h0
  rw [show (1 : ℝ) / 2 + t - 1 / 2 = t by ring] at h0
  have key : (a ^ 2 - 1) * t ^ 2 / Real.log 2 ≤ Ffun a (1 / 2 + t) - Ffun a (1 / 2) := by
    rw [div_le_iff₀ hL]; nlinarith [h0]
  linarith

/-! ## §2 Step (i): Jensen for the Bernstein operator -/

open LemmaB in
/-- **The `≥ 0` half of (4.3a).**  On the closed quadrant `ψ(·,θ)` is convex in
`y`: `ψ_yy = (a²T² - T_y²)/(T² ln2) ≥ 0`, because `T_y = a(sin θ·F - cos θ·E)`
while `T = cos θ·E + sin θ·F`, so `a²T² - T_y² = 4a² cos θ E sin θ F ≥ 0`. -/
lemma psi_y2_nonneg (a y θ : ℝ) (hc : 0 ≤ Real.cos θ) (hs : 0 ≤ Real.sin θ) :
    0 ≤ (a ^ 2 * (Tang a y θ) ^ 2 - (Ty a y θ) ^ 2) / ((Tang a y θ) ^ 2 * Real.log 2) := by
  have hL := logTwo_pos
  have hE : (0 : ℝ) < Real.exp (-(a * y)) := Real.exp_pos _
  have hF : (0 : ℝ) < Real.exp (-(a * (1 - y))) := Real.exp_pos _
  have hnum : 0 ≤ a ^ 2 * (Tang a y θ) ^ 2 - (Ty a y θ) ^ 2 := by
    unfold Tang Ty
    nlinarith [mul_nonneg (mul_nonneg (sq_nonneg a) (mul_nonneg hc hE.le))
      (mul_nonneg hs hF.le)]
  exact div_nonneg hnum (by positivity)

open LemmaB in
/-- **The supporting-line bound.**  Convexity of `ψ(·,θ)` in the tangent form
`ψ(y,θ) ≥ ψ(q,θ) + ψ_y(q,θ)(y - q)`. -/
lemma psi_supporting (a q θ : ℝ) (hT : ∀ y : ℝ, 0 < Tang a y θ)
    (hc : 0 ≤ Real.cos θ) (hs : 0 ≤ Real.sin θ) (y : ℝ) :
    psi a q θ + (Ty a q θ / (Tang a q θ * Real.log 2)) * (y - q) ≤ psi a y θ := by
  have hL := logTwo_pos
  set c : ℝ := Ty a q θ / (Tang a q θ * Real.log 2) with hcdef
  set f : ℝ → ℝ := fun x => psi a x θ - psi a q θ - c * (x - q) with hfdef
  set f1 : ℝ → ℝ := fun x => Ty a x θ / (Tang a x θ * Real.log 2) - c with hf1def
  have hlin : ∀ x : ℝ, HasDerivAt (fun z : ℝ => z - q) (1 : ℝ) x := fun x =>
    (hasDerivAt_id x).sub_const q
  have hf : ∀ x : ℝ, HasDerivAt f (f1 x) x := by
    intro x
    have h1 : HasDerivAt (fun z : ℝ => c * (z - q)) c x := HDA ((hlin x).const_mul c) (by ring)
    have h3 := hasDerivAt_psi_y a x θ (hT x)
    exact HDA ((h3.sub_const _).sub h1) (by simp [hf1def])
  have hf1 : ∀ x : ℝ, HasDerivAt f1
      ((a ^ 2 * (Tang a x θ) ^ 2 - (Ty a x θ) ^ 2) / ((Tang a x θ) ^ 2 * Real.log 2)) x := by
    intro x
    exact HDA ((hasDerivAt_psi_y2 a x θ (hT x)).sub_const c) (by ring)
  have hmono : Monotone f1 := by
    refine monotone_of_deriv_nonneg (fun x => (hf1 x).differentiableAt) ?_
    intro x
    rw [(hf1 x).deriv]
    exact psi_y2_nonneg a x θ hc hs
  have hf1q : f1 q = 0 := by simp [hf1def, hcdef]
  have hfq : f q = 0 := by simp [hfdef]
  have hgoal : 0 ≤ f y := by
    rcases lt_trichotomy y q with hlt | heq | hgt
    · obtain ⟨ξ, hξ, heq2⟩ := exists_hasDerivAt_eq_slope f f1 hlt
        (fun s _ => (hf s).continuousAt.continuousWithinAt) (fun s _ => hf s)
      have hξle : f1 ξ ≤ 0 := by
        have := hmono (le_of_lt hξ.2); rw [hf1q] at this; exact this
      have hden : (0 : ℝ) < q - y := by linarith
      rw [eq_comm, div_eq_iff (ne_of_gt hden)] at heq2
      rw [hfq] at heq2
      nlinarith
    · rw [heq, hfq]
    · obtain ⟨ξ, hξ, heq2⟩ := exists_hasDerivAt_eq_slope f f1 hgt
        (fun s _ => (hf s).continuousAt.continuousWithinAt) (fun s _ => hf s)
      have hξge : 0 ≤ f1 ξ := by
        have := hmono (le_of_lt hξ.1); rw [hf1q] at this; exact this
      have hden : (0 : ℝ) < y - q := by linarith
      rw [eq_comm, div_eq_iff (ne_of_gt hden)] at heq2
      rw [hfq] at heq2
      nlinarith
  simp only [hfdef] at hgoal
  linarith

open LemmaB in
/-- **Supercritical sharpness, step (i): Jensen removes `r`.**  The Bernstein operator is an
expectation over `J/r` with mean `q`, and `ψ(·,θ)` is convex, so
`B_r[ψ(·,θ)](q) ≥ ψ(q,θ)` for every `r ≥ 1`. -/
lemma bern_psi_ge (r : ℕ) (hr : 1 ≤ r) (a θ q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hT : ∀ y : ℝ, 0 < Tang a y θ) (hc : 0 ≤ Real.cos θ) (hs : 0 ≤ Real.sin θ) :
    psi a q θ ≤ bern r (fun j => psi a ((j : ℝ) / r) θ) q := by
  set c : ℝ := Ty a q θ / (Tang a q θ * Real.log 2) with hcdef
  have hle := bern_mono r
    (fun j => psi a q θ + c * ((j : ℝ) / r - q) + 0 * ((j : ℝ) / r - q) ^ 2)
    (fun j => psi a ((j : ℝ) / r) θ) q hq0 hq1
    (fun j => by
      have := psi_supporting a q θ hT hc hs ((j : ℝ) / r)
      linarith)
  rw [bern_quad r (psi a q θ) c 0 q (fun j => (j : ℝ) / r - q), bern_centered r hr] at hle
  linarith

/-! ## §3 Step (ii): the competitor and the value `F_a(q)/2` -/

open LemmaB in
/-- **Supercritical sharpness, steps (i)+(ii).**  For every `r ≥ 1` and `q ∈ [0,1]` there is a
`v ∈ [0,1]` — the polar-optimal `v_q = e^{-2a(1-q)}/(e^{-2aq}+e^{-2a(1-q)})` —
with `G_r(q,v) ≥ F_a(q)/2`, *uniformly in `r`*. -/
theorem Gfun_ge_Ffun_half (r : ℕ) (hr : 1 ≤ r) (lam q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1) :
    ∃ v ∈ Set.Icc (0 : ℝ) 1, Ffun (lam * Real.log 2) q / 2 ≤ Gfun r lam q v := by
  have hL := logTwo_pos
  set a : ℝ := lam * Real.log 2 with hadef
  set A : ℝ := Real.exp (-(a * q)) with hA
  set B : ℝ := Real.exp (-(a * (1 - q))) with hB
  have hApos : (0 : ℝ) < A := Real.exp_pos _
  have hBpos : (0 : ℝ) < B := Real.exp_pos _
  set θ : ℝ := Real.arctan (B / A) with hθ
  have hθ0 : 0 < θ := Real.arctan_pos.2 (by positivity)
  have hθ1 : θ < Real.pi / 2 := Real.arctan_lt_pi_div_two _
  have hcpos : 0 < Real.cos θ := Real.cos_pos_of_mem_Ioo ⟨by linarith [Real.pi_pos], hθ1⟩
  have hspos : 0 < Real.sin θ :=
    Real.sin_pos_of_pos_of_lt_pi hθ0 (by linarith [Real.pi_pos])
  refine ⟨Real.sin θ ^ 2, ⟨by positivity, ?_⟩, ?_⟩
  · nlinarith [Real.neg_one_le_sin θ, Real.sin_le_one θ]
  have hTpos : ∀ y : ℝ, 0 < Tang a y θ := fun y => Tang_pos hcpos hspos
  have hjensen := bern_psi_ge r hr a θ q hq0 hq1 hTpos hcpos.le hspos.le
  have hGθ := Gfun_theta r lam q θ (by omega) hcpos.le hspos.le
  have hbern : Gfun r lam q (Real.sin θ ^ 2)
      = binaryEntropy q / 2 + bern r (fun j => psi a ((j : ℝ) / r) θ) q := by
    rw [hGθ]; rfl
  have hpolar := Tang_eq_polar a q θ
  rw [← hA, ← hB, hθ, sub_self, Real.cos_zero, mul_one] at hpolar
  have hR2 : (0 : ℝ) < A ^ 2 + B ^ 2 := by positivity
  have hpsi : psi a q θ = logTwo (A ^ 2 + B ^ 2) / 2 := by
    unfold psi logTwo
    rw [hpolar, Real.log_sqrt hR2.le]
    ring
  have e1 : Real.exp (-(a * q)) ^ 2 = Real.exp (-(2 * a * q)) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have e2 : Real.exp (-(a * (1 - q))) ^ 2 = Real.exp (-(2 * a * (1 - q))) := by
    rw [pow_two, ← Real.exp_add]; congr 1; ring
  have hAB : A ^ 2 + B ^ 2
      = Real.exp (-(2 * a * q)) + Real.exp (-(2 * a * (1 - q))) := by
    rw [hA, hB, e1, e2]
  have hF : Ffun a q / 2 = binaryEntropy q / 2 + psi a q θ := by
    rw [hpsi, hAB]
    unfold Ffun
    ring
  rw [hbern, hF]
  linarith

/-! ## §4 The `C`-side and the assembly -/

/-- **Supercritical sharpness, (6.10).**  For `a = λ ln 2 > 1`, `r ≥ 1` with `a ≤ r`, and any
`t` with `t² ≤ ⅛` and `16t²(2+a⁴) ≤ 2(a²-1)`,

  `width_r ≤ a²/(8 r ln 2) - δ`,  `δ = (a²-1)t²/(2 ln 2) > 0`. -/
theorem width_le_super (r : ℕ) (lam t : ℝ) (hr : 1 ≤ r)
    (ha : 1 < lam * Real.log 2) (hrge : lam * Real.log 2 ≤ (r : ℝ))
    (ht0 : 0 < t) (hts : t ^ 2 ≤ 1 / 8)
    (hcond : 16 * t ^ 2 * (2 + (lam * Real.log 2) ^ 4) ≤ 2 * ((lam * Real.log 2) ^ 2 - 1)) :
    width r lam
      ≤ lam ^ 2 * Real.log 2 / (8 * (r : ℝ))
        - ((lam * Real.log 2) ^ 2 - 1) * t ^ 2 / (2 * Real.log 2) := by
  have hL := logTwo_pos
  have hr0 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hlam0 : 0 ≤ lam := by nlinarith
  have ht : t < 1 / 2 := by nlinarith
  have hFq := Ffun_ge_center_super (lam * Real.log 2) t ha ht0 hts hcond
  have hFhalf : Ffun (lam * Real.log 2) (1 / 2) = 2 - lam := by
    unfold Ffun binaryEntropy logTwo
    have h1 : Real.binEntropy (1 / 2 : ℝ) = Real.log 2 := by
      rw [show (1 / 2 : ℝ) = 2⁻¹ by norm_num]
      exact Real.binEntropy_two_inv
    have h2 : Real.exp (-(2 * (lam * Real.log 2) * (1 / 2)))
          + Real.exp (-(2 * (lam * Real.log 2) * (1 - 1 / 2)))
        = 2 * Real.exp (-(lam * Real.log 2)) := by
      rw [show -(2 * (lam * Real.log 2) * (1 / 2 : ℝ)) = -(lam * Real.log 2) by ring,
        show -(2 * (lam * Real.log 2) * (1 - 1 / 2 : ℝ)) = -(lam * Real.log 2) by ring]
      ring
    rw [h1, h2, Real.log_mul (by norm_num) (Real.exp_ne_zero _), Real.log_exp]
    field_simp
    ring
  obtain ⟨v, hv, hGv⟩ := Gfun_ge_Ffun_half r hr lam (1 / 2 + t)
    (by linarith) (by linarith)
  have hsup : Ffun (lam * Real.log 2) (1 / 2 + t) / 2 ≤ supG r lam :=
    le_trans hGv (le_csSup (bddAbove_image2_Gfun r lam hr)
      (Set.mem_image2_of_mem ⟨by linarith, by linarith⟩ hv))
  have hAside : 1 - lam / 2 + ((lam * Real.log 2) ^ 2 - 1) * t ^ 2 / (2 * Real.log 2)
      ≤ supG r lam := by
    have hhalf : Ffun (lam * Real.log 2) (1 / 2) / 2
          + ((lam * Real.log 2) ^ 2 - 1) * t ^ 2 / (2 * Real.log 2)
        ≤ Ffun (lam * Real.log 2) (1 / 2 + t) / 2 := by
      have : ((lam * Real.log 2) ^ 2 - 1) * t ^ 2 / (2 * Real.log 2)
          = (((lam * Real.log 2) ^ 2 - 1) * t ^ 2 / Real.log 2) / 2 := by
        rw [div_div]; ring_nf
      rw [this]
      linarith
    rw [hFhalf] at hhalf
    linarith
  have hC := DegeneracyLedger.le_r_mul_one_sub_Cside r lam hr hlam0 hrge
  have hCside : lam ^ 2 * Real.log 2 / (8 * (r : ℝ)) ≤ 1 - Cside r (tauOf r lam) := by
    rw [div_le_iff₀ (by positivity : (0:ℝ) < 8 * (r : ℝ))]
    linarith [hC]
  have htau : lam * tauOf r lam = lam / 2 - lam ^ 2 * Real.log 2 / (4 * (r : ℝ)) := by
    unfold tauOf
    field_simp
  unfold width Aside
  rw [htau]
  have hrne : ((r : ℝ)) ≠ 0 := ne_of_gt hrpos
  have hquarter : lam ^ 2 * Real.log 2 / (4 * (r : ℝ))
      = 2 * (lam ^ 2 * Real.log 2 / (8 * (r : ℝ))) := by
    field_simp
    ring
  linarith [hCside, hAside, hquarter]

/-! ## §5 The explicit witness and `W(λ) = -∞` -/

/-- The paper's explicit competitor offset
`t(a) = √(min(⅛, (a²-1)/(8(2+a⁴))))` (a deliberately crude witness). -/
def tOf (a : ℝ) : ℝ := Real.sqrt (min (1 / 8) ((a ^ 2 - 1) / (8 * (2 + a ^ 4))))

/-- The explicit deficit `δ(a) = (a²-1)t(a)²/(2 ln 2)`. -/
def deltaOf (a : ℝ) : ℝ := (a ^ 2 - 1) * tOf a ^ 2 / (2 * Real.log 2)

lemma tOf_sq {a : ℝ} (ha : 1 < a) :
    tOf a ^ 2 = min (1 / 8) ((a ^ 2 - 1) / (8 * (2 + a ^ 4))) := by
  have h1 : (0 : ℝ) < a ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℝ) < 8 * (2 + a ^ 4) := by positivity
  have hpos : (0 : ℝ) < min (1 / 8) ((a ^ 2 - 1) / (8 * (2 + a ^ 4))) :=
    lt_min (by norm_num) (by positivity)
  exact Real.sq_sqrt hpos.le

lemma tOf_pos {a : ℝ} (ha : 1 < a) : 0 < tOf a := by
  have h1 : (0 : ℝ) < a ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℝ) < 8 * (2 + a ^ 4) := by positivity
  exact Real.sqrt_pos.2 (lt_min (by norm_num) (by positivity))

lemma deltaOf_pos {a : ℝ} (ha : 1 < a) : 0 < deltaOf a := by
  have hL := logTwo_pos
  have h1 : (0 : ℝ) < a ^ 2 - 1 := by nlinarith
  have h2 : (0 : ℝ) < tOf a ^ 2 := by
    have := tOf_pos ha; positivity
  unfold deltaOf
  positivity

/-- **Supercritical sharpness, (6.10), explicit.**  For `λ > 1/ln 2` and every `r ≥ 1`
with `λ ln 2 ≤ r`,

  `width_r ≤ λ² ln2/(8r) - δ(λ ln 2)`,  `δ(λ ln 2) > 0`. -/
theorem width_le_super' (r : ℕ) (lam : ℝ) (hr : 1 ≤ r)
    (ha : 1 < lam * Real.log 2) (hrge : lam * Real.log 2 ≤ (r : ℝ)) :
    width r lam ≤ lam ^ 2 * Real.log 2 / (8 * (r : ℝ)) - deltaOf (lam * Real.log 2) := by
  have hsq := tOf_sq ha
  have hts : tOf (lam * Real.log 2) ^ 2 ≤ 1 / 8 := by rw [hsq]; exact min_le_left _ _
  have hcond : 16 * tOf (lam * Real.log 2) ^ 2 * (2 + (lam * Real.log 2) ^ 4)
      ≤ 2 * ((lam * Real.log 2) ^ 2 - 1) := by
    have h2 : tOf (lam * Real.log 2) ^ 2
        ≤ ((lam * Real.log 2) ^ 2 - 1) / (8 * (2 + (lam * Real.log 2) ^ 4)) := by
      rw [hsq]; exact min_le_right _ _
    have hden : (0 : ℝ) < 8 * (2 + (lam * Real.log 2) ^ 4) := by positivity
    rw [le_div_iff₀ hden] at h2
    nlinarith [h2]
  have h := width_le_super r lam (tOf (lam * Real.log 2)) hr ha hrge
    (tOf_pos ha) hts hcond
  unfold deltaOf
  linarith

/-- **Supercritical sharpness, the consequence.**  For `λ > 1/ln 2`,

  `r² · width_r ⟶ -∞`,   i.e.  `W(λ) = -∞`.

The center loses by the *constant* `δ(a) > 0`, so the window closes at rate
`-δ r²` rather than opening at rate `W(λ)/r²`. -/
theorem rsq_width_tendsto_atBot (lam : ℝ) (ha : 1 < lam * Real.log 2) :
    Tendsto (fun r : ℕ => (r : ℝ) ^ 2 * width r lam) atTop atBot := by
  have hL := logTwo_pos
  set δ : ℝ := deltaOf (lam * Real.log 2) with hδ
  have hδ0 : 0 < δ := deltaOf_pos ha
  have hlam0 : 0 < lam := by nlinarith
  have hcomp : Tendsto (fun r : ℕ => -((δ / 2) * (r : ℝ) ^ 2)) atTop atBot := by
    have hnat : Tendsto (fun r : ℕ => ((r : ℝ))) atTop atTop := tendsto_natCast_atTop_atTop
    have h : Tendsto (fun r : ℕ => ((r : ℝ)) ^ 2) atTop atTop :=
      (tendsto_pow_atTop (two_ne_zero)).comp hnat
    exact tendsto_neg_atTop_atBot.comp
      (Filter.Tendsto.const_mul_atTop (show (0:ℝ) < δ / 2 by linarith) h)
  refine tendsto_atBot_mono' _ ?_ hcomp
  obtain ⟨N, hN⟩ := exists_nat_ge (max (lam * Real.log 2) (lam ^ 2 * Real.log 2 / (4 * δ)))
  filter_upwards [eventually_ge_atTop (max 1 N)] with r hr
  have hrN : (N : ℝ) ≤ (r : ℝ) := by
    exact_mod_cast le_trans (le_max_right 1 N) hr
  have hr1 : 1 ≤ r := le_trans (le_max_left 1 N) hr
  have hr0 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hra : lam * Real.log 2 ≤ (r : ℝ) := le_trans (le_trans (le_max_left _ _) hN) hrN
  have hrδ : lam ^ 2 * Real.log 2 / (4 * δ) ≤ (r : ℝ) :=
    le_trans (le_trans (le_max_right _ _) hN) hrN
  have hkey := width_le_super' r lam hr1 ha hra
  have hmul : (r : ℝ) ^ 2 * width r lam
      ≤ (r : ℝ) ^ 2 * (lam ^ 2 * Real.log 2 / (8 * (r : ℝ)) - δ) :=
    mul_le_mul_of_nonneg_left hkey (by positivity)
  have hrw : (r : ℝ) ^ 2 * (lam ^ 2 * Real.log 2 / (8 * (r : ℝ)) - δ)
      = (r : ℝ) * (lam ^ 2 * Real.log 2 / 8) - δ * (r : ℝ) ^ 2 := by
    field_simp
  rw [hrw] at hmul
  have hlin : (r : ℝ) * (lam ^ 2 * Real.log 2 / 8) ≤ (δ / 2) * (r : ℝ) ^ 2 := by
    rw [div_le_iff₀ (by positivity)] at hrδ
    nlinarith [hrδ, hrpos, hδ0]
  linarith

end

end DegeneracyLawSuper
