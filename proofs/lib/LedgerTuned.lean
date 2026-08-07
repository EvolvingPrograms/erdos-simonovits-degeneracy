import CenterMaxThreshold
import Lemma44
import WindowLimit
import LedgerR

/-!
# The tuned sequence behind Theorem 1.3(b)

Machinery for Theorem 1.3(b); the headline family law itself is
`DegeneracyLawB.eight_rsq_epsMax_theta_tendsto` in `Theorem13b.lean`.

Design-notes reference (notes not shipped in this repository): §10 (Cor. 10.2, Prop. 10.3, (10.1)–(10.2), Thm 10.6(b)).

Theorem 1.3(a) (`DegeneracyLaw.width_tendsto`) fixes `λ` and lets `r → ∞`; the
resulting constant is `W(λ) = λ⁴ ln³2 / 64`, which is maximized only in the
limit `λ ↑ λ* = 1/ln 2`.  No *fixed* `λ` reaches `λ*`, because Lemma 4.2's
threshold `R(a)` blows up like `(1-a²)⁻¹` (Cor. 10.2, `DegeneracyLawQuant.Rreal`).

Theorem 1.3(b) escapes by letting `λ` drift:

  `ν_r = ln r / r`,  `λ_r = (1 - ν_r)/ln 2`,  `a_r = λ_r ln 2 = 1 - ν_r`.

Since `ν_r → 0` more slowly than `1/r`, the sequence outruns its own threshold:
`R(a_r) ≤ ⌈r/(4 ln r)⌉ ≤ r` (Prop. 10.3), so
`DegeneracyLawQuant.supG_eq_center_quant` — which `CenterMaxThreshold.lean` now proves
unconditionally given `r ≥ R_of λ` — applies at every member of the sequence.

## What is proved here

| Item | Lean name | Status |
|---|---|---|
| the schedule and its algebra | `nuR`, `lamR`, `aR_eq`, `nuR_pos`, `nuR_lt_one`, `aR_mem` | ✅ |
| the strip lower bound `ρ(a) ≥ (9/10)√(u/2)` for `u ≤ 1/2` | `rho_ge_sqrt` | ✅ |
| Cor. 10.2's rate: `Rreal a ≤ 1/(4u)` for `u ≤ 1/2` | `Rreal_le_of_u_small` | ✅ |
| `ν_r ≤ 2/7` and `u_r ≤ 1/2` for `r ≥ 7` | `nuR_le`, `uR_le_half` | ✅ |
| **Prop. 10.3, admissibility** | `R_of_lamR_le` | ✅ |
| **Lemma 4.2 along the tuned sequence** | `supG_eq_center_tuned` | ✅ |
| `ν_r → 0`, `λ_r → λ*`, `W(λ_r) → 1/(64 ln2)` | `tendsto_nuR`, `tendsto_lamR`, `tendsto_Wconst_lamR` | ✅ |
| **(10.2), the window limit** | `width_tuned_tendsto` | ✅ |
| **Thm 10.6(b), `16 r² ε^max_r → 1`** | `sixteen_rsq_epsMax_tendsto` | ✅ (§10.4(c) is an explicit hypothesis) |

**This file is `sorry`-free.**  `rho_ge_sqrt` — the paper's "`ρ(a)/√(u/2)` is
decreasing in `u`" — is proved here without any monotonicity argument, by the
sharper route `κ = √((1-u)/(1+u)) ≤ 1 - (100/121)u ≤ cos((20/11)√(u/2))`, using
`Real.one_sub_sq_div_two_le_cos` and antitonicity of `arccos`; the constant
`20/11 = 1.8181…` is exactly the one for which `0.99 · (20/11)/2 = 9/10`, so the
final step is an equality.  The `1/4` in `Rreal_le_of_u_small` is deliberately
slack (the sharp constant is `0.2406`); `1/4` is all Prop. 10.3 needs, since
`ln r ≥ ln 7 > 1/4`.

`sixteen_rsq_epsMax_tendsto` takes §10.4(c) — `r(1-β_r) → 1/(8 ln 2)`, the
`c* = 1/4` limit of `r(1-C_r) → 2(c*)²/ln 2` — as an explicit hypothesis rather
than a `sorry`, so the file is honest about what it assumes.
-/

namespace DegeneracyLawB

open Filter Topology DegeneracyLaw DegeneracyLawQuant TwoDegenerateGraphs

noncomputable section

lemma logTwoPos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-! ## §10.2 The tuned sequence -/

/-- The drift rate `ν_r = ln r / r`. -/
def nuR (r : ℕ) : ℝ := Real.log r / r

/-- The tuned Gibbs exponent `λ_r = λ*(1 - ν_r) = (1 - ν_r)/ln 2`. -/
def lamR (r : ℕ) : ℝ := (1 - nuR r) / Real.log 2

/-- `a_r = λ_r ln 2 = 1 - ν_r`. -/
lemma aR_eq (r : ℕ) : lamR r * Real.log 2 = 1 - nuR r := by
  unfold lamR; field_simp

lemma nuR_pos {r : ℕ} (hr : 2 ≤ r) : 0 < nuR r := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  exact div_pos (Real.log_pos (by linarith)) (by linarith)

/-- `ν_r < 1` for `r ≥ 2`: `ln r < r`. -/
lemma nuR_lt_one {r : ℕ} (hr : 2 ≤ r) : nuR r < 1 := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hne : (r : ℝ) ≠ 1 := by intro h; rw [h] at hr0; norm_num at hr0
  have hlt : Real.log (r : ℝ) < (r : ℝ) := by
    have := Real.log_lt_sub_one_of_pos (x := (r : ℝ)) hrpos hne
    linarith
  exact (div_lt_one hrpos).2 hlt

/-- Subcriticality of the schedule: `0 < a_r < 1` for every `r ≥ 2`. -/
lemma aR_mem {r : ℕ} (hr : 2 ≤ r) :
    0 < lamR r * Real.log 2 ∧ lamR r * Real.log 2 < 1 := by
  rw [aR_eq]
  exact ⟨by linarith [nuR_lt_one hr], by linarith [nuR_pos hr]⟩

lemma lamR_pos {r : ℕ} (hr : 2 ≤ r) : 0 < lamR r := by
  have h := (aR_mem hr).1
  nlinarith [logTwoPos]

/-! ## §10.1–10.2 The rate of `R(a)` -/

/-- **The strip lower bound of Prop. 10.3.**  For `0 < a < 1` with `u = 1-a² ≤ ½`,

  `ρ(a) ≥ (9/10)·√(u/2)`.

The paper argues that `ρ(a)/√(u/2)` is decreasing in `u`, with value
`0.99 × 0.9553 = 0.9458 > 0.9` at `u = ½`.  The proof here avoids the
monotonicity entirely: with `κ = √(a²/(2-a²)) = √((1-u)/(1+u))` and
`x = (20/11)√(u/2)`,

  `κ ≤ 1 - (100/121)u = 1 - x²/2 ≤ cos x`,

the middle step being `(1-u) ≤ (1-(100/121)u)²(1+u)` on `0 < u ≤ ½` (a cubic
with a comfortable margin, `0.033` at `u = ½`).  Antitonicity of `arccos` then
gives `arccos κ ≥ x`, and `0.99 · (20/11)/2 = 9/10` exactly, so the last step is
an equality — `20/11` is the largest constant this route delivers. -/
theorem rho_ge_sqrt {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) (hu : 1 - a ^ 2 ≤ 1 / 2) :
    (9 / 10) * Real.sqrt ((1 - a ^ 2) / 2) ≤ rho a := by
  have hu0 : (0 : ℝ) < 1 - a ^ 2 := by nlinarith
  set u : ℝ := 1 - a ^ 2 with hudef
  -- `S = √(u/2)`, `x = (20/11)S`; it suffices that `arccos κ ≥ x`
  set S : ℝ := Real.sqrt (u / 2) with hSdef
  have hS0 : 0 < S := Real.sqrt_pos.2 (by linarith)
  have hS2 : S ^ 2 = u / 2 := Real.sq_sqrt (by linarith)
  have hSle : S ≤ 1 / 2 := by nlinarith [hS0, hS2]
  set x : ℝ := (20 / 11) * S with hxdef
  have hx0 : 0 ≤ x := by positivity
  have hxpi : x ≤ Real.pi := by
    have := Real.pi_gt_three
    have : x ≤ 20 / 22 := by rw [hxdef]; nlinarith [hSle, hS0]
    linarith [Real.pi_gt_three]
  -- `cos x ≥ 1 - x²/2 = 1 - (100/121)u`
  have hcosx : 1 - (100 / 121) * u ≤ Real.cos x := by
    have h := Real.one_sub_sq_div_two_le_cos (x := x)
    have hxx : x ^ 2 / 2 = (100 / 121) * u := by
      rw [hxdef]; field_simp; nlinarith [hS2]
    linarith [h, hxx.le, hxx.ge]
  -- `κ = √(a²/(2-a²)) ≤ 1 - (100/121)u`
  have hknn : (0 : ℝ) ≤ 1 - (100 / 121) * u := by nlinarith
  have hkappa : Real.sqrt (a ^ 2 / (2 - a ^ 2)) ≤ 1 - (100 / 121) * u := by
    rw [show (1 : ℝ) - (100 / 121) * u = Real.sqrt ((1 - (100 / 121) * u) ^ 2) by
      rw [Real.sqrt_sq hknn]]
    apply Real.sqrt_le_sqrt
    rw [div_le_iff₀ (by nlinarith : (0 : ℝ) < 2 - a ^ 2)]
    -- `1 - u ≤ (1 - (100/121)u)²(1 + u)`, since `2 - a² = 1 + u` and `a² = 1 - u`
    have h2a : 2 - a ^ 2 = 1 + u := by rw [hudef]; ring
    have ha2 : a ^ 2 = 1 - u := by rw [hudef]; ring
    rw [h2a, ha2]
    nlinarith [hu0, hu, sq_nonneg (u - 1 / 2), mul_nonneg hu0.le (sq_nonneg (u - 1/2))]
  -- so `arccos κ ≥ arccos (cos x) = x`
  have harc : x ≤ Real.arccos (Real.sqrt (a ^ 2 / (2 - a ^ 2))) := by
    have h1 : Real.arccos (Real.cos x) ≤ Real.arccos (Real.sqrt (a ^ 2 / (2 - a ^ 2))) :=
      Real.arccos_le_arccos (le_trans hkappa hcosx)
    rwa [Real.arccos_cos hx0 hxpi] at h1
  unfold rho rhoCrit
  rw [hxdef] at harc
  linarith

/-- `√(x/2) ≥ (7067/10000)·√x`. -/
lemma sqrt_half_ge {x : ℝ} (hx : 0 ≤ x) :
    (7067 / 10000 : ℝ) * Real.sqrt x ≤ Real.sqrt (x / 2) := by
  have h2 : Real.sqrt (x / 2) * Real.sqrt 2 = Real.sqrt x := by
    rw [← Real.sqrt_mul (by positivity)]
    congr 1
    field_simp
  have hs2 : Real.sqrt 2 ≤ 1415 / 1000 := by
    rw [show (1415 : ℝ) / 1000 = Real.sqrt ((1415 / 1000) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by norm_num)
  have hs2p : (0 : ℝ) < Real.sqrt 2 := Real.sqrt_pos.2 (by norm_num)
  have hnn : (0 : ℝ) ≤ Real.sqrt (x / 2) := Real.sqrt_nonneg _
  have h3 : Real.sqrt x ≤ Real.sqrt (x / 2) * (1415 / 1000) := by
    rw [← h2]
    exact mul_le_mul_of_nonneg_left hs2 hnn
  linarith

/-- **Cor. 10.2's rate.**  For `0 < a < 1` with `u = 1-a² ≤ ½`,
`Rreal a ≤ 1/(4u)`.  (The sharp constant is `0.2406`; `1/4` is slack but is all
Prop. 10.3 needs.) -/
theorem Rreal_le_of_u_small {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hu : 1 - a ^ 2 ≤ 1 / 2) :
    Rreal a ≤ (1 / 4) / (1 - a ^ 2) := by
  have hu0 : (0 : ℝ) < 1 - a ^ 2 := by nlinarith
  set S : ℝ := Real.sqrt (1 - a ^ 2) with hS
  have hS0 : 0 < S := Real.sqrt_pos.2 hu0
  have hS2 : S ^ 2 = 1 - a ^ 2 := Real.sq_sqrt hu0.le
  have hrho0 : 0 < rho a := rho_pos ha0 ha1
  -- `ρ ≥ 0.9·√(u/2) ≥ 0.9·0.7071·S = 0.63639·S`
  have hrho : (63603 / 100000 : ℝ) * S ≤ rho a := by
    have h1 := rho_ge_sqrt ha0 ha1 hu
    have h2 := sqrt_half_ge (x := 1 - a ^ 2) hu0.le
    rw [← hS] at h2
    linarith
  -- `√(a²+2u) = √(1+u) ≤ 1.2248`
  have hsum : a ^ 2 + 2 * uOf a = 1 + (1 - a ^ 2) := by unfold uOf; ring
  have hss : Real.sqrt (a ^ 2 + 2 * uOf a) ≤ 12248 / 10000 := by
    rw [hsum, show (12248 : ℝ) / 10000 = Real.sqrt ((12248 / 10000) ^ 2) by
      rw [Real.sqrt_sq (by norm_num)]]
    exact Real.sqrt_le_sqrt (by nlinarith)
  have hssnn : (0 : ℝ) ≤ Real.sqrt (a ^ 2 + 2 * uOf a) := Real.sqrt_nonneg _
  have hsu : Real.sqrt (uOf a) = S := by unfold uOf; rw [hS]
  unfold Rreal
  rw [hsu]
  rw [div_le_div_iff₀ (by positivity) hu0]
  -- goal: `a²·√(1+u)·u ≤ (1/4)·(8 ρ S)`
  have ha2 : a ^ 2 ≤ 1 := by nlinarith
  have hkey : a ^ 2 * Real.sqrt (a ^ 2 + 2 * uOf a) ≤ (12248 / 10000 : ℝ) :=
    calc a ^ 2 * Real.sqrt (a ^ 2 + 2 * uOf a)
        ≤ 1 * Real.sqrt (a ^ 2 + 2 * uOf a) := mul_le_mul_of_nonneg_right ha2 hssnn
      _ = Real.sqrt (a ^ 2 + 2 * uOf a) := one_mul _
      _ ≤ _ := hss
  have hlhs : a ^ 2 * Real.sqrt (a ^ 2 + 2 * uOf a) * (1 - a ^ 2)
      ≤ (12248 / 10000 : ℝ) * S ^ 2 := by
    rw [← hS2]
    nlinarith [hkey, sq_nonneg S]
  have hrhs : (12248 / 10000 : ℝ) * S ^ 2 ≤ 1 / 4 * (8 * rho a * S) := by
    nlinarith [hrho, hS0]
  linarith

/-! ## §10.2 Prop. 10.3: admissibility of the tuned sequence -/

lemma exp_one_le_seven : Real.exp 1 ≤ 7 := by
  have := Real.exp_one_lt_d9
  linarith

/-- `ln 7 < 2`. -/
lemma log_seven_lt_two : Real.log 7 < 2 := by
  have h : (7 : ℝ) < Real.exp 2 := by
    have h1 : (2.7182818283 : ℝ) < Real.exp 1 := Real.exp_one_gt_d9
    have h2 : Real.exp 2 = Real.exp 1 ^ 2 := by
      rw [← Real.exp_nat_mul]; norm_num
    rw [h2]; nlinarith
  exact (Real.log_lt_iff_lt_exp (by norm_num)).2 h

/-- `ν_r ≤ 2/7` for `r ≥ 7`, by antitonicity of `log x / x` on `[e, ∞)`. -/
lemma nuR_le {r : ℕ} (hr : 7 ≤ r) : nuR r ≤ 2 / 7 := by
  have hr7 : (7 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hmem7 : (7 : ℝ) ∈ Set.Ici (Real.exp 1) := exp_one_le_seven
  have hmemr : ((r : ℝ)) ∈ Set.Ici (Real.exp 1) := le_trans exp_one_le_seven hr7
  have h := Real.log_div_self_antitoneOn hmem7 hmemr hr7
  have h7 : Real.log 7 / 7 ≤ 2 / 7 := by
    have := log_seven_lt_two; linarith
  exact le_trans h h7

/-- `u_r = 1 - a_r² ≤ ½` for `r ≥ 7`. -/
lemma uR_le_half {r : ℕ} (hr : 7 ≤ r) :
    1 - (lamR r * Real.log 2) ^ 2 ≤ 1 / 2 := by
  have hn := nuR_le hr
  have hp := nuR_pos (by omega : 2 ≤ r)
  rw [aR_eq]
  nlinarith

/-- `u_r ≥ ν_r`. -/
lemma uR_ge_nuR {r : ℕ} (hr : 2 ≤ r) :
    nuR r ≤ 1 - (lamR r * Real.log 2) ^ 2 := by
  have hp := nuR_pos hr
  have hl := nuR_lt_one hr
  rw [aR_eq]; nlinarith

/-- **Prop. 10.3.**  `R_of λ_r ≤ r` for every `r ≥ 7`: the tuned sequence
outruns Lemma 4.2's own threshold. -/
theorem R_of_lamR_le {r : ℕ} (hr : 7 ≤ r) : R_of (lamR r) ≤ r := by
  have hr2 : 2 ≤ r := by omega
  have hr7 : (7 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  obtain ⟨ha0, ha1⟩ := aR_mem hr2
  have hu0 : (0 : ℝ) < 1 - (lamR r * Real.log 2) ^ 2 := by nlinarith
  have hRr := Rreal_le_of_u_small ha0 ha1 (uR_le_half hr)
  -- `Rreal ≤ 1/(4u) ≤ 1/(4ν_r) = r/(4 ln r) ≤ r`
  have hnu := uR_ge_nuR hr2
  have hnup := nuR_pos hr2
  have h1 : (1 / 4 : ℝ) / (1 - (lamR r * Real.log 2) ^ 2) ≤ (1 / 4) / nuR r :=
    div_le_div_of_nonneg_left (by norm_num) hnup hnu
  have hlogr : (1 / 4 : ℝ) ≤ Real.log (r : ℝ) := by
    have : Real.log 2 ≤ Real.log (r : ℝ) :=
      Real.log_le_log (by norm_num) (by linarith)
    have h2 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
    linarith
  have h2 : (1 / 4 : ℝ) / nuR r ≤ (r : ℝ) := by
    unfold nuR
    rw [div_div_eq_mul_div, div_le_iff₀ (by positivity)]
    nlinarith [hlogr, hr7]
  have hfin : Rreal (lamR r * Real.log 2) ≤ (r : ℝ) := by linarith
  unfold R_of
  refine max_le (by omega) ?_
  exact Nat.ceil_le.2 hfin

/-- **Lemma 4.2 along the tuned sequence** — the point of `CenterMaxThreshold`.
For every `r ≥ 7`, `sup_{[0,1]²} G_r(λ_r,·,·) = G_r(λ_r,½,½)`, with no unproved
finite checks and no fixed-`λ` restriction. -/
theorem supG_eq_center_tuned {r : ℕ} (hr : 7 ≤ r) :
    supG r (lamR r) = Gfun r (lamR r) (1 / 2) (1 / 2) :=
  supG_eq_center_quant r (lamR r) (aR_mem (by omega)).1 (aR_mem (by omega)).2
    (R_of_lamR_le hr)

/-! ## §10.3 The window along the drifting `λ` -/

lemma tendsto_nuR : Tendsto nuR atTop (𝓝 0) := by
  have h : Tendsto (fun x : ℝ => Real.log x / x) atTop (𝓝 0) :=
    Real.isLittleO_log_id_atTop.tendsto_div_nhds_zero
  exact h.comp tendsto_natCast_atTop_atTop

lemma tendsto_aR : Tendsto (fun r : ℕ => lamR r * Real.log 2) atTop (𝓝 1) := by
  have h : Tendsto (fun r : ℕ => 1 - nuR r) atTop (𝓝 ((1 : ℝ) - 0)) :=
    tendsto_const_nhds.sub tendsto_nuR
  simpa [aR_eq] using h

lemma tendsto_lamR : Tendsto lamR atTop (𝓝 (1 / Real.log 2)) := by
  have h : Tendsto (fun r : ℕ => (1 - nuR r) / Real.log 2) atTop
      (𝓝 ((1 - 0) / Real.log 2)) :=
    (tendsto_const_nhds.sub tendsto_nuR).div_const _
  show Tendsto (fun r : ℕ => lamR r) atTop (𝓝 (1 / Real.log 2))
  simpa [lamR] using h

lemma tendsto_Wconst_lamR :
    Tendsto (fun r : ℕ => Wconst (lamR r)) atTop (𝓝 (1 / (64 * Real.log 2))) := by
  have hL := logTwoPos
  have h : Tendsto (fun r : ℕ => lamR r ^ 4 * Real.log 2 ^ 3 / 64) atTop
      (𝓝 ((1 / Real.log 2) ^ 4 * Real.log 2 ^ 3 / 64)) :=
    ((tendsto_lamR.pow 4).mul_const _).div_const _
  have hval : (1 / Real.log 2) ^ 4 * Real.log 2 ^ 3 / 64 = 1 / (64 * Real.log 2) := by
    field_simp
  rw [← hval]
  simpa [Wconst] using h

/-- The Lemma 4.4 lower bound at the drifting `λ`, i.e. paper (10.1). -/
theorem lowerSeq_le_tuned {r : ℕ} (hr : 7 ≤ r) :
    lowerSeq (lamR r) r ≤ (r : ℝ) ^ 2 * width r (lamR r) := by
  have hr2 : 2 ≤ r := by omega
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have : (7 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hlog := logTwoPos
  obtain ⟨ha0, ha1⟩ := aR_mem hr2
  have h := LemmaC.width_ge r (lamR r) hr2 (lamR_pos hr2) ha1 (supG_eq_center_tuned hr)
  have hsq : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  have h' := mul_le_mul_of_nonneg_left h hsq.le
  refine le_trans (le_of_eq ?_) h'
  have hden : (0 : ℝ) < 1 - (lamR r * Real.log 2) ^ 2 / 4 := by nlinarith
  rw [lowerSeq]
  field_simp
  try ring

/-- **(10.2).**  Along the tuned sequence the rescaled window converges to the
*maximal* value `W(λ*) = 1/(64 ln 2) = 0.02254211…`, which no fixed `λ` attains
(for fixed `λ` the limit is `W(λ) < W(λ*)`). -/
theorem width_tuned_tendsto :
    Tendsto (fun r : ℕ => (r : ℝ) ^ 2 * width r (lamR r)) atTop
      (𝓝 (1 / (64 * Real.log 2))) := by
  have hL := logTwoPos
  have hden : (0 : ℝ) < 1920 * Real.log 2 * (1 - (1 : ℝ) ^ 2 / 4) := by positivity
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le'
    (g := fun r : ℕ => lowerSeq (lamR r) r) (h := fun r : ℕ => upperSeq (lamR r) r)
    ?_ ?_ ?_ ?_
  · have hc : Tendsto (fun r : ℕ => 1 + (lamR r * Real.log 2) ^ 2 / 3) atTop
        (𝓝 (1 + (1 : ℝ) ^ 2 / 3)) :=
      (tendsto_const_nhds (x := (1:ℝ))).add ((tendsto_aR.pow 2).div_const 3)
    have hK : Tendsto (fun r : ℕ => (lamR r * Real.log 2) ^ 6 /
        (1920 * Real.log 2 * (1 - (lamR r * Real.log 2) ^ 2 / 4))) atTop
        (𝓝 ((1 : ℝ) ^ 6 / (1920 * Real.log 2 * (1 - (1 : ℝ) ^ 2 / 4)))) :=
      (tendsto_aR.pow 6).div ((tendsto_const_nhds (x := 1920 * Real.log 2)).mul
        ((tendsto_const_nhds (x := (1:ℝ))).sub ((tendsto_aR.pow 2).div_const 4)))
        (ne_of_gt hden)
    have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h1 : Tendsto (fun r : ℕ => Wconst (lamR r) *
        (1 - (1 + (lamR r * Real.log 2) ^ 2 / 3) * (1 / (r : ℝ)))) atTop
        (𝓝 (1 / (64 * Real.log 2) * (1 - (1 + (1 : ℝ) ^ 2 / 3) * 0))) :=
      tendsto_Wconst_lamR.mul (hone.sub (hc.mul tendsto_inv_nat))
    have h2 : Tendsto (fun r : ℕ => ((lamR r * Real.log 2) ^ 6 /
        (1920 * Real.log 2 * (1 - (lamR r * Real.log 2) ^ 2 / 4))) * (1 / (r : ℝ)) ^ 3)
        atTop (𝓝 (((1 : ℝ) ^ 6 / (1920 * Real.log 2 * (1 - (1 : ℝ) ^ 2 / 4))) * 0 ^ 3)) :=
      hK.mul (tendsto_inv_nat.pow 3)
    have h := h1.sub h2
    norm_num at h
    simpa [lowerSeq] using h
  · have hone : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1) := tendsto_const_nhds
    have h : Tendsto (fun r : ℕ => Wconst (lamR r) * (1 - 1 / (r : ℝ))) atTop
        (𝓝 (1 / (64 * Real.log 2) * (1 - 0))) :=
      tendsto_Wconst_lamR.mul (hone.sub tendsto_inv_nat)
    norm_num at h
    simpa [upperSeq] using h
  · filter_upwards [eventually_ge_atTop 7] with r hr
    exact lowerSeq_le_tuned hr
  · filter_upwards [eventually_ge_atTop 7] with r hr
    exact rsq_width_le_upperSeq (lamR r) (lamR_pos (by omega)) (aR_mem (by omega)).2
      (by omega)

/-! ## §10.6(b) The sharp constant `1/16` -/

/-- **Theorem 1.3(b) (the design notes Thm 10.6(b)), the `ε^max` form.**

Along the tuned sequence, at the midpoint `β_r` of §8.1,

  `16 r² ε^max_r → 1`.

The two inputs are (10.2) — `r² width_r → W(λ*) = 1/(64 ln 2)`, proved above as
`width_tuned_tendsto` — and §10.4(c), `r(1 - β_r) → 1/(8 ln 2)` (the `c* = ¼`
limit of `r(1 - C_r) → 2(c*)²/ln 2`), which is taken here as the hypothesis
`hbeta`.  Given both,

  `r² ε^max_r = (r²·½ width_r)/(r(1-β_r)) → (1/(128 ln2))/(1/(8 ln2)) = 1/16`,

so `16 r² ε^max_r → 1`, and Theorem 1.2's fixed slack `η_r = ½` (which would give
`½`) is replaced by `η_r = r^{-1/2} → 0` at the cost of inflating `m₀(r)` from
`Θ(r³ log r)` to `Θ(r^{7/2} log r)` — paper §10.7.1. -/
theorem sixteen_rsq_epsMax_tendsto
    (hbeta : Tendsto (fun r : ℕ => (r : ℝ) * (1 - DegeneracyLedger.betaMid r (lamR r)))
      atTop (𝓝 (1 / (8 * Real.log 2)))) :
    Tendsto (fun r : ℕ =>
      16 * (r : ℝ) ^ 2 * DegeneracyLedger.epsMaxR r (lamR r)
        (DegeneracyLedger.betaMid r (lamR r))) atTop (𝓝 1) := by
  have hL := logTwoPos
  have hne : (1 : ℝ) / (8 * Real.log 2) ≠ 0 := by positivity
  have hnum : Tendsto (fun r : ℕ => 16 * ((r : ℝ) ^ 2 * width r (lamR r) / 2)) atTop
      (𝓝 (16 * (1 / (64 * Real.log 2) / 2))) :=
    (width_tuned_tendsto.div_const 2).const_mul 16
  have hq := hnum.div hbeta hne
  have hval : 16 * (1 / (64 * Real.log 2) / 2) / (1 / (8 * Real.log 2)) = 1 := by
    field_simp
    ring
  rw [← hval]
  refine hq.congr' ?_
  filter_upwards [eventually_ge_atTop 2] with r hr
  have hr0 : (0 : ℝ) < (r : ℝ) := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  simp only [Pi.div_apply]
  unfold DegeneracyLedger.epsMaxR
  rw [DegeneracyLedger.betaMid_spec r (lamR r)]
  ring

end

end DegeneracyLawB
