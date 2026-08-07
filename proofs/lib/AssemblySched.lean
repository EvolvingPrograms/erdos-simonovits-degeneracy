import LedgerTuned
import LedgerAsym

/-!
# The schedule assembly, analytic layer (Corollary 1.4 of the paper)

The `δ`-parameterized counterparts of `AssemblyR`'s Block E constants, at the
tuned schedule `λ_r = (1 - ln r / r)/ln 2` instead of the fixed `λ = 27/20`,
with window position and ledger slack both set to `θ = η = δ/4`:

* `betaS r δ = β_{δ/4} = A_r + (δ/4) · width_r`  (`betaTheta`),
* `slackS r δ = (β − A_r)/4 = δ · width_r / 16`  (`deltaR`),
* `epsS  r δ = (1 − δ/4) · ε^max_r(β_{δ/4})`      (`epsR`).

Everything is *eventual in `r`* (the schedule needs `r ≥ r₀(δ)`), in contrast
to Block E's uniform `r ≥ 2` statements at `27/20`.

Main results, all `sorry`-free:

* `width_sched_pos` — the window is open along the schedule, eventually;
* `betaS_lt_one`, `betaS_pos`, `slackS_pos` — the parameters are admissible,
  eventually;
* `eight_rsq_epsS_tendsto` — `8 r² ε_S → (1 − δ/4)²`;
* `epsS_ge` — **the certified gain beats `(1 − δ)/(8 r²)`, eventually**: the
  analytic content of Corollary 1.4;
* `schedParams_admissible` — the conjunction, packaged for the (future)
  instantiation of the Block D pipeline along the schedule.

The Lemma-B input along the schedule is already available:
`DegeneracyLawB.supG_eq_center_tuned` (via `R_of_lamR_le`, `r ≥ 7`), and the
Gibbs bound `RAssembly.typeEntropyBound_supG_gen` is generic in `λ`.  What
this file does **not** contain is the re-instantiation of the sampling/bridge
chain (`exists_free_dense_hosts`) at these parameters; that is the remaining
step of the schedule assembly.
-/

namespace DegeneracyLawSched

open Filter Topology DegeneracyLaw DegeneracyLawB DegeneracyLedger
open TwoDegenerateGraphs

noncomputable section

lemma logTwoPos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-! ## §1 The schedule parameters -/

/-- `β_S(r, δ) = A_r + (δ/4) · width_r` at `λ = λ_r`. -/
def betaS (r : ℕ) (delta : ℝ) : ℝ := betaTheta r (lamR r) (delta / 4)

/-- The ledger slack `δ_S = (β_S − A_r)/4 = δ · width_r/16` at `λ = λ_r`. -/
def slackS (r : ℕ) (delta : ℝ) : ℝ := deltaR r (lamR r) (betaS r delta)

/-- The certified gain `ε_S = (1 − δ/4) ε^max_r(β_S)` at `λ = λ_r`. -/
def epsS (r : ℕ) (delta : ℝ) : ℝ := epsR r (lamR r) (betaS r delta) (delta / 4)

/-! ## §2 Eventual admissibility of the parameters -/

/-- The window is open along the schedule, eventually: from the window law
`r² width_r → 1/(64 ln 2) > 0`. -/
theorem width_sched_pos : ∀ᶠ r : ℕ in atTop, 0 < width r (lamR r) := by
  have hpos : (0 : ℝ) < 1 / (64 * Real.log 2) := by positivity
  have hev := width_tuned_tendsto.eventually (lt_mem_nhds hpos)
  filter_upwards [hev, eventually_ge_atTop 1] with r hr hr1
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hr1
  nlinarith [sq_nonneg (r : ℝ)]

/-- `β_S < 1` eventually: from `r(1 − β_S) → 1/(8 ln 2) > 0`. -/
theorem betaS_lt_one (delta : ℝ) :
    ∀ᶠ r : ℕ in atTop, betaS r delta < 1 := by
  have hpos : (0 : ℝ) < 1 / (8 * Real.log 2) := by positivity
  have hev := (tendsto_r_one_sub_betaTheta (delta / 4)).eventually (lt_mem_nhds hpos)
  filter_upwards [hev, eventually_ge_atTop 1] with r hr hr1
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast Nat.lt_of_lt_of_le Nat.zero_lt_one hr1
  rcases le_or_gt (1 - betaS r delta) 0 with hle | hpos
  · exfalso
    have : (r : ℝ) * (1 - betaTheta r (lamR r) (delta / 4)) ≤ 0 :=
      mul_nonpos_of_nonneg_of_nonpos hrpos.le (by simpa [betaS] using hle)
    linarith
  · linarith

/-- `0 < β_S` eventually: from `r(1 − β_S) → 1/(8 ln 2) < 1`. -/
theorem betaS_pos (delta : ℝ) :
    ∀ᶠ r : ℕ in atTop, 0 < betaS r delta := by
  have hlt : (1 : ℝ) / (8 * Real.log 2) < 1 := by
    rw [div_lt_one (by positivity)]
    have := Real.log_two_gt_d9
    nlinarith
  have hev := (tendsto_r_one_sub_betaTheta (delta / 4)).eventually (gt_mem_nhds hlt)
  filter_upwards [hev, eventually_ge_atTop 1] with r hr hr1
  have hr1' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  rcases le_or_gt (1 - betaS r delta) 0 with hneg | hpos
  · linarith
  · have hle : 1 - betaS r delta ≤ (r : ℝ) * (1 - betaS r delta) :=
      le_mul_of_one_le_left hpos.le hr1'
    have : (r : ℝ) * (1 - betaTheta r (lamR r) (delta / 4)) < 1 := hr
    simp only [betaS] at hle ⊢
    linarith

/-- The ledger slack is positive eventually. -/
theorem slackS_pos (delta : ℝ) (hd0 : 0 < delta) :
    ∀ᶠ r : ℕ in atTop, 0 < slackS r delta := by
  filter_upwards [width_sched_pos] with r hw
  have hAB : betaS r delta - Aside r (lamR r) = delta / 4 * width r (lamR r) := by
    simp only [betaS, betaTheta]; ring
  have hprod : 0 < delta / 4 * width r (lamR r) :=
    mul_pos (by linarith) hw
  simp only [slackS, deltaR]
  linarith [hAB ▸ hprod]

/-! ## §3 The family law for the certified gain -/

/-- The family law at general window position (Theorem 1.3(b); reproved here so
the analytic layer stays inside `proofs/lib/`): along the schedule,
`8 r² ε^max_r(β_θ) → 1 − θ`. -/
theorem eight_rsq_epsMax_theta_tendsto' (theta : ℝ) :
    Tendsto (fun r : ℕ =>
      8 * (r : ℝ) ^ 2 * epsMaxR r (lamR r) (betaTheta r (lamR r) theta)) atTop
      (𝓝 (1 - theta)) := by
  have hL := logTwoPos
  have hne : (1 : ℝ) / (8 * Real.log 2) ≠ 0 := by positivity
  have hnum : Tendsto (fun r : ℕ =>
      8 * ((r : ℝ) ^ 2 * width r (lamR r)) * (1 - theta)) atTop
      (𝓝 (8 * (1 / (64 * Real.log 2)) * (1 - theta))) :=
    (width_tuned_tendsto.const_mul 8).mul_const _
  have hq := hnum.div (tendsto_r_one_sub_betaTheta theta) hne
  have hval : 8 * (1 / (64 * Real.log 2)) * (1 - theta) / (1 / (8 * Real.log 2))
      = 1 - theta := by
    field_simp
    ring
  rw [← hval]
  refine hq.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with r hr
  simp only [Pi.div_apply]
  rw [epsMaxR, Cside_sub_betaTheta]
  ring

/-- `8 r² ε_S → (1 − δ/4)²` along the schedule. -/
theorem eight_rsq_epsS_tendsto (delta : ℝ) :
    Tendsto (fun r : ℕ => 8 * (r : ℝ) ^ 2 * epsS r delta) atTop
      (𝓝 ((1 - delta / 4) ^ 2)) := by
  have h := (eight_rsq_epsMax_theta_tendsto' (delta / 4)).const_mul (1 - delta / 4)
  have hlim : (1 - delta / 4) * (1 - delta / 4) = (1 - delta / 4) ^ 2 := by ring
  rw [hlim] at h
  refine h.congr fun r => ?_
  simp only [epsS, epsR, betaS]
  ring

/-- **The analytic content of Corollary 1.4**: the certified gain along the
schedule beats `(1 − δ)/(8 r²)`, eventually in `r`. -/
theorem epsS_ge (delta : ℝ) (hd0 : 0 < delta) :
    ∀ᶠ r : ℕ in atTop, (1 - delta) / (8 * (r : ℝ) ^ 2) ≤ epsS r delta := by
  have hgap : (1 - delta : ℝ) < (1 - delta / 4) ^ 2 := by nlinarith
  have hev := (eight_rsq_epsS_tendsto delta).eventually (lt_mem_nhds hgap)
  filter_upwards [hev, eventually_ge_atTop 1] with r h8 hr1
  have hr1' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have h8pos : (0 : ℝ) < 8 * (r : ℝ) ^ 2 := by positivity
  rw [div_le_iff₀ h8pos]
  nlinarith [h8]

/-- The certified gain is positive eventually. -/
theorem epsS_pos (delta : ℝ) (hd0 : 0 < delta) (hd1 : delta < 1) :
    ∀ᶠ r : ℕ in atTop, 0 < epsS r delta := by
  filter_upwards [epsS_ge delta hd0, eventually_ge_atTop 1] with r hge hr1
  have hr1' : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr1
  have : (0 : ℝ) < (1 - delta) / (8 * (r : ℝ) ^ 2) := by positivity
  linarith

/-! ## §4 The packaged admissibility statement -/

/-- The conjunction handed to the Block D pipeline: for every `δ ∈ (0,1)`,
eventually in `r`, the schedule parameters are admissible and the certified
gain exceeds `(1 − δ)/(8 r²)`.  Together with
`DegeneracyLawB.supG_eq_center_tuned` (`r ≥ 7`) and the `λ`-generic Gibbs
bound `RAssembly.typeEntropyBound_supG_gen`, this is the full analytic input
of Corollary 1.4. -/
theorem schedParams_admissible (delta : ℝ) (hd0 : 0 < delta) :
    ∀ᶠ r : ℕ in atTop,
      0 < width r (lamR r) ∧
      0 < betaS r delta ∧ betaS r delta < 1 ∧
      0 < slackS r delta ∧
      (1 - delta) / (8 * (r : ℝ) ^ 2) ≤ epsS r delta := by
  filter_upwards [width_sched_pos, betaS_pos delta, betaS_lt_one delta,
    slackS_pos delta hd0, epsS_ge delta hd0] with r h1 h2 h3 h4 h5
  exact ⟨h1, h2, h3, h4, h5⟩

end

end DegeneracyLawSched
