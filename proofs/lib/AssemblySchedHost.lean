import AssemblyR
import AssemblySched

/-!
# The schedule assembly, host layer (Corollary 1.4 of the paper)

The Block D/E pipeline of `AssemblyR.lean`, re-instantiated at the tuned
schedule `λ_r = (1 − ln r / r)/ln 2` with window position and ledger slack
`θ = η = δ/4`, in place of the fixed `λ = 27/20`, `θ = η = 1/100`.

Every lemma is the exact analogue of its `AssemblyR` namesake (`…C` ↦ `…S`),
with the Block E numeric facts (`0 < width`, `0 < β < 1`, …) carried in the
`Adm` bundle instead of being proved uniformly in `r ≥ 2`; the bundle is
supplied *eventually in `r`* by
`DegeneracyLawSched.schedParams_admissible` (`proofs/lib/AssemblySched.lean`).
The Gibbs bound is `λ`-generic (`RAssembly.typeEntropyBound_supG_gen`), so no
Lemma-B input is needed here: the center evaluation enters only through the
window analytics already baked into `AssemblySched`.

The end-to-end statement built on this file is `Corollary14.lean`:
for every `δ ∈ (0,1)`, eventually in `r`, a connected bipartite graph of
degeneracy exactly `r` with `ex(n, H) ≥ c·n^(2 − 1/r + (1−δ)/(8r²))`.

**This file is `sorry`-free.**
-/

namespace RAssemblySched

open Finset TwoDegenerateGraphs RGenericProfiles RGenericBridge RGenericKernel
open RGenericSampling ThreeSampling
open Filter Topology
open scoped BigOperators NNReal
open DegeneracyLaw DegeneracyLedger DegeneracyLawB DegeneracyLawSched
open RAssembly

noncomputable section

/-! ## The parameters and the admissibility bundle -/

/-- The ledger endpoint `A_r = λ_r τ_r + sup G_r` at the schedule weight. -/
def endpointS (r : ℕ) : ℝ := Aside r (lamR r)

/-- The depth: `⌈16/(δ·width_r)⌉ + 1`, so `depth · increment > 1` at the
per-layer increment `δ·width_r/4` (`increment_eq_S`). -/
def depthS (r : ℕ) (delta : ℝ) : ℕ :=
  ⌈16 / (delta * width r (lamR r))⌉₊ + 1

/-- `β_S` as a nonnegative real, for the retention measure. -/
def betaNNS (r : ℕ) (delta : ℝ) : ℝ≥0 := Real.toNNReal (betaS r delta)

/-- The tuned Hamming radius `⌊τ_r · m⌋` at the schedule weight. -/
def radiusS (r dimension : ℕ) : ℕ :=
  RGenericSampling.rHammingRadius (tauOf r (lamR r)) dimension

/-- The extremal exponent `2 − 1/r + ε_S`. -/
def powerS (r : ℕ) (delta : ℝ) : ℝ := (2 - 1 / (r : ℝ)) + epsS r delta

/-- The sampled edge entropy rate at the schedule parameters. -/
def rateS (r : ℕ) (delta : ℝ) : ℝ :=
  RGenericSampling.sampledREdgeEntropyRate (betaNNS r delta) (tauOf r (lamR r))

/-- Half the slack in the exponent inequality. -/
def gapS (r : ℕ) (delta : ℝ) : ℝ :=
  (rateS r delta - (1 - betaS r delta) * powerS r delta * Real.log 2) / 2

/-- The host vertex count. -/
def vertexCountS (r : ℕ) (delta : ℝ) (dimension : ℕ) : ℕ :=
  ⌈3 * threeRetentionProbability (betaNNS r delta) dimension *
    ((2 ^ dimension : ℕ) : ℝ)⌉₊

/-- **The admissibility bundle**, supplied eventually in `r` by
`DegeneracyLawSched.schedParams_admissible`. -/
structure Adm (r : ℕ) (delta : ℝ) : Prop where
  hr : 2 ≤ r
  hd0 : 0 < delta
  hd1 : delta < 1
  hw : 0 < width r (lamR r)
  hb0 : 0 < betaS r delta
  hb1 : betaS r delta < 1

variable {r : ℕ} {delta : ℝ}

/-! ## Block E analogues: the numeric layer -/

theorem betaS_spec (r : ℕ) (delta : ℝ) :
    betaS r delta - Aside r (lamR r) = delta / 4 * width r (lamR r) := by
  simp only [betaS, betaTheta]; ring

theorem betaNNS_coe (h : Adm r delta) :
    ((betaNNS r delta : ℝ≥0) : ℝ) = betaS r delta :=
  Real.coe_toNNReal _ h.hb0.le

theorem tauS_nonneg (h : Adm r delta) : 0 ≤ tauOf r (lamR r) := by
  obtain ⟨ha0, ha1⟩ := aR_mem h.hr
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h.hr
  have hdiv : lamR r * Real.log 2 / (4 * (r : ℝ)) < 1 / 2 := by
    rw [div_lt_iff₀ (by linarith)]
    nlinarith
  simp only [tauOf]
  linarith

theorem tauS_le_one (h : Adm r delta) : tauOf r (lamR r) ≤ 1 := by
  obtain ⟨ha0, ha1⟩ := aR_mem h.hr
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h.hr
  have hdiv : 0 ≤ lamR r * Real.log 2 / (4 * (r : ℝ)) := by positivity
  simp only [tauOf]
  linarith

theorem slackS_eq (r : ℕ) (delta : ℝ) :
    slackS r delta = delta * width r (lamR r) / 16 := by
  have h := betaS_spec r delta
  simp only [slackS, deltaR, betaS] at h ⊢
  linarith

/-- The per-layer potential increment is exactly `δ · width_r / 4`. -/
theorem increment_eq_S (r : ℕ) (delta : ℝ) :
    RGenericBridge.potentialIncrement (betaS r delta) (slackS r delta)
      (endpointS r) = delta * width r (lamR r) / 4 := by
  have h := betaS_spec r delta
  have hs := slackS_eq r delta
  simp only [RGenericBridge.potentialIncrement, endpointS]
  linarith

theorem depthS_pos (r : ℕ) (delta : ℝ) : 0 < depthS r delta := by
  simp [depthS]

theorem depthS_increment (h : Adm r delta) :
    1 < (depthS r delta : ℝ) *
      RGenericBridge.potentialIncrement (betaS r delta) (slackS r delta)
        (endpointS r) := by
  have hw := h.hw
  have hd0 := h.hd0
  have hdw : 0 < delta * width r (lamR r) := mul_pos hd0 hw
  have hceil : 16 / (delta * width r (lamR r)) ≤
      (⌈16 / (delta * width r (lamR r))⌉₊ : ℝ) := Nat.le_ceil _
  have hcast : ((depthS r delta : ℕ) : ℝ) =
      (⌈16 / (delta * width r (lamR r))⌉₊ : ℝ) + 1 := by
    simp [depthS]
  rw [increment_eq_S, hcast]
  have hlow : 16 / (delta * width r (lamR r)) *
      (delta * width r (lamR r) / 4) = 4 := by
    field_simp
    norm_num
  nlinarith [hceil, hdw]

theorem epsMaxS_pos (h : Adm r delta) :
    0 < epsMaxR r (lamR r) (betaS r delta) := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h.hr
  have hnum : Cside r (tauOf r (lamR r)) - betaS r delta =
      (1 - delta / 4) * width r (lamR r) := by
    simpa [betaS] using Cside_sub_betaTheta r (lamR r) (delta / 4)
  rw [epsMaxR, hnum]
  have hb1 := h.hb1
  apply div_pos
  · have : 0 < 1 - delta / 4 := by linarith [h.hd1]
    exact mul_pos this h.hw
  · nlinarith [h.hb1]

theorem epsS_pos' (h : Adm r delta) : 0 < epsS r delta := by
  have hmax := epsMaxS_pos h
  have hfac : 0 < 1 - delta / 4 := by linarith [h.hd1]
  simp only [epsS, epsR]
  exact mul_pos hfac hmax

theorem epsS_lt_max (h : Adm r delta) :
    epsS r delta < epsMaxR r (lamR r) (betaS r delta) := by
  have hmax := epsMaxS_pos h
  have hd0 := h.hd0
  simp only [epsS, epsR]
  nlinarith

theorem powerS_pos (h : Adm r delta) : 0 < powerS r delta := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast h.hr
  have h1 : 1 / (r : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have := epsS_pos' h
  unfold powerS; linarith

theorem exponentGapS (h : Adm r delta) :
    RGenericSampling.RExponentGap r (tauOf r (lamR r)) (betaS r delta)
      (epsS r delta) :=
  RAssembly.Params.rExponentGap_of_lt (by have := h.hr; omega) h.hb1
    (epsS_lt_max h)

theorem rateS_gt (h : Adm r delta) :
    (1 - betaS r delta) * powerS r delta * Real.log 2 < rateS r delta := by
  have hgt := RGenericSampling.sampledREdgeEntropyRate_gt (betaNNS r delta)
    (r := r) (tauOf r (lamR r)) (epsS r delta)
    (by rw [betaNNS_coe h]; exact exponentGapS h)
  rw [betaNNS_coe h] at hgt
  unfold rateS powerS
  exact hgt

theorem rateS_pos (h : Adm r delta) : 0 < rateS r delta := by
  exact RGenericSampling.sampledREdgeEntropyRate_pos (betaNNS r delta)
    (r := r) (tauOf r (lamR r)) (epsS r delta) (by have := h.hr; omega)
    (epsS_pos' h).le
    (by rw [betaNNS_coe h]; exact h.hb1)
    (by rw [betaNNS_coe h]; exact exponentGapS h)

theorem gapS_pos (h : Adm r delta) : 0 < gapS r delta := by
  have := rateS_gt h; unfold gapS; linarith

theorem rateS_eq_power (r : ℕ) (delta : ℝ) :
    rateS r delta =
      (1 - betaS r delta) * powerS r delta * Real.log 2 + 2 * gapS r delta := by
  unfold gapS; ring

/-! ## Block D analogues: the expected retained edge count -/

theorem eventually_expectedRetainedEdge_entropy_lower_S (h : Adm r delta)
    (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ dimension : ℕ in atTop,
      Real.exp ((dimension : ℝ) * (rateS r delta - loss)) /
          ((dimension + 1 : ℕ) : ℝ) ≤
        threeExpectedRetainedEdgeCount (betaNNS r delta) dimension
          (radiusS r dimension) := by
  filter_upwards [RGenericSampling.eventually_rHammingRadius_binEntropy_ge
    (tauOf r (lamR r)) (tauS_nonneg h) loss hloss] with dimension hentropy0
  have hentropy : Real.binEntropy (tauOf r (lamR r)) - loss ≤
      Real.binEntropy ((radiusS r dimension : ℝ) / (dimension : ℝ)) := hentropy0
  have hdegree :
      Real.exp ((dimension : ℝ) *
          Real.binEntropy ((radiusS r dimension : ℝ) / (dimension : ℝ))) /
          ((dimension + 1 : ℕ) : ℝ) ≤
        ((∑ distance ∈ Finset.range (radiusS r dimension + 1),
          dimension.choose distance : ℕ) : ℝ) := by
    have hball := RGenericSampling.rHammingBall_card_entropy_lower
      (tauOf r (lamR r)) (tauS_nonneg h) (tauS_le_one h) dimension
      (fun _ : Fin dimension => false)
    rw [hammingBall_card] at hball
    exact hball
  calc
    Real.exp ((dimension : ℝ) * (rateS r delta - loss)) /
        ((dimension + 1 : ℕ) : ℝ) =
      (threeRetentionProbability (betaNNS r delta) dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        (Real.exp ((dimension : ℝ) *
            (Real.binEntropy (tauOf r (lamR r)) - loss)) /
          ((dimension + 1 : ℕ) : ℝ)) := by
        rw [threeRetentionProbability_sq_mul_wordCount_eq_exp,
          ← mul_div_assoc, ← Real.exp_add]
        congr 1
        unfold rateS RGenericSampling.sampledREdgeEntropyRate
        ring_nf
    _ ≤ (threeRetentionProbability (betaNNS r delta) dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        (Real.exp ((dimension : ℝ) *
            Real.binEntropy ((radiusS r dimension : ℝ) / (dimension : ℝ))) /
          ((dimension + 1 : ℕ) : ℝ)) := by gcongr
    _ ≤ (threeRetentionProbability (betaNNS r delta) dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        ((∑ distance ∈ Finset.range (radiusS r dimension + 1),
          dimension.choose distance : ℕ) : ℝ) := by gcongr
    _ = threeExpectedRetainedEdgeCount (betaNNS r delta) dimension
        (radiusS r dimension) := by
      rw [threeExpectedRetainedEdgeCount_eq]

theorem expectedRetainedEdgeCount_tendsto_atTop_S (h : Adm r delta) :
    Tendsto
      (fun dimension : ℕ =>
        threeExpectedRetainedEdgeCount (betaNNS r delta) dimension
          (radiusS r dimension))
      atTop atTop := by
  have hrate := rateS_pos h
  have hloss : 0 < rateS r delta / 2 := by positivity
  have hlower := eventually_expectedRetainedEdge_entropy_lower_S h
    (rateS r delta / 2) hloss
  have hgrowth := exp_mul_div_nat_succ_tendsto_atTop (rateS r delta / 2) hloss
  have hhalf : rateS r delta - rateS r delta / 2 = rateS r delta / 2 := by ring
  apply tendsto_atTop_mono' atTop _ hgrowth
  filter_upwards [hlower] with dimension hdimension
  simpa only [hhalf, mul_comm] using hdimension

theorem expectedRetainedEdgeCount_inv_tendsto_zero_S (h : Adm r delta) :
    Tendsto
      (fun dimension : ℕ =>
        1 / threeExpectedRetainedEdgeCount (betaNNS r delta) dimension
          (radiusS r dimension))
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    (expectedRetainedEdgeCount_tendsto_atTop_S h)
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]

/-! ## Block D analogues: the host vertex count -/

open Classical in
theorem retainedVertex_card_le_vertexCountS (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension))
    (hvertices :
      threeRetainedVertexCount dimension retained <
        3 * threeRetentionProbability (betaNNS r delta) dimension *
          ((2 ^ dimension : ℕ) : ℝ)) :
    Fintype.card retained ≤ vertexCountS r delta dimension := by
  have hreal : (Fintype.card retained : ℝ) ≤
      (vertexCountS r delta dimension : ℝ) := by
    calc (Fintype.card retained : ℝ)
        = threeRetainedVertexCount dimension retained :=
          (threeRetainedVertexCount_eq_card dimension retained).symm
      _ ≤ 3 * threeRetentionProbability (betaNNS r delta) dimension *
            ((2 ^ dimension : ℕ) : ℝ) := hvertices.le
      _ ≤ (vertexCountS r delta dimension : ℝ) := Nat.le_ceil _
  exact_mod_cast hreal

theorem vertexCountS_le_four_wordMean (dimension : ℕ)
    (hmean : 1 ≤ threeRetentionProbability (betaNNS r delta) dimension *
      ((2 ^ dimension : ℕ) : ℝ)) :
    (vertexCountS r delta dimension : ℝ) ≤
      4 * (threeRetentionProbability (betaNNS r delta) dimension *
        ((2 ^ dimension : ℕ) : ℝ)) := by
  have hpos := threeRetentionProbability_pos (betaNNS r delta) dimension
  have hargument :
      0 ≤ 3 * threeRetentionProbability (betaNNS r delta) dimension *
        ((2 ^ dimension : ℕ) : ℝ) := by positivity
  have hceiling :
      (vertexCountS r delta dimension : ℝ) <
        3 * threeRetentionProbability (betaNNS r delta) dimension *
          ((2 ^ dimension : ℕ) : ℝ) + 1 := by
    unfold vertexCountS
    exact Nat.ceil_lt_add_one hargument
  nlinarith

theorem eventually_vertexCountS_le_four_wordMean (h : Adm r delta) :
    ∀ᶠ dimension : ℕ in atTop,
      (vertexCountS r delta dimension : ℝ) ≤
        4 * (threeRetentionProbability (betaNNS r delta) dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
  have hlarge := Filter.tendsto_atTop.1
    (threeRetentionProbability_mul_wordCount_tendsto_atTop (betaNNS r delta)
      (by rw [betaNNS_coe h]; exact h.hb1)) (1 : ℝ)
  filter_upwards [hlarge] with dimension hdimension
  exact vertexCountS_le_four_wordMean dimension hdimension

theorem eventually_gapS_dominates_power_constant (h : Adm r delta) :
    ∀ᶠ dimension : ℕ in atTop,
      2 * (4 : ℝ) ^ powerS r delta ≤
        Real.exp (gapS r delta * (dimension : ℝ)) / ((dimension + 1 : ℕ) : ℝ) :=
  Filter.tendsto_atTop.1
    (exp_mul_div_nat_succ_tendsto_atTop (gapS r delta) (gapS_pos h))
    (2 * (4 : ℝ) ^ powerS r delta)

theorem eventually_vertexCountS_power_le_expectedRetainedEdge (h : Adm r delta) :
    ∀ᶠ dimension : ℕ in atTop,
      (vertexCountS r delta dimension : ℝ) ^ powerS r delta ≤
        threeExpectedRetainedEdgeCount (betaNNS r delta) dimension
          (radiusS r dimension) / 2 := by
  have hlower := eventually_expectedRetainedEdge_entropy_lower_S h
    (gapS r delta) (gapS_pos h)
  filter_upwards [hlower, eventually_vertexCountS_le_four_wordMean h,
    eventually_gapS_dominates_power_constant h] with dimension
    hedge_lower hvertex_bound hconstant_bound
  have hbeta : ((betaNNS r delta : ℝ≥0) : ℝ) = betaS r delta := betaNNS_coe h
  have hconstant_half :
      (4 : ℝ) ^ powerS r delta ≤
        (Real.exp (gapS r delta * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
    linarith
  have hexponent :
      ((1 - ((betaNNS r delta : ℝ≥0) : ℝ)) * (dimension : ℝ) * Real.log 2) *
            powerS r delta + gapS r delta * (dimension : ℝ) =
        (dimension : ℝ) * (rateS r delta - gapS r delta) := by
    rw [hbeta, rateS_eq_power]; ring
  have hppos := threeRetentionProbability_pos (betaNNS r delta) dimension
  calc
    (vertexCountS r delta dimension : ℝ) ^ powerS r delta ≤
      (4 * (threeRetentionProbability (betaNNS r delta) dimension *
        ((2 ^ dimension : ℕ) : ℝ))) ^ powerS r delta := by
        apply Real.rpow_le_rpow (by positivity) hvertex_bound (powerS_pos h).le
    _ = (4 : ℝ) ^ powerS r delta *
        Real.exp (((1 - ((betaNNS r delta : ℝ≥0) : ℝ)) * (dimension : ℝ) *
          Real.log 2) * powerS r delta) := by
      rw [threeRetentionProbability_mul_wordCount_eq_exp,
        Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
    _ ≤ Real.exp (((1 - ((betaNNS r delta : ℝ≥0) : ℝ)) * (dimension : ℝ) *
            Real.log 2) * powerS r delta) *
        ((Real.exp (gapS r delta * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2) := by
      rw [mul_comm ((4 : ℝ) ^ powerS r delta)]
      exact mul_le_mul_of_nonneg_left hconstant_half (Real.exp_pos _).le
    _ = (Real.exp (((1 - ((betaNNS r delta : ℝ≥0) : ℝ)) * (dimension : ℝ) *
            Real.log 2) * powerS r delta + gapS r delta * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
      rw [Real.exp_add]; ring
    _ = (Real.exp ((dimension : ℝ) * (rateS r delta - gapS r delta)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by rw [hexponent]
    _ ≤ threeExpectedRetainedEdgeCount (betaNNS r delta) dimension
        (radiusS r dimension) / 2 := by
        gcongr

theorem vertexCountS_tendsto_atTop (h : Adm r delta) :
    Tendsto (vertexCountS r delta) atTop atTop := by
  have hscaled :
      Tendsto (fun dimension : ℕ =>
          3 * (threeRetentionProbability (betaNNS r delta) dimension *
            ((2 ^ dimension : ℕ) : ℝ))) atTop atTop :=
    (threeRetentionProbability_mul_wordCount_tendsto_atTop (betaNNS r delta)
      (by rw [betaNNS_coe h]; exact h.hb1)).const_mul_atTop (by norm_num)
  have hceiling := tendsto_nat_ceil_atTop.comp hscaled
  apply hceiling.congr'
  filter_upwards [] with dimension
  change ⌈3 * (threeRetentionProbability (betaNNS r delta) dimension *
    ((2 ^ dimension : ℕ) : ℝ))⌉₊ = vertexCountS r delta dimension
  unfold vertexCountS
  congr 1
  ring

theorem vertexCountS_succ_le_two_mul (h : Adm r delta) (dimension : ℕ) :
    vertexCountS r delta (dimension + 1) ≤ 2 * vertexCountS r delta dimension := by
  have hbeta : ((betaNNS r delta : ℝ≥0) : ℝ) = betaS r delta := betaNNS_coe h
  have hbpos : (0 : ℝ) < ((betaNNS r delta : ℝ≥0) : ℝ) := by
    rw [hbeta]; exact h.hb0
  have hfactor :
      Real.exp ((1 - ((betaNNS r delta : ℝ≥0) : ℝ)) * Real.log 2) ≤ (2 : ℝ) := by
    have hstep := Real.exp_le_exp.mpr
      (show (1 - ((betaNNS r delta : ℝ≥0) : ℝ)) * Real.log 2 ≤ Real.log 2 by
        nlinarith [mul_pos hbpos (Real.log_pos (by norm_num : (1 : ℝ) < 2))])
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hstep
  have hrecurrence :
      threeRetentionProbability (betaNNS r delta) (dimension + 1) *
          ((2 ^ (dimension + 1) : ℕ) : ℝ) =
        Real.exp ((1 - ((betaNNS r delta : ℝ≥0) : ℝ)) * Real.log 2) *
          (threeRetentionProbability (betaNNS r delta) dimension *
            ((2 ^ dimension : ℕ) : ℝ)) := by
    rw [threeRetentionProbability_mul_wordCount_eq_exp,
      threeRetentionProbability_mul_wordCount_eq_exp, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hppos := threeRetentionProbability_pos (betaNNS r delta) dimension
  unfold vertexCountS
  apply Nat.ceil_le.mpr
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    3 * threeRetentionProbability (betaNNS r delta) (dimension + 1) *
        ((2 ^ (dimension + 1) : ℕ) : ℝ) =
      Real.exp ((1 - ((betaNNS r delta : ℝ≥0) : ℝ)) * Real.log 2) *
        (3 * threeRetentionProbability (betaNNS r delta) dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
        rw [show 3 * threeRetentionProbability (betaNNS r delta) (dimension + 1) *
              ((2 ^ (dimension + 1) : ℕ) : ℝ) =
            3 * (threeRetentionProbability (betaNNS r delta) (dimension + 1) *
              ((2 ^ (dimension + 1) : ℕ) : ℝ)) by ring, hrecurrence]
        ring
    _ ≤ 2 * (3 * threeRetentionProbability (betaNNS r delta) dimension *
          ((2 ^ dimension : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ ≤ 2 * (⌈3 * threeRetentionProbability (betaNNS r delta) dimension *
            ((2 ^ dimension : ℕ) : ℝ)⌉₊ : ℝ) := by
        gcongr
        exact Nat.le_ceil _

theorem exists_vertexCountS_bracket (h : Adm r delta) (minimum n : ℕ)
    (hminimum : vertexCountS r delta minimum ≤ n) :
    ∃ dimension : ℕ, minimum ≤ dimension ∧
      vertexCountS r delta dimension ≤ n ∧
      n < vertexCountS r delta (dimension + 1) := by
  have hlarge : ∀ᶠ dimension : ℕ in atTop,
      n < vertexCountS r delta dimension := by
    have hevent := Filter.tendsto_atTop.1 (vertexCountS_tendsto_atTop h) (n + 1)
    filter_upwards [hevent] with dimension hdimension
    omega
  obtain ⟨dimension, hdimension, hafter⟩ :=
    (hlarge.and (Filter.eventually_ge_atTop minimum)).exists
  have hexists : ∃ offset : ℕ, n < vertexCountS r delta (minimum + offset) := by
    refine ⟨dimension - minimum, ?_⟩
    rw [Nat.add_sub_of_le hafter]
    exact hdimension
  let offset : ℕ := Nat.find hexists
  have hnext : n < vertexCountS r delta (minimum + offset) := Nat.find_spec hexists
  have hoffset : 0 < offset := by
    by_contra hnot
    have hzero : offset = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hzero, Nat.add_zero] at hnext
    omega
  refine ⟨minimum + (offset - 1), by omega, ?_, ?_⟩
  · exact Nat.le_of_not_gt (Nat.find_min hexists (by omega))
  · rw [show minimum + (offset - 1) + 1 = minimum + offset by omega]
    exact hnext

/-! ## The budget -/

theorem eventually_budget_S (h : Adm r delta) (depth : ℕ) :
    ∀ᶠ dimension : ℕ in atTop,
      ((2 * depth : ℕ) : ℝ) * Real.exp (-(dimension : ℝ) * Real.log 2) +
        4 / threeExpectedRetainedVertexCount (betaNNS r delta) dimension +
        (4 / threeExpectedRetainedEdgeCount (betaNNS r delta) dimension
            (radiusS r dimension) +
          8 / (threeRetentionProbability (betaNNS r delta) dimension *
            ((2 ^ dimension : ℕ) : ℝ))) < 1 := by
  have hbeta : ((betaNNS r delta : ℝ≥0) : ℝ) < 1 := by
    rw [betaNNS_coe h]; exact h.hb1
  have h1 : Tendsto (fun dimension : ℕ =>
      ((2 * depth : ℕ) : ℝ) * Real.exp (-(dimension : ℝ) * Real.log 2))
      atTop (𝓝 0) := pairLayerExclusionProbability_tendsto_zero depth
  have h2 : Tendsto (fun dimension : ℕ =>
      4 / threeExpectedRetainedVertexCount (betaNNS r delta) dimension)
      atTop (𝓝 0) := by
    have hh := (threeExpectedRetainedVertexCount_inv_tendsto_zero (betaNNS r delta)
      hbeta).const_mul (4 : ℝ)
    rw [mul_zero] at hh
    exact Filter.Tendsto.congr (fun x => mul_one_div 4 _) hh
  have h3 : Tendsto (fun dimension : ℕ =>
      4 / threeExpectedRetainedEdgeCount (betaNNS r delta) dimension
        (radiusS r dimension)) atTop (𝓝 0) := by
    have hh := (expectedRetainedEdgeCount_inv_tendsto_zero_S h).const_mul (4 : ℝ)
    rw [mul_zero] at hh
    exact Filter.Tendsto.congr (fun x => mul_one_div 4 _) hh
  have h4 : Tendsto (fun dimension : ℕ =>
      8 / (threeRetentionProbability (betaNNS r delta) dimension *
        ((2 ^ dimension : ℕ) : ℝ))) atTop (𝓝 0) := by
    have hh := (threeRetentionProbability_mul_wordCount_inv_tendsto_zero
      (betaNNS r delta) hbeta).const_mul (8 : ℝ)
    rw [mul_zero] at hh
    exact Filter.Tendsto.congr (fun x => mul_one_div 8 _) hh
  have hsum := ((h1.add h2).add (h3.add h4))
  simpa using (tendsto_order.1 hsum).2 1 (by norm_num)

/-! ## The exclusion step at the schedule parameters -/

section Copy

variable {baseSize depth dimension radius : ℕ}

theorem rGraphCopy_layer_entropy_upper_S
    (h : Adm r delta)
    (hGibbs : TypeEntropyBound r (supG r (lamR r)) (lamR r))
    (hbase : 2 * r ^ 2 ≤ baseSize) (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (hdis : RGenericBridge.rChildArrayAverageDisagreement r
        (rGraphCopyParentWords retained copy layer)
        (rGraphCopyChildWords retained copy layer) ≤ tauOf r (lamR r)) :
    rChildArrayEntropy
        (rGraphCopyParentWords retained copy layer)
        (rGraphCopyChildWords retained copy layer) ≤
      endpointS r +
        (rGraphCopyLayerPotential retained copy ⟨layer.val + 1, by omega⟩ -
          rGraphCopyLayerPotential retained copy ⟨layer.val, by omega⟩) / 2 +
        worCorrectionR r (Fintype.card (RLayer baseSize r layer.val))
          (lamR r) := by
  have hr1 : (2 : ℕ) ≤ r := h.hr
  have hb2 : r + 1 ≤ 2 * r ^ 2 := by nlinarith
  have hbase' : r + 1 ≤ baseSize := le_trans hb2 hbase
  have hcard : 2 * r ^ 2 ≤ Fintype.card (RLayer baseSize r layer.val) := by
    have hge := RGenericBridge.rLayer_card_ge_base (r := r) baseSize layer.val
      (by omega) hbase'
    omega
  have hbound := RGenericBridge.rChildArrayEntropy_empirical_bound
    (A := supG r (lamR r)) (lam := lamR r)
    (by omega) (lamR_pos h.hr).le hGibbs hcard hdimension
    (rGraphCopyParentWords retained copy layer)
    (rGraphCopyChildWords retained copy layer)
  rw [rGraphCopy_childPotential_eq retained copy layer,
    rGraphCopy_parentPotential_eq retained copy layer] at hbound
  have hend : endpointS r = supG r (lamR r) + lamR r * tauOf r (lamR r) := by
    unfold endpointS Aside; ring
  rw [hend]
  have hlam : (0 : ℝ) ≤ lamR r := (lamR_pos h.hr).le
  linarith [hbound, mul_le_mul_of_nonneg_left hdis hlam]

theorem rGraphCopy_averageDisagreement_le_tau_S
    (hr : 2 ≤ r) (hbase : r + 1 ≤ baseSize) (hdimension : 0 < dimension)
    (hradius : (radius : ℝ) ≤ tauOf r (lamR r) * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    RGenericBridge.rChildArrayAverageDisagreement r
      (rGraphCopyParentWords retained copy layer)
      (rGraphCopyChildWords retained copy layer) ≤ tauOf r (lamR r) := by
  have hdimension_real : (0 : ℝ) < (dimension : ℝ) := by exact_mod_cast hdimension
  have hparents : r ≤ Fintype.card (RLayer baseSize r layer.val) := by
    have := RGenericBridge.rLayer_card_ge_base (r := r) baseSize layer.val
      (by omega) hbase
    omega
  refine le_trans
    (RGenericBridge.rChildArrayAverageDisagreement_le_radius (by omega) hparents
      hdimension _ _ radius
      (fun sub parent hparent =>
        rGraphCopy_parent_child_hammingDist_le retained copy layer
          sub parent hparent))
    ((div_le_iff₀ hdimension_real).mpr hradius)

theorem rGraph_free_of_layer_exclusion_S
    (h : Adm r delta)
    (hGibbs : TypeEntropyBound r (supG r (lamR r)) (lamR r))
    (hbase : 2 * r ^ 2 ≤ baseSize) (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) *
      RGenericBridge.potentialIncrement (betaS r delta) (slackS r delta)
        (endpointS r))
    (hradius : (radius : ℝ) ≤ tauOf r (lamR r) * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion : ∀ (side : Bool) (layer : Fin depth),
      retained ∉ RGenericSampling.badRLayerRetentionEvent
        (Fintype.card (RLayer baseSize r layer.val)) dimension r side
        (betaS r delta - slackS r delta))
    (herror : ∀ layer : Fin depth,
      worCorrectionR r (Fintype.card (RLayer baseSize r layer.val)) (lamR r) <
        slackS r delta) :
    (rParentSystem baseSize r depth).graph.Free
      (retainedHammingHost dimension radius retained) := by
  classical
  have hr1 : (2 : ℕ) ≤ r := h.hr
  have hb2 : r + 1 ≤ 2 * r ^ 2 := by nlinarith
  have hbase' : r + 1 ≤ baseSize := le_trans hb2 hbase
  intro hcontained
  obtain ⟨copy⟩ := hcontained
  set potential : ℕ → ℝ := fun level =>
    if hlevel : level < depth + 1 then
      rGraphCopyLayerPotential retained copy ⟨level, hlevel⟩ else 0
    with hpotential
  apply RGenericBridge.potential_layers_impossible depth potential
    (RGenericBridge.potentialIncrement (betaS r delta) (slackS r delta)
      (endpointS r))
  · intro level hlevel
    have hinrange : level < depth + 1 := by omega
    simpa [hpotential, hinrange, show level ≤ depth from by omega] using
      rGraphCopyLayerPotential_mem_Icc hr1 hbase' hdimension retained copy
        ⟨level, hinrange⟩
  · intro level hlevel
    have hnext : level + 1 < depth + 1 := by omega
    have hcurrent : level < depth + 1 := by omega
    have hsize : r ≤ Fintype.card (RLayer baseSize r level) := by
      have hge := RGenericBridge.rLayer_card_ge_base (r := r) baseSize level
        (by omega) hbase'
      omega
    let reference : RLayer (Fintype.card (RLayer baseSize r level)) r 1 :=
      Classical.choice (rLayerSub_nonempty hsize)
    have hlower := rGraphCopy_entropy_lower_of_exclusion retained copy
      hr1 hbase' ⟨level, hlevel⟩ reference (betaS r delta - slackS r delta)
      (hexclusion
        (rGraphCopyChildSide retained copy ⟨level, hlevel⟩ reference)
        ⟨level, hlevel⟩)
    have hupper := rGraphCopy_layer_entropy_upper_S h hGibbs hbase hdimension
      retained copy ⟨level, hlevel⟩
      (rGraphCopy_averageDisagreement_le_tau_S hr1 hbase' hdimension hradius
        retained copy ⟨level, hlevel⟩)
    have hincrement := RGenericBridge.potential_increment
      (betaS r delta) (slackS r delta) (endpointS r)
      (rGraphCopyLayerPotential retained copy ⟨level, hcurrent⟩)
      (rGraphCopyLayerPotential retained copy ⟨level + 1, hnext⟩)
      (rChildArrayEntropy
        (rGraphCopyParentWords retained copy ⟨level, hlevel⟩)
        (rGraphCopyChildWords retained copy ⟨level, hlevel⟩))
      (worCorrectionR r (Fintype.card (RLayer baseSize r level)) (lamR r))
      (herror ⟨level, hlevel⟩) hlower hupper
    simpa [hpotential, hnext, hcurrent, hlevel,
      show level ≤ depth from by omega] using hincrement
  · exact hdepth

end Copy

theorem rGraphOverFin_free_of_exclusion_S
    {baseSize depth dimension : ℕ}
    (h : Adm r delta)
    (hGibbs : TypeEntropyBound r (supG r (lamR r)) (lamR r))
    (hbase : 2 * r ^ 2 ≤ baseSize) (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) *
      RGenericBridge.potentialIncrement (betaS r delta) (slackS r delta)
        (endpointS r))
    (herror : ∀ layer : Fin depth,
      worCorrectionR r (Fintype.card (RLayer baseSize r layer.val)) (lamR r) <
        slackS r delta)
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion : retained ∉
      RGenericSampling.badRLayersRetentionEvent (betaNNS r delta)
        (slackS r delta) r
        (fun layer : Fin depth => Fintype.card (RLayer baseSize r layer.val))
        dimension) :
    (rGraphOverFin baseSize r depth).Free
      (retainedHammingHost dimension (radiusS r dimension) retained) := by
  refine (SimpleGraph.free_congr_left (rGraphOverFinIso baseSize r depth)).mp ?_
  refine rGraph_free_of_layer_exclusion_S h hGibbs hbase hdimension hdepth
    (RGenericSampling.rHammingRadius_le _ (tauS_nonneg h) dimension)
    retained ?_ herror
  intro side layer hmem
  refine hexclusion (Set.mem_iUnion.mpr ⟨side, Set.mem_iUnion.mpr ⟨layer, ?_⟩⟩)
  rwa [betaNNS_coe h]

/-! ## The free dense hosts and the extremal assembly -/

theorem slackS_pos' (h : Adm r delta) : 0 < slackS r delta := by
  rw [slackS_eq]
  have := mul_pos h.hd0 h.hw
  linarith

theorem exists_free_dense_hosts_S (h : Adm r delta)
    (hGibbs : TypeEntropyBound r (supG r (lamR r)) (lamR r)) :
    ∃ baseSize depth : ℕ, 2 * r ^ 2 ≤ baseSize ∧ 0 < depth ∧
      ∀ᶠ dimension : ℕ in atTop,
        ∃ retained : Set (Bool × HammingWord dimension),
          (rGraphOverFin baseSize r depth).Free
              (retainedHammingHost dimension (radiusS r dimension) retained) ∧
          threeRetainedVertexCount dimension retained <
            3 * threeRetentionProbability (betaNNS r delta) dimension *
              ((2 ^ dimension : ℕ) : ℝ) ∧
          threeExpectedRetainedEdgeCount (betaNNS r delta) dimension
              (radiusS r dimension) / 2 ≤
            hammingRetainedEdgeCount dimension (radiusS r dimension) retained := by
  classical
  obtain ⟨Lerr, hLerr⟩ :=
    exists_worCorrection_base r (lamR r) (slackS r delta) (slackS_pos' h)
  obtain ⟨Lcnt, hLcnt⟩ := exists_counting_base r h.hr (slackS r delta)
    (slackS_pos' h)
  refine ⟨max (2 * r ^ 2) (max Lerr Lcnt), depthS r delta, le_max_left _ _,
    depthS_pos r delta, ?_⟩
  set baseSize := max (2 * r ^ 2) (max Lerr Lcnt) with hbaseSize
  have hbase2 : 2 * r ^ 2 ≤ baseSize := le_max_left _ _
  have hr2 := h.hr
  have hb2 : r + 1 ≤ 2 * r ^ 2 := by nlinarith
  have hbase' : r + 1 ≤ baseSize := le_trans hb2 hbase2
  set layerSizes : Fin (depthS r delta) → ℕ :=
    fun layer => Fintype.card (RLayer baseSize r layer.val) with hlayerSizes
  have hcard_ge : ∀ layer : Fin (depthS r delta), baseSize ≤ layerSizes layer :=
    fun layer => RGenericBridge.rLayer_card_ge_base (r := r) baseSize layer.val
      (by omega) hbase'
  have hparents : ∀ layer, r ≤ layerSizes layer :=
    fun layer => le_trans (by omega) (hcard_ge layer)
  have hcount : ∀ layer,
      (layerSizes layer : ℝ) +
        ((r : ℝ) + 1) * logTwo (((layerSizes layer).choose r + 1 : ℕ) : ℝ) -
          slackS r delta * ((layerSizes layer).choose r : ℝ) < -1 := by
    intro layer
    refine hLcnt _ (le_trans ?_ (hcard_ge layer))
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have herror : ∀ layer : Fin (depthS r delta),
      worCorrectionR r (layerSizes layer) (lamR r) < slackS r delta := by
    intro layer
    refine hLerr _ (le_trans ?_ (hcard_ge layer))
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  filter_upwards [eventually_budget_S h (depthS r delta),
    Filter.eventually_gt_atTop 0] with dimension hbudget hdimension
  obtain ⟨retained, hout, hvert, hedge⟩ :=
    RGenericSampling.exists_good_retention (betaNNS r delta) (slackS r delta)
      (r := r) layerSizes (radiusS r dimension) hdimension hparents hcount
      hbudget
  exact ⟨retained,
    rGraphOverFin_free_of_exclusion_S h hGibbs hbase2 hdimension
      (depthS_increment h) herror retained hout,
    hvert, hedge⟩

open Classical in
theorem eventually_expectedRetainedEdge_le_extremalNumber_S
    {baseSize depth : ℕ} (h : Adm r delta)
    (hbase : r ≤ baseSize) (hdepth : 0 < depth)
    (hhosts : ∀ᶠ dimension : ℕ in atTop,
      ∃ retained : Set (Bool × HammingWord dimension),
        (rGraphOverFin baseSize r depth).Free
            (retainedHammingHost dimension (radiusS r dimension) retained) ∧
        threeRetainedVertexCount dimension retained <
          3 * threeRetentionProbability (betaNNS r delta) dimension *
            ((2 ^ dimension : ℕ) : ℝ) ∧
        threeExpectedRetainedEdgeCount (betaNNS r delta) dimension
            (radiusS r dimension) / 2 ≤
          hammingRetainedEdgeCount dimension (radiusS r dimension) retained) :
    ∀ᶠ dimension : ℕ in atTop,
      threeExpectedRetainedEdgeCount (betaNNS r delta) dimension
          (radiusS r dimension) / 2 ≤
        (SimpleGraph.extremalNumber (vertexCountS r delta dimension)
          (rGraphOverFin baseSize r depth) : ℝ) := by
  filter_upwards [hhosts] with dimension hhost
  obtain ⟨retained, hfree, hvertices, hedges⟩ := hhost
  have hcard := retainedVertex_card_le_vertexCountS dimension retained hvertices
  have hembedding : Nonempty (retained ↪ Fin (vertexCountS r delta dimension)) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa using hcard
  obtain ⟨embedding⟩ := hembedding
  let paddedHost : SimpleGraph (Fin (vertexCountS r delta dimension)) :=
    (retainedHammingHost dimension (radiusS r dimension) retained).map embedding
  have hpadded_free : (rGraphOverFin baseSize r depth).Free paddedHost :=
    CompactnessConjecture.free_map_of_no_isolated
      (rGraphOverFin baseSize r depth)
      (rGraphOverFin_forall_exists_adj baseSize r depth h.hr hbase hdepth)
      embedding hfree
  have hpadded_edges :
      paddedHost.edgeFinset.card ≤
        SimpleGraph.extremalNumber (vertexCountS r delta dimension)
          (rGraphOverFin baseSize r depth) := by
    simpa using (SimpleGraph.card_edgeFinset_le_extremalNumber hpadded_free)
  calc
    threeExpectedRetainedEdgeCount (betaNNS r delta) dimension
        (radiusS r dimension) / 2 ≤
      hammingRetainedEdgeCount dimension (radiusS r dimension) retained := hedges
    _ = ((retainedHammingHost dimension (radiusS r dimension)
        retained).edgeFinset.card : ℝ) :=
      hammingRetainedEdgeCount_eq_edgeFinset_card dimension
        (radiusS r dimension) retained
    _ = (paddedHost.edgeFinset.card : ℝ) := by
      congr 1
      exact (SimpleGraph.card_edgeFinset_map embedding
        (retainedHammingHost dimension (radiusS r dimension) retained)).symm
    _ ≤ (SimpleGraph.extremalNumber (vertexCountS r delta dimension)
        (rGraphOverFin baseSize r depth) : ℝ) := by exact_mod_cast hpadded_edges

open Classical in
theorem rDegenerateExtremalCounterexample_of_hosts_S
    {baseSize depth : ℕ} (h : Adm r delta)
    (hbase1 : r + 1 ≤ baseSize) (hdepth : 0 < depth)
    (hhosts : ∀ᶠ dimension : ℕ in atTop,
      ∃ retained : Set (Bool × HammingWord dimension),
        (rGraphOverFin baseSize r depth).Free
            (retainedHammingHost dimension (radiusS r dimension) retained) ∧
        threeRetainedVertexCount dimension retained <
          3 * threeRetentionProbability (betaNNS r delta) dimension *
            ((2 ^ dimension : ℕ) : ℝ) ∧
        threeExpectedRetainedEdgeCount (betaNNS r delta) dimension
            (radiusS r dimension) / 2 ≤
          hammingRetainedEdgeCount dimension (radiusS r dimension) retained) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧ H.IsBipartite ∧ IsDegenerate r H ∧
      ¬ IsDegenerate (r - 1) H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + epsS r delta) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  classical
  have hbase : r ≤ baseSize := by omega
  set forbidden := rGraphOverFin baseSize r depth with hforbidden
  have hnoisolated :
      ∀ vertex : Fin (Fintype.card (RVertex baseSize r depth)),
        ∃ neighbor, forbidden.Adj vertex neighbor :=
    rGraphOverFin_forall_exists_adj baseSize r depth h.hr hbase hdepth
  have hsubsequence :
      ∀ᶠ dimension : ℕ in atTop,
        (vertexCountS r delta dimension : ℝ) ^ powerS r delta ≤
          (SimpleGraph.extremalNumber (vertexCountS r delta dimension)
            forbidden : ℝ) := by
    filter_upwards [eventually_vertexCountS_power_le_expectedRetainedEdge h,
      eventually_expectedRetainedEdge_le_extremalNumber_S h hbase hdepth hhosts]
      with dimension hpower hbound
    exact hpower.trans hbound
  refine ⟨Fintype.card (RVertex baseSize r depth), forbidden,
    rGraphOverFin_connected baseSize r depth h.hr hbase hdepth,
    rGraphOverFin_isBipartite baseSize r depth,
    rGraphOverFin_isDegenerate baseSize r depth,
    rGraphOverFin_not_isDegenerate baseSize r depth
      (by have := h.hr; omega) hbase1 hdepth,
    1 / (2 : ℝ) ^ powerS r delta,
    one_div_pos.mpr (Real.rpow_pos_of_pos (by norm_num) (powerS r delta)), ?_⟩
  obtain ⟨minimum, hminimum⟩ := Filter.eventually_atTop.1 hsubsequence
  apply Filter.eventually_atTop.2
  refine ⟨vertexCountS r delta minimum, ?_⟩
  intro n hn
  obtain ⟨dimension, hdimension, hbelow, habove⟩ :=
    exists_vertexCountS_bracket h minimum n hn
  have hdouble := vertexCountS_succ_le_two_mul h dimension
  have hn_bound : n ≤ 2 * vertexCountS r delta dimension := by omega
  have hn_real : (n : ℝ) ≤ 2 * (vertexCountS r delta dimension : ℝ) := by
    exact_mod_cast hn_bound
  have hsubseq := hminimum dimension hdimension
  have hmonotone :
      SimpleGraph.extremalNumber (vertexCountS r delta dimension) forbidden ≤
        SimpleGraph.extremalNumber n forbidden :=
    CompactnessConjecture.extremalNumber_monotone_of_no_isolated
      forbidden hnoisolated hbelow
  have hpower_eq : (2 : ℝ) - 1 / (r : ℝ) + epsS r delta = powerS r delta := by
    unfold powerS; ring
  rw [hpower_eq]
  calc
    (1 / (2 : ℝ) ^ powerS r delta) * (n : ℝ) ^ powerS r delta ≤
      (1 / (2 : ℝ) ^ powerS r delta) *
        (2 * (vertexCountS r delta dimension : ℝ)) ^ powerS r delta := by
        apply mul_le_mul_of_nonneg_left
        · exact Real.rpow_le_rpow (Nat.cast_nonneg n) hn_real (powerS_pos h).le
        · positivity
    _ = (vertexCountS r delta dimension : ℝ) ^ powerS r delta := by
        rw [Real.mul_rpow (by norm_num)
          (Nat.cast_nonneg (vertexCountS r delta dimension))]
        have htwo : (2 : ℝ) ^ powerS r delta ≠ 0 :=
          (Real.rpow_pos_of_pos (by norm_num) (powerS r delta)).ne'
        field_simp
    _ ≤ (SimpleGraph.extremalNumber (vertexCountS r delta dimension)
        forbidden : ℝ) := hsubseq
    _ ≤ (SimpleGraph.extremalNumber n forbidden : ℝ) := by
        exact_mod_cast hmonotone

/-- **The schedule counterexample at admissible `(r, δ)`**: gain
`(1 − δ)/(8 r²)` requires only the additional certificate `epsS_ge`. -/
theorem rDegenerateExtremalCounterexample_sched
    (h : Adm r delta)
    (heps : (1 - delta) / (8 * (r : ℝ) ^ 2) ≤ epsS r delta) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧ H.IsBipartite ∧ IsDegenerate r H ∧
      ¬ IsDegenerate (r - 1) H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) +
              (1 - delta) / (8 * (r : ℝ) ^ 2)) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  have hGibbs : TypeEntropyBound r (supG r (lamR r)) (lamR r) :=
    typeEntropyBound_supG_gen r (by have := h.hr; omega) (lamR r)
  obtain ⟨baseSize, depth, hbase2, hdepth, hhosts⟩ :=
    exists_free_dense_hosts_S h hGibbs
  have hr2 := h.hr
  have hb1 : r + 1 ≤ baseSize := by nlinarith
  obtain ⟨q, H, hcon, hbip, hdeg, hnodeg, c, hc0, hbnd⟩ :=
    rDegenerateExtremalCounterexample_of_hosts_S h hb1 hdepth hhosts
  refine ⟨q, H, hcon, hbip, hdeg, hnodeg, c, hc0, ?_⟩
  filter_upwards [hbnd, Filter.eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hmono : (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) +
      (1 - delta) / (8 * (r : ℝ) ^ 2)) ≤
      (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + epsS r delta) :=
    Real.rpow_le_rpow_of_exponent_le hn1' (by linarith)
  calc c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) +
      (1 - delta) / (8 * (r : ℝ) ^ 2))
      ≤ c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + epsS r delta) :=
        mul_le_mul_of_nonneg_left hmono hc0.le
    _ ≤ (SimpleGraph.extremalNumber n H : ℝ) := hn

end

end RAssemblySched
