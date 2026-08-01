import Sampling3
import ProfilesR
import LawDefs

/-!
# `SamplingR.lean` — the `r`-generic retention/sampling layer

Generalises the `r`-specific parts of `Sampling3.lean`:

* the `badRChild / badRLayer / badRLayersRetentionEvent` chain over
  `ProfilesR`'s counting (`RBitType r = Fin (r+1)`, `M = C(L,r)`);
* the `tauOf`-based Hamming radius `⌊τ_r · m⌋` with
  `τ_r = DegeneracyLaw.tauOf r lam`;
* the entropy lower bound on the ball size;
* the whp conjunction `exists_good_retention`, generic in `(r, beta, eps)`,
  with the exponent inequality taken as a **hypothesis** (the numerals arrive
  from `LedgerR` / the window at instantiation).

**The generic measure chain is reused, not re-proved.**  `Sampling3` lines
907–2059 (`threeRetentionProbability`, `threeRetentionMeasure`, the Chebyshev
vertex/edge second-moment chain, `threeRetainedVertexCount_*`,
`threeRetainedEdgeCount_*`) is `beta`-generic *and arity-free*: it never
mentions `3` or `.choose 3`.  We `open ThreeSampling` and instantiate it.
The `three` in those names is historical, not an arity.

See `research/results_U_generic_survey.md` §3 and
`research/results_Z_lean_bridgeR.md`.
-/

open TwoDegenerateGraphs Filter Topology
open scoped NNReal

namespace RGenericSampling

open RGenericProfiles ThreeSampling

variable (beta : ℝ≥0) (slack : ℝ)

/-! ## Part 1: the child-array retention events, over `r`-subsets -/

noncomputable def rChildVertexFinset
    {parentCount dimension r : ℕ}
    (side : Bool)
    (children : RLayer parentCount r 1 → HammingWord dimension) :
    Finset (Bool × HammingWord dimension) := by
  classical
  exact (Finset.univ : Finset (RLayer parentCount r 1)).image
    (fun sub => (side, children sub))

theorem rChildVertexFinset_card
    {parentCount dimension r : ℕ}
    (side : Bool)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (hinjective : Function.Injective children) :
    (rChildVertexFinset side children).card = parentCount.choose r := by
  classical
  unfold rChildVertexFinset
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ, rLayer_one_card]
  · intro first second hequal
    exact hinjective (congrArg Prod.snd hequal)

def rChildRetentionEvent
    {parentCount dimension r : ℕ}
    (side : Bool)
    (children : RLayer parentCount r 1 → HammingWord dimension) :
    Set (Set (Bool × HammingWord dimension)) :=
  {retained | ∀ sub, (side, children sub) ∈ retained}

theorem retentionMeasure_real_rChildren
    {parentCount dimension r : ℕ}
    (side : Bool)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (hinjective : Function.Injective children) :
    (threeRetentionMeasure beta dimension).real
        (rChildRetentionEvent side children) =
      threeRetentionProbability beta dimension ^ (parentCount.choose r) := by
  classical
  have hevent :
      rChildRetentionEvent side children =
        {retained : Set (Bool × HammingWord dimension) |
          ∀ vertex ∈ rChildVertexFinset side children,
            vertex ∈ retained} := by
    ext retained
    simp [rChildRetentionEvent, rChildVertexFinset]
  rw [hevent, threeRetentionMeasure_real_contains_finset,
    rChildVertexFinset_card side children hinjective]

noncomputable def badRChildRetentionEvent
    {parentCount dimension : ℕ} (r : ℕ)
    (parents : Fin parentCount → HammingWord dimension)
    (side : Bool)
    (threshold : ℝ) : Set (Set (Bool × HammingWord dimension)) := by
  classical
  exact
    ⋃ children ∈
        (badRChildArrays r parents threshold).filter Function.Injective,
      rChildRetentionEvent side children

theorem badRChildRetentionEvent_real_le
    {parentCount dimension r : ℕ}
    (hparents : r ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (side : Bool)
    (threshold : ℝ) :
    (threeRetentionMeasure beta dimension).real
        (badRChildRetentionEvent r parents side threshold) ≤
      ((((parentCount.choose r + 1) ^ ((r + 1) * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose r : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          threeRetentionProbability beta dimension ^
            (parentCount.choose r) := by
  classical
  set distinctBad :
      Finset (RLayer parentCount r 1 → HammingWord dimension) :=
    (badRChildArrays r parents threshold).filter Function.Injective
      with hdistinctBad
  have hprobability_nonneg :
      0 ≤ threeRetentionProbability beta dimension ^
        (parentCount.choose r) :=
    pow_nonneg (threeRetentionProbability_pos beta dimension).le _
  have hcard :
      (distinctBad.card : ℝ) ≤
        ((badRChildArrays r parents threshold).card : ℝ) := by
    rw [hdistinctBad]
    exact_mod_cast
      Finset.card_filter_le
        (badRChildArrays r parents threshold) Function.Injective
  calc
    (threeRetentionMeasure beta dimension).real
        (badRChildRetentionEvent r parents side threshold) =
      (threeRetentionMeasure beta dimension).real
        (⋃ children ∈ distinctBad, rChildRetentionEvent side children) := by
        rw [hdistinctBad]; rfl
    _ ≤ ∑ children ∈ distinctBad,
          (threeRetentionMeasure beta dimension).real
            (rChildRetentionEvent side children) :=
        MeasureTheory.measureReal_biUnion_finset_le
          distinctBad (rChildRetentionEvent side)
    _ = ∑ _children ∈ distinctBad,
          threeRetentionProbability beta dimension ^
            (parentCount.choose r) := by
        refine Finset.sum_congr rfl fun children hchildren => ?_
        have hinjective : Function.Injective children := by
          rw [hdistinctBad] at hchildren
          exact (Finset.mem_filter.mp hchildren).2
        exact retentionMeasure_real_rChildren beta side children hinjective
    _ = (distinctBad.card : ℝ) *
          threeRetentionProbability beta dimension ^
            (parentCount.choose r) := by
        simp [nsmul_eq_mul]
    _ ≤ ((badRChildArrays r parents threshold).card : ℝ) *
          threeRetentionProbability beta dimension ^
            (parentCount.choose r) :=
        mul_le_mul_of_nonneg_right hcard hprobability_nonneg
    _ ≤ _ :=
        mul_le_mul_of_nonneg_right
          (badRChildArrays_card_le hparents hdimension parents threshold)
          hprobability_nonneg

/-! ## Part 2: the union over parent arrays (one layer) -/

noncomputable def badRLayerRetentionEvent
    (parentCount dimension r : ℕ)
    (side : Bool)
    (threshold : ℝ) : Set (Set (Bool × HammingWord dimension)) :=
  ⋃ parents : Fin parentCount → HammingWord dimension,
    badRChildRetentionEvent r parents side threshold

theorem badRLayerRetentionEvent_real_le
    {parentCount dimension r : ℕ}
    (hparents : r ≤ parentCount)
    (hdimension : 0 < dimension)
    (side : Bool)
    (threshold : ℝ) :
    (threeRetentionMeasure beta dimension).real
        (badRLayerRetentionEvent parentCount dimension r side threshold) ≤
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose r + 1) ^ ((r + 1) * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose r : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          threeRetentionProbability beta dimension ^
            (parentCount.choose r) := by
  classical
  set bound : ℝ :=
    ((((parentCount.choose r + 1) ^ ((r + 1) * dimension) : ℕ) : ℝ) *
      Real.exp
        ((parentCount.choose r : ℝ) * Real.log 2 *
          (dimension : ℝ) * threshold)) *
        threeRetentionProbability beta dimension ^
          (parentCount.choose r) with hbound
  calc
    (threeRetentionMeasure beta dimension).real
        (badRLayerRetentionEvent parentCount dimension r side threshold) =
      (threeRetentionMeasure beta dimension).real
        (⋃ parents : Fin parentCount → HammingWord dimension,
          badRChildRetentionEvent r parents side threshold) := rfl
    _ ≤ ∑ parents : Fin parentCount → HammingWord dimension,
          (threeRetentionMeasure beta dimension).real
            (badRChildRetentionEvent r parents side threshold) :=
        MeasureTheory.measureReal_iUnion_fintype_le
          (fun parents => badRChildRetentionEvent r parents side threshold)
    _ ≤ ∑ _parents : Fin parentCount → HammingWord dimension, bound := by
      refine Finset.sum_le_sum fun parents _ => ?_
      rw [hbound]
      exact badRChildRetentionEvent_real_le beta
        hparents hdimension parents side threshold
    _ = _ := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        hammingParentTuple_card, hbound]
      ring

/-- The layer-exclusion bound, in the `exp(-m log 2)` form used by the union
bound.  `hbase` is the `r`-generic counting hypothesis:
`L + (r+1)·log₂(C(L,r)+1) − slack·C(L,r) < −1`. -/
theorem badRLayerRetentionEvent_real_lt_exp_neg
    {parentCount dimension r : ℕ}
    (hparents : r ≤ parentCount)
    (hdimension : 0 < dimension)
    (hbase :
      (parentCount : ℝ) +
        ((r : ℝ) + 1) * logTwo ((parentCount.choose r + 1 : ℕ) : ℝ) -
          slack * (parentCount.choose r : ℝ) < -1)
    (side : Bool) :
    (threeRetentionMeasure beta dimension).real
      (badRLayerRetentionEvent parentCount dimension r side
        ((beta : ℝ) - slack)) <
      Real.exp (-(dimension : ℝ) * Real.log 2) := by
  have hdimension_real : 0 < (dimension : ℝ) := by exact_mod_cast hdimension
  calc
    (threeRetentionMeasure beta dimension).real
      (badRLayerRetentionEvent parentCount dimension r side
        ((beta : ℝ) - slack)) ≤
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose r + 1) ^ ((r + 1) * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose r : ℝ) * Real.log 2 *
            (dimension : ℝ) * ((beta : ℝ) - slack))) *
          threeRetentionProbability beta dimension ^
            (parentCount.choose r) :=
        badRLayerRetentionEvent_real_le beta hparents hdimension side _
    _ = Real.exp
        ((dimension : ℝ) * Real.log 2 *
          ((parentCount : ℝ) +
            ((r : ℝ) + 1) * logTwo ((parentCount.choose r + 1 : ℕ) : ℝ) -
              slack * (parentCount.choose r : ℝ))) := by
        rw [show threeRetentionProbability beta dimension =
            Real.exp (-((beta : ℝ) * (dimension : ℝ) * Real.log 2)) from rfl]
        exact badRLayerRetentionBound_eq_exp parentCount dimension r
          (beta : ℝ) slack
    _ < Real.exp (-(dimension : ℝ) * Real.log 2) := by
      apply Real.exp_lt_exp.mpr
      have hscaled := mul_lt_mul_of_pos_left hbase
        (mul_pos hdimension_real log_two_pos)
      nlinarith

/-! ## Part 3: the union over all layers and both sides -/

noncomputable def badRLayersRetentionEvent
    {depth : ℕ} (r : ℕ)
    (layerSizes : Fin depth → ℕ)
    (dimension : ℕ) : Set (Set (Bool × HammingWord dimension)) :=
  ⋃ side : Bool, ⋃ layer : Fin depth,
    badRLayerRetentionEvent (layerSizes layer) dimension r side
      ((beta : ℝ) - slack)

theorem badRLayersRetentionEvent_real_le
    {depth dimension r : ℕ}
    (layerSizes : Fin depth → ℕ)
    (hdimension : 0 < dimension)
    (hparents : ∀ layer, r ≤ layerSizes layer)
    (hbase : ∀ layer,
      (layerSizes layer : ℝ) +
        ((r : ℝ) + 1) * logTwo
          (((layerSizes layer).choose r + 1 : ℕ) : ℝ) -
          slack * ((layerSizes layer).choose r : ℝ) < -1) :
    (threeRetentionMeasure beta dimension).real
        (badRLayersRetentionEvent beta slack r layerSizes dimension) ≤
      (((2 * depth : ℕ) : ℝ)) *
        Real.exp (-(dimension : ℝ) * Real.log 2) := by
  classical
  set bound : ℝ := Real.exp (-(dimension : ℝ) * Real.log 2) with hbnd
  calc
    (threeRetentionMeasure beta dimension).real
        (badRLayersRetentionEvent beta slack r layerSizes dimension) =
      (threeRetentionMeasure beta dimension).real
        (⋃ side : Bool, ⋃ layer : Fin depth,
          badRLayerRetentionEvent (layerSizes layer) dimension r side
            ((beta : ℝ) - slack)) := rfl
    _ ≤ ∑ side : Bool,
        (threeRetentionMeasure beta dimension).real
          (⋃ layer : Fin depth,
            badRLayerRetentionEvent (layerSizes layer) dimension r side
              ((beta : ℝ) - slack)) :=
        MeasureTheory.measureReal_iUnion_fintype_le _
    _ ≤ ∑ side : Bool, ∑ layer : Fin depth,
          (threeRetentionMeasure beta dimension).real
            (badRLayerRetentionEvent
              (layerSizes layer) dimension r side
                ((beta : ℝ) - slack)) := by
        refine Finset.sum_le_sum fun side _ => ?_
        exact MeasureTheory.measureReal_iUnion_fintype_le _
    _ ≤ ∑ _side : Bool, ∑ _layer : Fin depth, bound := by
        refine Finset.sum_le_sum fun side _ => ?_
        refine Finset.sum_le_sum fun layer _ => ?_
        exact (badRLayerRetentionEvent_real_lt_exp_neg beta slack
          (hparents layer) hdimension (hbase layer) side).le
    _ = (((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2) := by
        simp [hbnd, nsmul_eq_mul]
        ring

/-! ## Part 4: the `tauOf`-based Hamming radius

`τ_r = DegeneracyLaw.tauOf r lam = 1/2 − λ ln 2 / (4r)`.  Everything below is
stated for an abstract `tau` with `0 ≤ tau ≤ 1`; `tauOf` is substituted at
instantiation, where `LedgerR` supplies the two inequalities. -/

/-- The `r`-generic Hamming radius `⌊τ·m⌋`. -/
noncomputable def rHammingRadius (tau : ℝ) (dimension : ℕ) : ℕ :=
  ⌊tau * (dimension : ℝ)⌋₊

theorem rHammingRadius_le (tau : ℝ) (htau : 0 ≤ tau) (dimension : ℕ) :
    (rHammingRadius tau dimension : ℝ) ≤ tau * (dimension : ℝ) :=
  Nat.floor_le (mul_nonneg htau (Nat.cast_nonneg dimension))

theorem rHammingRadius_le_dimension (tau : ℝ) (htau : 0 ≤ tau) (htau1 : tau ≤ 1)
    (dimension : ℕ) : rHammingRadius tau dimension ≤ dimension := by
  have hradius := rHammingRadius_le tau htau dimension
  have hdimension : (0 : ℝ) ≤ (dimension : ℝ) := Nat.cast_nonneg dimension
  have hreal : (rHammingRadius tau dimension : ℝ) ≤ (dimension : ℝ) := by
    nlinarith
  exact_mod_cast hreal

theorem rHammingRadius_ratio_tendsto (tau : ℝ) (htau : 0 ≤ tau) :
    Tendsto
      (fun dimension : ℕ =>
        (rHammingRadius tau dimension : ℝ) / (dimension : ℝ))
      atTop (𝓝 tau) := by
  unfold rHammingRadius
  exact (tendsto_nat_floor_mul_div_atTop (R := ℝ) htau).comp
    tendsto_natCast_atTop_atTop

theorem rHammingRadius_binEntropy_tendsto (tau : ℝ) (htau : 0 ≤ tau) :
    Tendsto
      (fun dimension : ℕ =>
        Real.binEntropy
          ((rHammingRadius tau dimension : ℝ) / (dimension : ℝ)))
      atTop (𝓝 (Real.binEntropy tau)) :=
  Real.binEntropy_continuous.continuousAt.tendsto.comp
    (rHammingRadius_ratio_tendsto tau htau)

/-- `D_m ≥ 2^{m·h(r_m/m)} / (m+1)`: the entropy lower bound on the ball size. -/
theorem rHammingBall_card_entropy_lower
    (tau : ℝ) (htau : 0 ≤ tau) (htau1 : tau ≤ 1)
    (dimension : ℕ) (word : HammingWord dimension) :
    Real.exp
        ((dimension : ℝ) *
          Real.binEntropy
            ((rHammingRadius tau dimension : ℝ) / (dimension : ℝ))) /
        ((dimension + 1 : ℕ) : ℝ) ≤
      ((hammingBall dimension (rHammingRadius tau dimension) word).card : ℝ) := by
  calc
    Real.exp
        ((dimension : ℝ) *
          Real.binEntropy
            ((rHammingRadius tau dimension : ℝ) / (dimension : ℝ))) /
        ((dimension + 1 : ℕ) : ℝ) ≤
      (dimension.choose (rHammingRadius tau dimension) : ℝ) :=
        exp_binary_entropy_div_le_choose dimension
          (rHammingRadius tau dimension)
          (rHammingRadius_le_dimension tau htau htau1 dimension)
    _ ≤ _ := by
      exact_mod_cast hammingBall_card_ge_boundary_binomial
        dimension (rHammingRadius tau dimension) word

theorem eventually_rHammingRadius_binEntropy_ge
    (tau : ℝ) (htau : 0 ≤ tau) (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ dimension : ℕ in atTop,
      Real.binEntropy tau - loss ≤
        Real.binEntropy
          ((rHammingRadius tau dimension : ℝ) / (dimension : ℝ)) := by
  have hneighborhood :
      Set.Ioi (Real.binEntropy tau - loss) ∈ 𝓝 (Real.binEntropy tau) :=
    Ioi_mem_nhds (by linarith)
  filter_upwards [rHammingRadius_binEntropy_tendsto tau htau hneighborhood]
    with dimension hdimension
  exact (show Real.binEntropy tau - loss <
    Real.binEntropy
      ((rHammingRadius tau dimension : ℝ) / (dimension : ℝ)) from hdimension).le

/-! ## Part 5: the sampled edge exponent, generic in `(r, beta, eps)`

The sampled Hamming host has `≈ p·2^m` vertices per side and `≈ p²·2^m·D_m`
edges, so its edge exponent is `(1 + h(τ) − 2β)/(1 − β)`, which must beat
`2 − 1/r`.  **The exponent inequality is a hypothesis**: at instantiation it is
discharged from `LedgerR` (`epsR`, `eps_explicit`) with the concrete numerals.
For `r = 3`, `2 − 1/r = 5/3` and `ThreeSampling.threeExponent_product_gt`
is exactly `RExponentGap 3 β ε` unfolded. -/

/-- The `r`-generic exponent hypothesis, in product form (no division):
`(1 − β)(2 − 1/r + ε) < 1 − 2β + h(τ)`. -/
def RExponentGap (r : ℕ) (tau beta eps : ℝ) : Prop :=
  (1 - beta) * ((2 - 1 / (r : ℝ)) + eps) < 1 - 2 * beta + binaryEntropy tau

/-- Ratio form of the exponent hypothesis. -/
theorem rExponent_ratio_gt {r : ℕ} {tau beta eps : ℝ}
    (hbeta : beta < 1) (hgap : RExponentGap r tau beta eps) :
    (2 - 1 / (r : ℝ)) + eps <
      (1 + binaryEntropy tau - 2 * beta) / (1 - beta) := by
  have hpos : 0 < 1 - beta := by linarith
  rw [lt_div_iff₀ hpos]
  unfold RExponentGap at hgap
  nlinarith [hgap]

/-- `log` of the growth rate of `p²·2^m·D_m`, i.e. `(1 − 2β)·log 2 + h_nat(τ)`. -/
noncomputable def sampledREdgeEntropyRate (tau : ℝ) : ℝ :=
  (1 - 2 * (beta : ℝ)) * Real.log 2 + Real.binEntropy tau

theorem sampledREdgeEntropyRate_gt {r : ℕ} (tau : ℝ) (eps : ℝ)
    (hgap : RExponentGap r tau (beta : ℝ) eps) :
    (1 - (beta : ℝ)) * ((2 - 1 / (r : ℝ)) + eps) * Real.log 2 <
      sampledREdgeEntropyRate beta tau := by
  have hentropy :
      Real.binEntropy tau = binaryEntropy tau * Real.log 2 := by
    unfold binaryEntropy
    field_simp [log_two_pos.ne']
  have hlog := log_two_pos
  unfold sampledREdgeEntropyRate
  rw [hentropy]
  unfold RExponentGap at hgap
  nlinarith [hgap, hlog]

theorem sampledREdgeEntropyRate_pos {r : ℕ} (tau : ℝ) (eps : ℝ)
    (hr : 1 ≤ r) (heps0 : 0 ≤ eps) (hbeta1 : (beta : ℝ) < 1)
    (hgap : RExponentGap r tau (beta : ℝ) eps) :
    0 < sampledREdgeEntropyRate beta tau := by
  have h := sampledREdgeEntropyRate_gt beta tau eps hgap
  have hr1 : (1 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrinv : 1 / (r : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have hone : (1 : ℝ) ≤ 2 - 1 / (r : ℝ) + eps := by linarith
  have hlog := log_two_pos
  have hbpos : (0 : ℝ) < 1 - (beta : ℝ) := by linarith
  have hlow : (1 - (beta : ℝ)) * 1 ≤ (1 - (beta : ℝ)) * (2 - 1 / (r : ℝ) + eps) :=
    mul_le_mul_of_nonneg_left hone hbpos.le
  nlinarith [h, hlog, hlow, mul_pos hbpos hlog]

/-! ## Part 6: the whp conjunction, generic in `r` -/

/-- `W_m ≤ 3·p·Q`, `e_m ≥ ½·p²·Q·D_m` and the layer-exclusion event all hold
simultaneously for some retention set, as soon as the three failure
probabilities sum to less than `1`.

Note: the `3 *` in the vertex tail is the *vertex-tail slack factor*, **not**
the arity `r` — it stays `3` for every `r`. -/
theorem exists_good_retention
    {depth dimension r : ℕ} (layerSizes : Fin depth → ℕ) (radius : ℕ)
    (hdimension : 0 < dimension)
    (hparents : ∀ layer, r ≤ layerSizes layer)
    (hbase : ∀ layer,
      (layerSizes layer : ℝ) +
        ((r : ℝ) + 1) * logTwo (((layerSizes layer).choose r + 1 : ℕ) : ℝ) -
          slack * ((layerSizes layer).choose r : ℝ) < -1)
    (hbudget :
      ((2 * depth : ℕ) : ℝ) * Real.exp (-(dimension : ℝ) * Real.log 2) +
        4 / threeExpectedRetainedVertexCount beta dimension +
        (4 / threeExpectedRetainedEdgeCount beta dimension radius +
          8 / (threeRetentionProbability beta dimension *
            ((2 ^ dimension : ℕ) : ℝ))) < 1) :
    ∃ retained : Set (Bool × HammingWord dimension),
      retained ∉
          badRLayersRetentionEvent beta slack r layerSizes dimension ∧
      threeRetainedVertexCount dimension retained <
        3 * threeRetentionProbability beta dimension *
          ((2 ^ dimension : ℕ) : ℝ) ∧
      threeExpectedRetainedEdgeCount beta dimension radius / 2 ≤
        hammingRetainedEdgeCount dimension radius retained := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure
      (threeRetentionMeasure beta dimension) :=
    threeRetentionMeasure_isProbability beta dimension
  set vertexBad : Set (Set (Bool × HammingWord dimension)) :=
    {retained : Set (Bool × HammingWord dimension) |
      3 * threeRetentionProbability beta dimension *
          ((2 ^ dimension : ℕ) : ℝ) ≤
        threeRetainedVertexCount dimension retained} with hvertexBad
  set edgeBad : Set (Set (Bool × HammingWord dimension)) :=
    {retained : Set (Bool × HammingWord dimension) |
      hammingRetainedEdgeCount dimension radius retained <
        threeExpectedRetainedEdgeCount beta dimension radius / 2} with hedgeBad
  set layerBad : Set (Set (Bool × HammingWord dimension)) :=
    badRLayersRetentionEvent beta slack r layerSizes dimension with hlayerBad
  have hlayer :=
    badRLayersRetentionEvent_real_le beta slack layerSizes
      hdimension hparents hbase
  have hvertex :=
    threeRetainedVertexCount_upper_tail_probability_le beta dimension
  have hedge :=
    threeRetainedEdgeCount_lower_tail_probability_le beta dimension radius
  have hunion :
      (threeRetentionMeasure beta dimension).real
          (layerBad ∪ (vertexBad ∪ edgeBad)) < 1 := by
    have h1 :=
      MeasureTheory.measureReal_union_le
        (μ := threeRetentionMeasure beta dimension)
        layerBad (vertexBad ∪ edgeBad)
    have h2 :=
      MeasureTheory.measureReal_union_le
        (μ := threeRetentionMeasure beta dimension)
        vertexBad edgeBad
    linarith [h1, h2, hlayer, hvertex, hedge, hbudget]
  obtain ⟨retained, hretained⟩ :=
    exists_threeRetention_outside_event beta dimension _ hunion
  refine ⟨retained, ?_, ?_, ?_⟩
  · exact fun hmem => hretained (Or.inl hmem)
  · have : retained ∉ vertexBad := fun hmem => hretained (Or.inr (Or.inl hmem))
    simpa [hvertexBad, not_le] using this
  · have : retained ∉ edgeBad := fun hmem => hretained (Or.inr (Or.inr hmem))
    simpa [hedgeBad, not_lt] using this

/-- Restated with the ball-size `D_m` made explicit: `e_m ≥ ½·p²·Q·D_m`.
Arity-free; re-exported here so `AssemblyR` need not import `Sampling3`. -/
theorem exists_good_retention_edge_lower
    {dimension : ℕ} (radius : ℕ)
    (retained : Set (Bool × HammingWord dimension))
    (hedges :
      threeExpectedRetainedEdgeCount beta dimension radius / 2 ≤
        hammingRetainedEdgeCount dimension radius retained) :
    (1 / 2 : ℝ) * threeRetentionProbability beta dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) ≤
      hammingRetainedEdgeCount dimension radius retained :=
  ThreeSampling.exists_good_retention_edge_lower beta radius retained hedges

end RGenericSampling
