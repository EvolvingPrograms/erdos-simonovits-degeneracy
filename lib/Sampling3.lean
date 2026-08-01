import CompactnessAndDegeneracy

/-!
# Sampling and Hamming balls for the `r = 3` degeneracy argument

Port of the published `SamplingAndHammingBalls` section of
`CompactnessAndDegeneracy.lean` (namespace `TwoDegenerateGraphs`, lines
14659–15956, plus the edge-count second moment at 16202–16750 and the
Hamming-radius block at 17594–17685) from `r = 2` to `r = 3`.

Two things change relative to the published development.

* The retention probability `p = 2^{-β m}` is **generic in `β`** here
  (`beta : ℝ≥0`), instead of hardwiring `midpointBeta`.  Downstream the
  intended instantiation is `β ∈ (0.9125, 0.9128517834)` — the window
  narrowed by `research/results_H_lean_entropy.md`; the numeric lemmas below
  are proved under the explicit hypothesis `β ≤ 0.9126`.
* Everything pair-shaped becomes triple-shaped, reusing the counting layer of
  `scratchpad/Profiles3.lean` (copied in verbatim below, since that file is
  not a lake module).

See `research/results_K_lean_sampling.md` for the reuse map.
-/

open TwoDegenerateGraphs Filter Topology
open scoped NNReal



/-!
# Hamming profiles for the 3-ary (triple) layered graph

Port of the `HammingProfiles` counting layer of `CompactnessAndDegeneracy.lean`
(namespace `TwoDegenerateGraphs`, lines 12525–14659) from `r = 2` (children =
pairs of parents) to `r = 3` (children = triples of parents).

Everything up to and including `classifiedBooleanWords_card` in the published
file is already generic (it is stated for an arbitrary classification
`classify : ι → γ`), so it is *reused verbatim* here.  What is ported below is
the pair-specific tail: the bit-type classification, the profile count, and the
two counting bounds

* `(a)` per-coordinate profile count: `#profiles = (M+1)^(4m)` with
  `M = parentCount.choose 3` — `tripleTypeCountProfile_card`;
* `(b)` for a fixed profile, `#child arrays ≤ ∏ C(N_{g,j}, b_{g,j}) ≤ 2^{m M E}`
  — `tripleChildArraysOfRealizedProfile_card_le` and the union over profiles
  `badTripleChildArrays_card_le`.

The parent-type alphabet is `Fin 4`: the type of a triple at a coordinate is
the *number* `j ∈ {0,1,2,3}` of its three parents carrying a `1` there
(conditioning on the type, not on the ordered tuple — see `THEOREM_r3.md`
step 5).  For `r = 2` the published file used `Fin 3` with the encoding
`0 = both false`, `1 = both true`, `2 = mixed`; the counting-relevant content
is identical.
-/


namespace ThreeDegenerateProfiles

/-! ## The triple layer

Copy of `TwoDegenerateGraphs.PairLayer` with `card = 2` replaced by
`card = 3`; definitionally the same as `ThreeDegenerateGraphs.Layer` in
`scratchpad/LayeredGraph.lean`. -/

def TripleLayer (baseSize : ℕ) : ℕ → Type
  | 0 => Fin baseSize
  | i + 1 => {parents : Finset (TripleLayer baseSize i) // parents.card = 3}

instance tripleLayerDecidableEq (baseSize i : ℕ) :
    DecidableEq (TripleLayer baseSize i) := by
  induction i with
  | zero =>
      change DecidableEq (Fin baseSize)
      infer_instance
  | succ i ih =>
      letI := ih
      change DecidableEq
        {parents : Finset (TripleLayer baseSize i) // parents.card = 3}
      infer_instance

noncomputable instance tripleLayerFintype (baseSize i : ℕ) :
    Fintype (TripleLayer baseSize i) := by
  classical
  induction i with
  | zero =>
      change Fintype (Fin baseSize)
      infer_instance
  | succ i ih =>
      letI := ih
      change Fintype
        {parents : Finset (TripleLayer baseSize i) // parents.card = 3}
      infer_instance

theorem tripleLayer_card_zero (baseSize : ℕ) :
    Fintype.card (TripleLayer baseSize 0) = baseSize := by
  change Fintype.card (Fin baseSize) = baseSize
  simp

theorem tripleLayer_card_succ (baseSize i : ℕ) :
    Fintype.card (TripleLayer baseSize (i + 1)) =
      (Fintype.card (TripleLayer baseSize i)).choose 3 := by
  classical
  let layerTriples : Finset (Finset (TripleLayer baseSize i)) :=
    (Finset.univ : Finset (TripleLayer baseSize i)).powersetCard 3
  let equivalence : TripleLayer baseSize (i + 1) ≃ layerTriples :=
    { toFun := fun p =>
        ⟨p.val, by
          apply Finset.mem_powersetCard.mpr
          exact ⟨Finset.subset_univ _, p.property⟩⟩
      invFun := fun p => ⟨p.val, (Finset.mem_powersetCard.mp p.property).2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  calc
    Fintype.card (TripleLayer baseSize (i + 1)) = Fintype.card layerTriples :=
      Fintype.card_congr equivalence
    _ = layerTriples.card := Fintype.card_coe layerTriples
    _ = (Fintype.card (TripleLayer baseSize i)).choose 3 := by
      simp [layerTriples]

theorem tripleLayer_one_card (baseSize : ℕ) :
    Fintype.card (TripleLayer baseSize 1) = baseSize.choose 3 := by
  rw [tripleLayer_card_succ, tripleLayer_card_zero]

/-! ## Coordinate bit types

`(a)` The parent-type alphabet has four letters: `j = #{parents in the triple
carrying a 1 at this coordinate} ∈ {0,1,2,3}`. -/

abbrev TripleBitType := Fin 4

abbrev TripleTypeCountProfile (parentCount dimension : ℕ) :=
  TripleBitType → Fin dimension → Fin (parentCount.choose 3 + 1)

/-- `(a)` There are `(M+1)^(4m)` profiles, `M = parentCount.choose 3`. -/
theorem tripleTypeCountProfile_card (parentCount dimension : ℕ) :
    Fintype.card (TripleTypeCountProfile parentCount dimension) =
      (parentCount.choose 3 + 1) ^ (4 * dimension) := by
  simp [TripleTypeCountProfile, pow_mul, Nat.mul_comm]

/-- The type of a triple at a coordinate: how many of its three parents carry
a `1` there. -/
noncomputable def tripleCoordinateBitType
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (triple : TripleLayer parentCount 1) : TripleBitType := by
  refine ⟨(triple.val.filter
      (fun parent => parents parent coordinate = true)).card, ?_⟩
  exact lt_of_le_of_lt
    (le_trans (Finset.card_filter_le _ _) (le_of_eq triple.property))
    (by norm_num)

noncomputable def tripleTypeGroup
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : TripleBitType) : Finset (TripleLayer parentCount 1) := by
  classical
  exact Finset.univ.filter
    (fun triple => tripleCoordinateBitType parents coordinate triple = bitType)

noncomputable def tripleCoordinateClassification
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension) :
    TripleLayer parentCount 1 × Fin dimension → TripleBitType × Fin dimension :=
  fun index =>
    (tripleCoordinateBitType parents index.2 index.1, index.2)

noncomputable def tripleCoordinateClassificationFiberEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (bitType : TripleBitType) (coordinate : Fin dimension) :
    ClassificationFiber
        (tripleCoordinateClassification parents) (bitType, coordinate) ≃
      ↥(tripleTypeGroup parents coordinate bitType) := by
  classical
  refine
    { toFun := fun index => ⟨index.val.1, ?_⟩
      invFun := fun triple => ⟨(triple.val, coordinate), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have htype := congrArg Prod.fst index.property
    have hcoordinate : index.val.2 = coordinate := by
      simpa [tripleCoordinateClassification] using
        congrArg Prod.snd index.property
    simp only [tripleTypeGroup, Finset.mem_filter,
      Finset.mem_univ, true_and]
    simpa [tripleCoordinateClassification, hcoordinate] using htype
  · have hmembership :
        triple.val ∈
          (Finset.univ.filter
            (fun candidate : TripleLayer parentCount 1 =>
              tripleCoordinateBitType parents coordinate candidate =
                bitType)) := by
      simpa only [tripleTypeGroup] using triple.property
    have htype := (Finset.mem_filter.mp hmembership).2
    change
      (tripleCoordinateBitType parents coordinate triple.val, coordinate) =
        (bitType, coordinate)
    exact Prod.ext htype rfl
  · intro index
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hcoordinate := congrArg Prod.snd index.property
      simpa [tripleCoordinateClassification] using hcoordinate.symm
  · intro triple
    apply Subtype.ext
    rfl

theorem tripleCoordinateClassificationFiber_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (bitType : TripleBitType) (coordinate : Fin dimension) :
    Fintype.card
      (ClassificationFiber
        (tripleCoordinateClassification parents) (bitType, coordinate)) =
      (tripleTypeGroup parents coordinate bitType).card := by
  calc
    Fintype.card
        (ClassificationFiber
          (tripleCoordinateClassification parents) (bitType, coordinate)) =
        Fintype.card ↥(tripleTypeGroup parents coordinate bitType) :=
      Fintype.card_congr
        (tripleCoordinateClassificationFiberEquiv parents bitType coordinate)
    _ = (tripleTypeGroup parents coordinate bitType).card :=
      Fintype.card_coe _

theorem sum_tripleTypeGroup_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : TripleBitType,
      (tripleTypeGroup parents coordinate bitType).card) =
      parentCount.choose 3 := by
  classical
  have hmaps :
      (((Finset.univ : Finset (TripleLayer parentCount 1)) :
        Set (TripleLayer parentCount 1))).MapsTo
          (tripleCoordinateBitType parents coordinate)
          (Finset.univ : Finset TripleBitType) := by
    intro triple _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have htriples :
      (Finset.univ : Finset (TripleLayer parentCount 1)).card =
        parentCount.choose 3 := by
    rw [Finset.card_univ, tripleLayer_one_card]
  calc
    (∑ bitType : TripleBitType,
        (tripleTypeGroup parents coordinate bitType).card) =
      (Finset.univ : Finset (TripleLayer parentCount 1)).card := by
        simpa [tripleTypeGroup] using hpartition.symm
    _ = parentCount.choose 3 := htriples

theorem tripleTypeGroup_card_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : TripleBitType) :
    (tripleTypeGroup parents coordinate bitType).card ≤
      parentCount.choose 3 := by
  classical
  calc
    (tripleTypeGroup parents coordinate bitType).card ≤
      (Finset.univ : Finset (TripleLayer parentCount 1)).card := by
        unfold tripleTypeGroup
        exact Finset.card_filter_le _ _
    _ = parentCount.choose 3 := by
      rw [Finset.card_univ, tripleLayer_one_card]

noncomputable def tripleTypeGroupChildOnes
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : TripleBitType) : Finset (TripleLayer parentCount 1) := by
  classical
  exact (tripleTypeGroup parents coordinate bitType).filter
    (fun triple => children triple coordinate = true)

theorem tripleTypeGroupChildOnes_card_le
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : TripleBitType) :
    (tripleTypeGroupChildOnes parents children coordinate bitType).card ≤
      (tripleTypeGroup parents coordinate bitType).card := by
  classical
  unfold tripleTypeGroupChildOnes
  exact Finset.card_filter_le _ _

def flattenTripleChildArray
    {parentCount dimension : ℕ}
    (children : TripleLayer parentCount 1 → HammingWord dimension) :
    TripleLayer parentCount 1 × Fin dimension → Bool :=
  fun index => children index.1 index.2

theorem tripleChildClassificationOnes_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (bitType : TripleBitType) (coordinate : Fin dimension) :
    (classifiedWordOnes
      (tripleCoordinateClassification parents) (bitType, coordinate)
      (flattenTripleChildArray children)).card =
        (tripleTypeGroupChildOnes parents children coordinate bitType).card := by
  classical
  apply Finset.card_bij (fun index _ => index.1)
  · intro index hindex
    have hclassified :
        index ∈
          (classificationGroup (tripleCoordinateClassification parents)
            (bitType, coordinate)).filter
              (fun candidate =>
                flattenTripleChildArray children candidate = true) := by
      simpa only [classifiedWordOnes] using hindex
    have hparts := Finset.mem_filter.mp hclassified
    have hgroup := (Finset.mem_filter.mp hparts.1).2
    have htype := congrArg Prod.fst hgroup
    have hcoordinate := congrArg Prod.snd hgroup
    have hcoord : index.2 = coordinate := by
      simpa [tripleCoordinateClassification] using hcoordinate
    simp only [tripleTypeGroupChildOnes, Finset.mem_filter]
    constructor
    · simp only [tripleTypeGroup, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simpa [tripleCoordinateClassification, hcoord] using htype
    · simpa [flattenTripleChildArray, hcoord] using hparts.2
  · intro first hfirst second hsecond hequal
    apply Prod.ext
    · exact hequal
    · have hfirst_group := (Finset.mem_filter.mp hfirst).1
      have hsecond_group := (Finset.mem_filter.mp hsecond).1
      have hfirst_class := (Finset.mem_filter.mp hfirst_group).2
      have hsecond_class := (Finset.mem_filter.mp hsecond_group).2
      have hfirst_coordinate := congrArg Prod.snd hfirst_class
      have hsecond_coordinate := congrArg Prod.snd hsecond_class
      simpa [tripleCoordinateClassification] using
        hfirst_coordinate.trans hsecond_coordinate.symm
  · intro triple htriple
    refine ⟨(triple, coordinate), ?_, rfl⟩
    have htriple_parts := Finset.mem_filter.mp htriple
    have htriple_type := (Finset.mem_filter.mp htriple_parts.1).2
    change
      (triple, coordinate) ∈
        (classificationGroup (tripleCoordinateClassification parents)
          (bitType, coordinate)).filter
            (fun index => flattenTripleChildArray children index = true)
    apply Finset.mem_filter.mpr
    constructor
    · unfold classificationGroup
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact Prod.ext htriple_type rfl
    · exact htriple_parts.2

noncomputable def tripleChildCountProfile
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension) :
    TripleTypeCountProfile parentCount dimension := by
  intro bitType coordinate
  refine
    ⟨(tripleTypeGroupChildOnes parents children coordinate bitType).card, ?_⟩
  have hones := tripleTypeGroupChildOnes_card_le
    parents children coordinate bitType
  have hgroup := tripleTypeGroup_card_le parents coordinate bitType
  omega

noncomputable def tripleChildArraysOfProfile
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : TripleTypeCountProfile parentCount dimension) :
    Finset (TripleLayer parentCount 1 → HammingWord dimension) := by
  classical
  exact Finset.univ.filter
    (fun children => tripleChildCountProfile parents children = profile)

noncomputable def tripleChildArraysOfProfileEquiv
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : TripleTypeCountProfile parentCount dimension) :
    ↥(tripleChildArraysOfProfile parents profile) ≃
      ↥(classifiedBooleanWords
        (tripleCoordinateClassification parents)
        (fun index : TripleBitType × Fin dimension =>
          (profile index.1 index.2).val)) := by
  classical
  refine
    { toFun := fun children =>
        ⟨flattenTripleChildArray children.val, ?_⟩
      invFun := fun word =>
        ⟨fun triple coordinate => word.val (triple, coordinate), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership := children.property
    unfold tripleChildArraysOfProfile at hmembership
    have hprofile := (Finset.mem_filter.mp hmembership).2
    simp only [classifiedBooleanWords, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rintro ⟨bitType, coordinate⟩
    rw [tripleChildClassificationOnes_card]
    have hcount := congrArg
      (fun candidate : TripleTypeCountProfile parentCount dimension =>
        (candidate bitType coordinate).val) hprofile
    simpa [tripleChildCountProfile] using hcount
  · simp only [tripleChildArraysOfProfile, Finset.mem_filter,
      Finset.mem_univ, true_and]
    funext bitType
    funext coordinate
    apply Fin.ext
    change
      (tripleTypeGroupChildOnes parents
        (fun triple coordinate => word.val (triple, coordinate))
        coordinate bitType).card = (profile bitType coordinate).val
    have hmembership := word.property
    unfold classifiedBooleanWords at hmembership
    have hprofile :=
      (Finset.mem_filter.mp hmembership).2 (bitType, coordinate)
    rw [← tripleChildClassificationOnes_card]
    have hflatten :
        flattenTripleChildArray
          (fun triple coordinate => word.val (triple, coordinate)) =
            word.val := by
      funext index
      rcases index with ⟨triple, coordinate⟩
      rfl
    rw [hflatten]
    exact hprofile
  · intro children
    apply Subtype.ext
    funext triple
    funext coordinate
    rfl
  · intro word
    apply Subtype.ext
    funext index
    rcases index with ⟨triple, coordinate⟩
    rfl

/-- `(b)` For a fixed profile, the child arrays realizing it are counted
exactly by a product of binomial coefficients. -/
theorem tripleChildArraysOfProfile_card
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : TripleTypeCountProfile parentCount dimension) :
    (tripleChildArraysOfProfile parents profile).card =
      ∏ index : TripleBitType × Fin dimension,
        ((tripleTypeGroup parents index.2 index.1).card).choose
          (profile index.1 index.2).val := by
  calc
    (tripleChildArraysOfProfile parents profile).card =
      Fintype.card ↥(tripleChildArraysOfProfile parents profile) :=
        (Fintype.card_coe _).symm
    _ = Fintype.card
      ↥(classifiedBooleanWords
        (tripleCoordinateClassification parents)
        (fun index : TripleBitType × Fin dimension =>
          (profile index.1 index.2).val)) :=
        Fintype.card_congr
          (tripleChildArraysOfProfileEquiv parents profile)
    _ = (classifiedBooleanWords
        (tripleCoordinateClassification parents)
        (fun index : TripleBitType × Fin dimension =>
          (profile index.1 index.2).val)).card :=
        Fintype.card_coe _
    _ = ∏ index : TripleBitType × Fin dimension,
        (Fintype.card
          (ClassificationFiber
            (tripleCoordinateClassification parents) index)).choose
          (profile index.1 index.2).val :=
        classifiedBooleanWords_card
          (tripleCoordinateClassification parents)
          (fun index : TripleBitType × Fin dimension =>
            (profile index.1 index.2).val)
    _ = ∏ index : TripleBitType × Fin dimension,
        ((tripleTypeGroup parents index.2 index.1).card).choose
          (profile index.1 index.2).val := by
      apply Finset.prod_congr rfl
      rintro ⟨bitType, coordinate⟩ _
      rw [tripleCoordinateClassificationFiber_card]

/-! ## Empirical conditional entropy and the `2^{mME}` bound -/

noncomputable def tripleCoordinateConditionalEntropy
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : ℝ :=
  ∑ bitType : TripleBitType,
    ((tripleTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 3 : ℝ) *
      binaryEntropy
        (((tripleTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
          ((tripleTypeGroup parents coordinate bitType).card : ℝ))

noncomputable def tripleChildArrayEntropy
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    tripleCoordinateConditionalEntropy parents children coordinate) /
      (dimension : ℝ)

theorem tripleCoordinateConditionalEntropy_mass
    {parentCount dimension : ℕ} (hparents : 3 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (parentCount.choose 3 : ℝ) *
        tripleCoordinateConditionalEntropy parents children coordinate =
      ∑ bitType : TripleBitType,
        ((tripleTypeGroup parents coordinate bitType).card : ℝ) *
          binaryEntropy
            (((tripleTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((tripleTypeGroup parents coordinate bitType).card : ℝ)) := by
  have htriple : 0 < (parentCount.choose 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  unfold tripleCoordinateConditionalEntropy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bitType _
  field_simp [htriple.ne']

theorem tripleCoordinateConditionalEntropy_log_mass
    {parentCount dimension : ℕ} (hparents : 3 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : TripleBitType,
      ((tripleTypeGroup parents coordinate bitType).card : ℝ) *
        Real.binEntropy
          (((tripleTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
            ((tripleTypeGroup parents coordinate bitType).card : ℝ))) =
      (parentCount.choose 3 : ℝ) * Real.log 2 *
        tripleCoordinateConditionalEntropy parents children coordinate := by
  calc
    (∑ bitType : TripleBitType,
        ((tripleTypeGroup parents coordinate bitType).card : ℝ) *
          Real.binEntropy
            (((tripleTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((tripleTypeGroup parents coordinate bitType).card : ℝ))) =
      (∑ bitType : TripleBitType,
        ((tripleTypeGroup parents coordinate bitType).card : ℝ) *
          binaryEntropy
            (((tripleTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((tripleTypeGroup parents coordinate bitType).card : ℝ))) *
        Real.log 2 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro bitType _
          unfold binaryEntropy
          field_simp [Real.log_pos (by norm_num : (1:ℝ) < 2) |>.ne']
    _ = (parentCount.choose 3 : ℝ) * Real.log 2 *
        tripleCoordinateConditionalEntropy parents children coordinate := by
      rw [← tripleCoordinateConditionalEntropy_mass
        hparents parents children coordinate]
      ring

theorem tripleChildGroup_choose_product_entropy_bound
    {parentCount dimension : ℕ} (hparents : 3 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension) :
    (∏ index : TripleBitType × Fin dimension,
      ((tripleTypeGroup parents index.2 index.1).card).choose
        ((tripleTypeGroupChildOnes parents children
          index.2 index.1).card) : ℝ) ≤
      Real.exp
        ((parentCount.choose 3 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            tripleCoordinateConditionalEntropy parents children
              coordinate)) := by
  have hproduct := choose_product_le_exp_binary_entropy
    (ι := TripleBitType × Fin dimension)
    (fun index => (tripleTypeGroup parents index.2 index.1).card)
    (fun index =>
      (tripleTypeGroupChildOnes parents children index.2 index.1).card)
    (fun index => tripleTypeGroupChildOnes_card_le
      parents children index.2 index.1)
  have hsum :
      (∑ index : TripleBitType × Fin dimension,
        ((tripleTypeGroup parents index.2 index.1).card : ℝ) *
          Real.binEntropy
            (((tripleTypeGroupChildOnes parents children
                index.2 index.1).card : ℝ) /
              ((tripleTypeGroup parents index.2 index.1).card : ℝ))) =
        (parentCount.choose 3 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            tripleCoordinateConditionalEntropy parents children
              coordinate) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [tripleCoordinateConditionalEntropy_log_mass
      hparents parents children]
    rw [Finset.mul_sum]
  rw [hsum] at hproduct
  exact hproduct

/-- `(b)` The child arrays sharing the profile of a given child array number at
most `2^{m M E}` where `E` is that array's average conditional entropy. -/
theorem tripleChildArraysOfRealizedProfile_card_le
    {parentCount dimension : ℕ} (hparents : 3 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension) :
    ((tripleChildArraysOfProfile parents
        (tripleChildCountProfile parents children)).card : ℝ) ≤
      Real.exp
        ((parentCount.choose 3 : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            tripleCoordinateConditionalEntropy parents children
              coordinate)) := by
  have hcard :
      ((tripleChildArraysOfProfile parents
        (tripleChildCountProfile parents children)).card : ℝ) =
        ∏ index : TripleBitType × Fin dimension,
          (((tripleTypeGroup parents index.2 index.1).card).choose
            ((tripleTypeGroupChildOnes parents children
              index.2 index.1).card) : ℝ) := by
    exact_mod_cast
      tripleChildArraysOfProfile_card parents
        (tripleChildCountProfile parents children)
  rw [hcard]
  exact tripleChildGroup_choose_product_entropy_bound
    hparents parents children

/-! ## The union over profiles

`(a) + (b)`: the low-entropy ("bad") child arrays number at most
`(M+1)^{4m} · 2^{m M · threshold}`, `M = parentCount.choose 3`. -/

noncomputable def badTripleChildArrays
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (threshold : ℝ) :
    Finset (TripleLayer parentCount 1 → HammingWord dimension) := by
  classical
  exact Finset.univ.filter
    (fun children => tripleChildArrayEntropy parents children ≤ threshold)

theorem badTripleChildArrays_card_le
    {parentCount dimension : ℕ}
    (hparents : 3 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (threshold : ℝ) :
    ((badTripleChildArrays parents threshold).card : ℝ) ≤
      (((parentCount.choose 3 + 1) ^ (4 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 3 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold) := by
  classical
  let bound : ℝ :=
    Real.exp
      ((parentCount.choose 3 : ℝ) * Real.log 2 *
        (dimension : ℝ) * threshold)
  have hbound_nonneg : 0 ≤ bound := by
    dsimp [bound]
    exact (Real.exp_pos _).le
  have hmaps :
      ((badTripleChildArrays parents threshold :
        Finset (TripleLayer parentCount 1 → HammingWord dimension)) :
        Set (TripleLayer parentCount 1 → HammingWord dimension)).MapsTo
        (tripleChildCountProfile parents)
        (Finset.univ :
          Finset (TripleTypeCountProfile parentCount dimension)) := by
    intro children _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (profile : TripleTypeCountProfile parentCount dimension) :
      (((badTripleChildArrays parents threshold).filter
        (fun children =>
          tripleChildCountProfile parents children = profile)).card : ℝ) ≤
        bound := by
    by_cases hnonempty :
        ((badTripleChildArrays parents threshold).filter
          (fun children =>
            tripleChildCountProfile parents children = profile)).Nonempty
    · obtain ⟨children, hchildren⟩ := hnonempty
      have hparts := Finset.mem_filter.mp hchildren
      have hprofile : tripleChildCountProfile parents children = profile :=
        hparts.2
      have hbad : tripleChildArrayEntropy parents children ≤ threshold := by
        have hmembership :
            children ∈
              (Finset.univ.filter
                (fun candidate : TripleLayer parentCount 1 →
                    HammingWord dimension =>
                  tripleChildArrayEntropy parents candidate ≤ threshold)) := by
          simpa only [badTripleChildArrays] using hparts.1
        exact (Finset.mem_filter.mp hmembership).2
      have hsubset :
          (badTripleChildArrays parents threshold).filter
              (fun candidate =>
                tripleChildCountProfile parents candidate = profile) ⊆
            tripleChildArraysOfProfile parents profile := by
        intro candidate hcandidate
        have hcandidate_profile := (Finset.mem_filter.mp hcandidate).2
        unfold tripleChildArraysOfProfile
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hcandidate_profile⟩
      have hcard :
          (((badTripleChildArrays parents threshold).filter
            (fun candidate =>
              tripleChildCountProfile parents candidate =
                profile)).card : ℝ) ≤
            ((tripleChildArraysOfProfile parents profile).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      have hrealized :
          ((tripleChildArraysOfProfile parents profile).card : ℝ) ≤
            Real.exp
              ((parentCount.choose 3 : ℝ) * Real.log 2 *
                (∑ coordinate : Fin dimension,
                  tripleCoordinateConditionalEntropy
                    parents children coordinate)) := by
        rw [← hprofile]
        exact tripleChildArraysOfRealizedProfile_card_le
          hparents parents children
      have hdimension_real : 0 < (dimension : ℝ) := by
        exact_mod_cast hdimension
      have hsum :
          (∑ coordinate : Fin dimension,
            tripleCoordinateConditionalEntropy parents children
              coordinate) ≤ (dimension : ℝ) * threshold := by
        unfold tripleChildArrayEntropy at hbad
        have hcleared := (div_le_iff₀ hdimension_real).mp hbad
        nlinarith
      have hcoefficient :
          0 ≤ (parentCount.choose 3 : ℝ) * Real.log 2 :=
        mul_nonneg (Nat.cast_nonneg _)
          (Real.log_pos (by norm_num : (1:ℝ) < 2)).le
      have hexponential :
          Real.exp
              ((parentCount.choose 3 : ℝ) * Real.log 2 *
                (∑ coordinate : Fin dimension,
                  tripleCoordinateConditionalEntropy
                    parents children coordinate)) ≤ bound := by
        dsimp [bound]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hsum hcoefficient]
      exact hcard.trans (hrealized.trans hexponential)
    · have hempty :
          (badTripleChildArrays parents threshold).filter
            (fun children =>
              tripleChildCountProfile parents children = profile) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hnonempty
      simpa [hempty] using hbound_nonneg
  calc
    ((badTripleChildArrays parents threshold).card : ℝ) =
        ∑ profile : TripleTypeCountProfile parentCount dimension,
          (((badTripleChildArrays parents threshold).filter
            (fun children =>
              tripleChildCountProfile parents children =
                profile)).card : ℝ) := by
      exact_mod_cast hpartition
    _ ≤ ∑ _profile : TripleTypeCountProfile parentCount dimension, bound := by
      exact Finset.sum_le_sum (fun profile _ => hfiber profile)
    _ = (((parentCount.choose 3 + 1) ^ (4 * dimension) : ℕ) : ℝ) *
          Real.exp
            ((parentCount.choose 3 : ℝ) * Real.log 2 *
              (dimension : ℝ) * threshold) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        tripleTypeCountProfile_card]

/-! ## `(c)` The union-bound exponent

Parent arrays number `2^{mL}`; profiles `(M+1)^{4m}`; bad child arrays per
profile `2^{mM(β-δ)}`; each such child array survives retention with
probability `p^M = 2^{-βmM}`.  Multiplying gives exactly

`exp( m · log 2 · [ L + 4·log₂(M+1) − δ·M ] )`,  `M = parentCount.choose 3`,

which is the `r = 3` form of `THEOREM_r3.md` step 5.  This is an identity, so
it is proved here for an arbitrary retention exponent `beta` and slack `slack`
(the published `r = 2` version hardwires `midpointBeta`/`entropySlack`). -/
theorem badTripleLayerRetentionBound_eq_exp
    (parentCount dimension : ℕ) (beta slack : ℝ) :
    ((((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
      (((parentCount.choose 3 + 1) ^ (4 * dimension) : ℕ) : ℝ) *
      Real.exp
        ((parentCount.choose 3 : ℝ) * Real.log 2 *
          (dimension : ℝ) * (beta - slack))) *
        Real.exp (-(beta * (dimension : ℝ) * Real.log 2)) ^
          (parentCount.choose 3)) =
      Real.exp
        ((dimension : ℝ) * Real.log 2 *
          ((parentCount : ℝ) +
            4 * logTwo ((parentCount.choose 3 + 1 : ℕ) : ℝ) -
              slack * (parentCount.choose 3 : ℝ))) := by
  have hparent :
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ)) =
        Real.exp
          (((dimension * parentCount : ℕ) : ℝ) * Real.log 2) := by
    calc
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ)) =
          (2 : ℝ) ^ (dimension * parentCount) := by norm_cast
      _ = Real.exp
          (((dimension * parentCount : ℕ) : ℝ) * Real.log 2) := by
            rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
  have hprofile :
      (((parentCount.choose 3 + 1) ^ (4 * dimension) : ℕ) : ℝ) =
        Real.exp
          (((4 * dimension : ℕ) : ℝ) *
            Real.log ((parentCount.choose 3 + 1 : ℕ) : ℝ)) := by
    calc
      (((parentCount.choose 3 + 1) ^ (4 * dimension) : ℕ) : ℝ) =
          (((parentCount.choose 3 + 1 : ℕ) : ℝ)) ^ (4 * dimension) := by
            norm_cast
      _ = Real.exp
          (((4 * dimension : ℕ) : ℝ) *
            Real.log ((parentCount.choose 3 + 1 : ℕ) : ℝ)) := by
            rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hretention :
      Real.exp (-(beta * (dimension : ℝ) * Real.log 2)) ^
          (parentCount.choose 3) =
        Real.exp
          ((parentCount.choose 3 : ℝ) *
            (-(beta * (dimension : ℝ) * Real.log 2))) := by
    rw [Real.exp_nat_mul]
  rw [hparent, hprofile, hretention,
    ← Real.exp_add, ← Real.exp_add, ← Real.exp_add]
  apply congrArg Real.exp
  unfold logTwo
  push_cast
  field_simp [Real.log_ne_zero_of_pos_of_ne_one (by norm_num : (0:ℝ) < 2)
    (by norm_num : (2:ℝ) ≠ 1)]
  ring

end ThreeDegenerateProfiles

namespace ThreeSampling

open ThreeDegenerateProfiles

variable (beta : ℝ≥0) (slack : ℝ)


/-- The `r = 3` Hamming radius fraction. -/
noncomputable def tauThree : ℝ := 2 / 5

theorem binaryEntropy_tauThree_eq :
    binaryEntropy tauThree =
      (5 * Real.log 5 - 3 * Real.log 3 - 2 * Real.log 2) / (5 * Real.log 2) := by
  have h5 : (0:ℝ) < 5 := by norm_num
  have h2 : (0:ℝ) < 2 := by norm_num
  have h3 : (0:ℝ) < 3 := by norm_num
  have hone : (1 : ℝ) - tauThree = 3 / 5 := by unfold tauThree; norm_num
  unfold binaryEntropy tauThree Real.binEntropy
  rw [show ((2:ℝ)/5)⁻¹ = 5 / 2 by norm_num,
      show (1 - (2:ℝ)/5) = 3/5 by norm_num,
      show ((3:ℝ)/5)⁻¹ = 5 / 3 by norm_num,
      Real.log_div h5.ne' h2.ne', Real.log_div h5.ne' h3.ne']
  field_simp
  ring

set_option exponentiation.threshold 400 in
/-- `log₂ (5^275 / 3^165) ≥ 377`, the integer certificate behind the
rational lower bound `h(2/5) ≥ 267/275`. -/
theorem pow_certificate : (2:ℝ) ^ (377:ℕ) * 3 ^ (165:ℕ) ≤ 5 ^ (275:ℕ) := by
  have : (2:ℕ) ^ (377:ℕ) * 3 ^ (165:ℕ) ≤ 5 ^ (275:ℕ) := by decide
  exact_mod_cast this

theorem binaryEntropy_tauThree_ge : (267 : ℝ) / 275 ≤ binaryEntropy tauThree := by
  have hlog2 := log_two_pos
  have hkey : (377 : ℝ) * Real.log 2 ≤ 55 * (5 * Real.log 5 - 3 * Real.log 3) := by
    have h := Real.log_le_log (by positivity) pow_certificate
    rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow,
      Real.log_pow] at h
    push_cast at h
    linarith
  rw [binaryEntropy_tauThree_eq, le_div_iff₀ (by positivity)]
  linarith

/-! ## The `r = 3` exponent inequality

The sampled Hamming host has `≈ p·2^m` vertices per side and
`≈ p²·2^m·D_m` edges with `D_m = 2^{(h(τ)+o(1))m}`, so its edge exponent is
`(1 + h(τ) − 2β)/(1 − β)`.  For `r = 3` this has to beat `5/3`
(`= 2 − 1/3`, the `K_{3,…}`-free exponent to be contradicted).  With
`τ = 2/5` and `β` in the narrowed window of `results_H_lean_entropy.md`
this holds with room `ε = 1/4000`. -/

/-- Product form of the exponent inequality (no division). -/
theorem threeExponent_product_gt (beta eps : ℝ)
    (hbeta : beta ≤ 9126 / 10000) (heps : eps ≤ 1 / 4000) (heps0 : 0 < eps) :
    (1 - beta) * (5 / 3 + eps) < 1 - 2 * beta + binaryEntropy tauThree := by
  have hH := binaryEntropy_tauThree_ge
  nlinarith [hH, hbeta, heps, heps0, mul_nonneg (sub_nonneg.mpr hbeta) heps0.le]

/-- Ratio form: the sampled edge exponent exceeds `5/3 + ε`. -/
theorem threeExponent_ratio_gt (beta eps : ℝ)
    (_ : 9125 / 10000 < beta) (hbeta : beta ≤ 9126 / 10000)
    (heps : eps ≤ 1 / 4000) (heps0 : 0 < eps) :
    5 / 3 + eps <
      (1 + binaryEntropy tauThree - 2 * beta) / (1 - beta) := by
  have hpos : 0 < 1 - beta := by linarith
  rw [lt_div_iff₀ hpos]
  have := threeExponent_product_gt beta eps hbeta heps heps0
  nlinarith [this]


noncomputable def threeRetentionProbability (dimension : ℕ) : ℝ :=
  Real.exp (-((beta:ℝ) * (dimension : ℝ) * Real.log 2))

theorem threeRetentionProbability_pos (dimension : ℕ) :
    0 < threeRetentionProbability beta dimension := by
  unfold threeRetentionProbability
  exact Real.exp_pos _

theorem threeRetentionProbability_le_one (dimension : ℕ) :
    threeRetentionProbability beta dimension ≤ 1 := by
  unfold threeRetentionProbability
  apply Real.exp_le_one_iff.mpr
  have hproduct :
      0 ≤ (beta:ℝ) * (dimension : ℝ) * Real.log 2 :=
    mul_nonneg
      (mul_nonneg beta.coe_nonneg (Nat.cast_nonneg dimension))
      log_two_pos.le
  linarith

theorem threeRetentionProbability_mul_wordCount_eq_exp
    (dimension : ℕ) :
    threeRetentionProbability beta dimension *
        ((2 ^ dimension : ℕ) : ℝ) =
      Real.exp
        ((1 - (beta:ℝ)) * (dimension : ℝ) * Real.log 2) := by
  have hwords :
      ((2 ^ dimension : ℕ) : ℝ) =
        Real.exp ((dimension : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_cast
  unfold threeRetentionProbability
  rw [hwords, ← Real.exp_add]
  congr 1
  ring

theorem threeRetentionProbability_sq_mul_wordCount_eq_exp
    (dimension : ℕ) :
    threeRetentionProbability beta dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ) =
      Real.exp
        ((1 - 2 * (beta:ℝ)) * (dimension : ℝ) * Real.log 2) := by
  have hwords :
      ((2 ^ dimension : ℕ) : ℝ) =
        Real.exp ((dimension : ℝ) * Real.log 2) := by
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num)]
    norm_cast
  unfold threeRetentionProbability
  rw [hwords, ← Real.exp_nat_mul, ← Real.exp_add]
  congr 1
  push_cast
  ring

theorem threeRetentionProbability_mul_wordCount_tendsto_atTop
    (hbeta : (beta:ℝ) < 1) :
    Tendsto
      (fun dimension : ℕ =>
        threeRetentionProbability beta dimension *
          ((2 ^ dimension : ℕ) : ℝ))
      atTop atTop := by
  have hrate : 0 < (1 - (beta:ℝ)) * Real.log 2 :=
    mul_pos (sub_pos.mpr hbeta) log_two_pos
  have hlinear :
      Tendsto
        (fun dimension : ℕ =>
          ((1 - (beta:ℝ)) * Real.log 2) * (dimension : ℝ))
        atTop atTop :=
    tendsto_natCast_atTop_atTop.const_mul_atTop hrate
  have hexponential := Real.tendsto_exp_atTop.comp hlinear
  apply hexponential.congr'
  filter_upwards [] with dimension
  simp only [Function.comp_apply]
  rw [threeRetentionProbability_mul_wordCount_eq_exp]
  congr 1
  ring

theorem threeRetentionProbability_mul_wordCount_inv_tendsto_zero
    (hbeta : (beta:ℝ) < 1) :
    Tendsto
      (fun dimension : ℕ =>
        1 / (threeRetentionProbability beta dimension *
          ((2 ^ dimension : ℕ) : ℝ)))
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    (threeRetentionProbability_mul_wordCount_tendsto_atTop beta hbeta)
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]


noncomputable def threeRetentionParameter (dimension : ℕ) : unitInterval :=
  ⟨threeRetentionProbability beta dimension,
    threeRetentionProbability_pos beta dimension |>.le,
    threeRetentionProbability_le_one beta dimension⟩

noncomputable def threeRetentionMeasure (dimension : ℕ) :
    MeasureTheory.Measure (Set (Bool × HammingWord dimension)) :=
  ProbabilityTheory.setBernoulli Set.univ
    (threeRetentionParameter beta dimension)

theorem threeRetentionMeasure_isProbability (dimension : ℕ) :
    MeasureTheory.IsProbabilityMeasure
      (threeRetentionMeasure beta dimension) := by
  unfold threeRetentionMeasure
  infer_instance

theorem threeRetentionMeasure_integrable
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    MeasureTheory.Integrable observable
      (threeRetentionMeasure beta dimension) := by
  letI : MeasureTheory.IsProbabilityMeasure
      (threeRetentionMeasure beta dimension) :=
    threeRetentionMeasure_isProbability beta dimension
  exact MeasureTheory.Integrable.of_finite

theorem threeRetentionMeasure_memLp_two
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    MeasureTheory.MemLp observable 2
      (threeRetentionMeasure beta dimension) := by
  apply (MeasureTheory.memLp_two_iff_integrable_sq
    (threeRetentionMeasure_integrable beta dimension observable).aestronglyMeasurable).mpr
  exact threeRetentionMeasure_integrable beta dimension
    (fun retained => observable retained ^ 2)

theorem threeRetentionMeasure_integral_eq_sum
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ) :
    (∫ retained,
      observable retained ∂threeRetentionMeasure beta dimension) =
      ∑ retained : Set (Bool × HammingWord dimension),
        (threeRetentionMeasure beta dimension).real {retained} *
          observable retained := by
  classical
  simpa [smul_eq_mul] using
    (MeasureTheory.integral_fintype
      (threeRetentionMeasure_integrable beta dimension observable))

open Classical in
theorem threeRetentionMeasure_real_event_eq_sum
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension))) :
    (threeRetentionMeasure beta dimension).real event =
      ∑ retained : Set (Bool × HammingWord dimension),
        if retained ∈ event then
          (threeRetentionMeasure beta dimension).real {retained}
        else 0 := by
  classical
  letI : MeasureTheory.IsProbabilityMeasure
      (threeRetentionMeasure beta dimension) :=
    threeRetentionMeasure_isProbability beta dimension
  let support : Finset (Set (Bool × HammingWord dimension)) :=
    Finset.univ.filter (fun retained => retained ∈ event)
  have hsupport :
      (support : Set (Set (Bool × HammingWord dimension))) = event := by
    ext retained
    simp [support]
  calc
    (threeRetentionMeasure beta dimension).real event =
        (threeRetentionMeasure beta dimension).real support := by
      rw [hsupport]
    _ = ∑ retained ∈ support,
        (threeRetentionMeasure beta dimension).real {retained} := by
      exact (MeasureTheory.sum_measureReal_singleton support).symm
    _ = ∑ retained : Set (Bool × HammingWord dimension),
        if retained ∈ event then
          (threeRetentionMeasure beta dimension).real {retained}
        else 0 := by
      rw [← Finset.sum_filter]

open Classical in
theorem threeRetentionMeasure_integral_event_indicator
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension))) :
    (∫ retained,
      (if retained ∈ event then (1 : ℝ) else 0)
        ∂threeRetentionMeasure beta dimension) =
      (threeRetentionMeasure beta dimension).real event := by
  rw [threeRetentionMeasure_integral_eq_sum,
    threeRetentionMeasure_real_event_eq_sum]
  apply Finset.sum_congr rfl
  intro retained _
  split_ifs <;> simp

theorem threeRetentionMeasure_real_deviation_le
    (dimension : ℕ)
    (observable : Set (Bool × HammingWord dimension) → ℝ)
    (threshold : ℝ) (hthreshold : 0 < threshold) :
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |observable retained -
            (∫ candidate,
              observable candidate ∂threeRetentionMeasure beta dimension)|} ≤
      ProbabilityTheory.variance observable
          (threeRetentionMeasure beta dimension) /
        threshold ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure
      (threeRetentionMeasure beta dimension) :=
    threeRetentionMeasure_isProbability beta dimension
  have hchebyshev :=
    ProbabilityTheory.meas_ge_le_variance_div_sq
      (threeRetentionMeasure_memLp_two beta dimension observable)
      hthreshold
  have hreal := ENNReal.toReal_mono ENNReal.ofReal_ne_top hchebyshev
  have hnonnegative :
      0 ≤ ProbabilityTheory.variance observable
          (threeRetentionMeasure beta dimension) /
        threshold ^ 2 := by
    exact div_nonneg
      (ProbabilityTheory.variance_nonneg observable
        (threeRetentionMeasure beta dimension))
      (sq_nonneg threshold)
  simpa [MeasureTheory.Measure.real, ENNReal.toReal_ofReal hnonnegative]
    using hreal

theorem threeRetentionMeasure_real_contains_finset
    (dimension : ℕ)
    (required : Finset (Bool × HammingWord dimension)) :
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        ∀ vertex ∈ required, vertex ∈ retained} =
      threeRetentionProbability beta dimension ^ required.card := by
  classical
  have hpreimage :
      (fun membership : (Bool × HammingWord dimension) → Prop =>
        {vertex | membership vertex}) ⁻¹'
          {retained : Set (Bool × HammingWord dimension) |
            ∀ vertex ∈ required, vertex ∈ retained} =
        Set.pi (required : Set (Bool × HammingWord dimension))
          (fun _ => ({True} : Set Prop)) := by
    ext membership
    simp
  have hmeasure :
      threeRetentionMeasure beta dimension
          {retained : Set (Bool × HammingWord dimension) |
            ∀ vertex ∈ required, vertex ∈ retained} =
        (↑(unitInterval.toNNReal
          (threeRetentionParameter beta dimension)) : ENNReal) ^
            required.card := by
    unfold threeRetentionMeasure
    rw [ProbabilityTheory.setBernoulli_apply']
    rw [hpreimage]
    rw [MeasureTheory.Measure.infinitePi_pi]
    · simp
    · intro vertex _
      measurability
  change
    ENNReal.toReal
        (threeRetentionMeasure beta dimension
          {retained : Set (Bool × HammingWord dimension) |
            ∀ vertex ∈ required, vertex ∈ retained}) = _
  rw [hmeasure, ENNReal.toReal_pow]
  simp [threeRetentionParameter]

theorem threeRetentionMeasure_real_contains_pair
    (dimension : ℕ)
    (first second : Bool × HammingWord dimension)
    (hdistinct : first ≠ second) :
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        first ∈ retained ∧ second ∈ retained} =
      threeRetentionProbability beta dimension ^ 2 := by
  classical
  simpa [hdistinct] using
    threeRetentionMeasure_real_contains_finset beta dimension {first, second}

theorem threeRetentionMeasure_real_contains_vertex
    (dimension : ℕ)
    (vertex : Bool × HammingWord dimension) :
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        vertex ∈ retained} =
      threeRetentionProbability beta dimension := by
  classical
  simpa using
    threeRetentionMeasure_real_contains_finset beta dimension {vertex}

theorem threeRetentionMeasure_real_contains_edgePair
    (dimension : ℕ)
    (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} =
      threeRetentionProbability beta dimension ^
        (2 +
          (if firstLeft = secondLeft then 0 else 1) +
          (if firstRight = secondRight then 0 else 1)) := by
  classical
  let required : Finset (Bool × HammingWord dimension) :=
    {(false, firstLeft), (true, firstRight),
      (false, secondLeft), (true, secondRight)}
  have hevent :
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} =
      {retained : Set (Bool × HammingWord dimension) |
        ∀ vertex ∈ required, vertex ∈ retained} := by
    ext retained
    simp [required, and_left_comm]
  rw [hevent, threeRetentionMeasure_real_contains_finset]
  by_cases hleft : firstLeft = secondLeft <;>
    by_cases hright : firstRight = secondRight
  · subst secondLeft
    subst secondRight
    simp [required]
  · subst secondLeft
    simp [required, hright]
  · subst secondRight
    simp [required, hleft]
  · simp [required, hleft, hright]

theorem threeRetentionMeasure_real_contains_edgePair_le
    (dimension : ℕ)
    (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        (false, firstLeft) ∈ retained ∧
        (true, firstRight) ∈ retained ∧
        (false, secondLeft) ∈ retained ∧
        (true, secondRight) ∈ retained} ≤
      threeRetentionProbability beta dimension ^ 4 +
        (if firstLeft = secondLeft then
          threeRetentionProbability beta dimension ^ 3 else 0) +
        (if firstRight = secondRight then
          threeRetentionProbability beta dimension ^ 3 else 0) +
        (if firstLeft = secondLeft ∧ firstRight = secondRight then
          threeRetentionProbability beta dimension ^ 2 else 0) := by
  rw [threeRetentionMeasure_real_contains_edgePair]
  have hnonnegative := (threeRetentionProbability_pos beta dimension).le
  by_cases hleft : firstLeft = secondLeft <;>
    by_cases hright : firstRight = secondRight <;>
    simp only [hleft, hright, ↓reduceIte, add_zero, Nat.reduceAdd,
      and_self, and_false, and_true, le_add_iff_nonneg_left, ge_iff_le,
      Std.le_refl] <;>
    positivity

noncomputable def threeExpectedRetainedVertexCount
    (dimension : ℕ) : ℝ :=
  ∑ vertex : Bool × HammingWord dimension,
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        vertex ∈ retained}

theorem threeExpectedRetainedVertexCount_eq
    (dimension : ℕ) :
    threeExpectedRetainedVertexCount beta dimension =
      2 * threeRetentionProbability beta dimension *
        ((2 ^ dimension : ℕ) : ℝ) := by
  unfold threeExpectedRetainedVertexCount
  simp_rw [threeRetentionMeasure_real_contains_vertex]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  simp [HammingWord]
  ring

theorem threeExpectedRetainedVertexCount_pos
    (dimension : ℕ) :
    0 < threeExpectedRetainedVertexCount beta dimension := by
  rw [threeExpectedRetainedVertexCount_eq]
  have hprobability := threeRetentionProbability_pos beta dimension
  positivity

theorem threeExpectedRetainedVertexCount_tendsto_atTop
    (hbeta : (beta:ℝ) < 1) :
    Tendsto (threeExpectedRetainedVertexCount beta) atTop atTop := by
  have hgrowth :=
    (threeRetentionProbability_mul_wordCount_tendsto_atTop beta
      hbeta).const_mul_atTop
      (by norm_num : (0 : ℝ) < 2)
  apply hgrowth.congr'
  filter_upwards [] with dimension
  rw [threeExpectedRetainedVertexCount_eq]
  ring

theorem threeExpectedRetainedVertexCount_inv_tendsto_zero
    (hbeta : (beta:ℝ) < 1) :
    Tendsto
      (fun dimension : ℕ =>
        1 / threeExpectedRetainedVertexCount beta dimension)
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    (threeExpectedRetainedVertexCount_tendsto_atTop beta hbeta)
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]

theorem threeRetentionMeasure_real_vertexPair
    (dimension : ℕ)
    (first second : Bool × HammingWord dimension) :
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        first ∈ retained ∧ second ∈ retained} =
      if first = second then
        threeRetentionProbability beta dimension
      else threeRetentionProbability beta dimension ^ 2 := by
  classical
  by_cases hequal : first = second
  · subst second
    have hevent :
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained ∧ first ∈ retained} =
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained} := by
      ext retained
      simp
    rw [hevent, threeRetentionMeasure_real_contains_vertex]
    simp
  · rw [threeRetentionMeasure_real_contains_pair beta
      dimension first second hequal]
    simp [hequal]

noncomputable def threeExpectedRetainedVertexSquare
    (dimension : ℕ) : ℝ :=
  ∑ first : Bool × HammingWord dimension,
    ∑ second : Bool × HammingWord dimension,
      (threeRetentionMeasure beta dimension).real
        {retained : Set (Bool × HammingWord dimension) |
          first ∈ retained ∧ second ∈ retained}

theorem threeExpectedRetainedVertexSquare_eq
    (dimension : ℕ) :
    threeExpectedRetainedVertexSquare beta dimension =
      (((2 * 2 ^ dimension : ℕ) : ℝ) ^ 2) *
        threeRetentionProbability beta dimension ^ 2 +
      (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        (threeRetentionProbability beta dimension -
          threeRetentionProbability beta dimension ^ 2) := by
  classical
  have hpoint
      (first second : Bool × HammingWord dimension) :
      (if first = second then
        threeRetentionProbability beta dimension
      else threeRetentionProbability beta dimension ^ 2) =
        threeRetentionProbability beta dimension ^ 2 +
          (if first = second then
            threeRetentionProbability beta dimension -
              threeRetentionProbability beta dimension ^ 2
           else 0) := by
    by_cases hequal : first = second <;>
      simp [hequal]
  unfold threeExpectedRetainedVertexSquare
  simp_rw [threeRetentionMeasure_real_vertexPair,
    hpoint, Finset.sum_add_distrib]
  simp [HammingWord, nsmul_eq_mul]
  ring

theorem threeExpectedRetainedVertexVariance_eq
    (dimension : ℕ) :
    threeExpectedRetainedVertexSquare beta dimension -
        threeExpectedRetainedVertexCount beta dimension ^ 2 =
      (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        threeRetentionProbability beta dimension *
        (1 - threeRetentionProbability beta dimension) := by
  rw [threeExpectedRetainedVertexSquare_eq,
    threeExpectedRetainedVertexCount_eq]
  push_cast
  ring

theorem threeExpectedRetainedVertexVariance_le_mean
    (dimension : ℕ) :
    threeExpectedRetainedVertexSquare beta dimension -
        threeExpectedRetainedVertexCount beta dimension ^ 2 ≤
      threeExpectedRetainedVertexCount beta dimension := by
  rw [threeExpectedRetainedVertexVariance_eq,
    threeExpectedRetainedVertexCount_eq]
  have hprobability := threeRetentionProbability_pos beta dimension
  have hupper := threeRetentionProbability_le_one beta dimension
  have hfactor :
      0 ≤ (((2 * 2 ^ dimension : ℕ) : ℝ)) *
        threeRetentionProbability beta dimension := by
    positivity
  have hle : 1 - threeRetentionProbability beta dimension ≤ 1 := by
    linarith
  have hscaled := mul_le_mul_of_nonneg_left hle hfactor
  push_cast at hscaled ⊢
  nlinarith

noncomputable def threeRetainedVertexCount
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) : ℝ := by
  classical
  exact ∑ vertex : Bool × HammingWord dimension,
    if vertex ∈ retained then 1 else 0

open Classical in
theorem threeRetainedVertexCount_eq_card
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    threeRetainedVertexCount dimension retained =
      (Fintype.card retained : ℝ) := by
  classical
  simp [threeRetainedVertexCount, Fintype.card_subtype]

theorem threeRetainedVertexCount_integral_eq
    (dimension : ℕ) :
    (∫ retained,
      threeRetainedVertexCount dimension retained
        ∂threeRetentionMeasure beta dimension) =
      threeExpectedRetainedVertexCount beta dimension := by
  classical
  unfold threeRetainedVertexCount threeExpectedRetainedVertexCount
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun vertex _ => threeRetentionMeasure_integrable beta dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if vertex ∈ retained then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro vertex _
  exact threeRetentionMeasure_integral_event_indicator beta dimension
    {retained : Set (Bool × HammingWord dimension) | vertex ∈ retained}

open Classical in
theorem threeRetainedVertexCount_sq
    (dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension)) :
    threeRetainedVertexCount dimension retained ^ 2 =
      ∑ first : Bool × HammingWord dimension,
        ∑ second : Bool × HammingWord dimension,
          if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0 := by
  classical
  unfold threeRetainedVertexCount
  rw [pow_two, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro first _
  apply Finset.sum_congr rfl
  intro second _
  by_cases hfirst : first ∈ retained <;>
    by_cases hsecond : second ∈ retained <;>
    simp [hfirst, hsecond]

theorem threeRetainedVertexCount_sq_integral_eq
    (dimension : ℕ) :
    (∫ retained,
      threeRetainedVertexCount dimension retained ^ 2
        ∂threeRetentionMeasure beta dimension) =
      threeExpectedRetainedVertexSquare beta dimension := by
  classical
  simp_rw [threeRetainedVertexCount_sq]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun first _ => threeRetentionMeasure_integrable beta dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ second : Bool × HammingWord dimension,
          if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0))]
  unfold threeExpectedRetainedVertexSquare
  apply Finset.sum_congr rfl
  intro first _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun second _ => threeRetentionMeasure_integrable beta dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if first ∈ retained ∧ second ∈ retained then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro second _
  rw [threeRetentionMeasure_integral_eq_sum,
    threeRetentionMeasure_real_event_eq_sum]
  apply Finset.sum_congr rfl
  intro retained _
  by_cases hretained : first ∈ retained ∧ second ∈ retained <;>
    simp [hretained]

theorem threeRetainedVertexCount_variance_eq
    (dimension : ℕ) :
    ProbabilityTheory.variance
        (threeRetainedVertexCount dimension)
        (threeRetentionMeasure beta dimension) =
      threeExpectedRetainedVertexSquare beta dimension -
        threeExpectedRetainedVertexCount beta dimension ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure
      (threeRetentionMeasure beta dimension) :=
    threeRetentionMeasure_isProbability beta dimension
  rw [ProbabilityTheory.variance_eq_sub
    (threeRetentionMeasure_memLp_two beta dimension
      (threeRetainedVertexCount dimension))]
  change
    (∫ retained,
      threeRetainedVertexCount dimension retained ^ 2
        ∂threeRetentionMeasure beta dimension) -
      (∫ retained,
        threeRetainedVertexCount dimension retained
          ∂threeRetentionMeasure beta dimension) ^ 2 =
      threeExpectedRetainedVertexSquare beta dimension -
        threeExpectedRetainedVertexCount beta dimension ^ 2
  rw [threeRetainedVertexCount_sq_integral_eq,
    threeRetainedVertexCount_integral_eq]

theorem threeRetainedVertexCount_variance_le
    (dimension : ℕ) :
    ProbabilityTheory.variance
        (threeRetainedVertexCount dimension)
        (threeRetentionMeasure beta dimension) ≤
      threeExpectedRetainedVertexCount beta dimension := by
  rw [threeRetainedVertexCount_variance_eq]
  exact threeExpectedRetainedVertexVariance_le_mean beta dimension

theorem threeRetainedVertexCount_deviation_probability_le
    (dimension : ℕ) (threshold : ℝ)
    (hthreshold : 0 < threshold) :
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |threeRetainedVertexCount dimension retained -
            threeExpectedRetainedVertexCount beta dimension|} ≤
      threeExpectedRetainedVertexCount beta dimension / threshold ^ 2 := by
  have hchebyshev := threeRetentionMeasure_real_deviation_le beta
    dimension (threeRetainedVertexCount dimension)
    threshold hthreshold
  rw [threeRetainedVertexCount_integral_eq] at hchebyshev
  calc
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |threeRetainedVertexCount dimension retained -
            threeExpectedRetainedVertexCount beta dimension|} ≤
      ProbabilityTheory.variance
          (threeRetainedVertexCount dimension)
          (threeRetentionMeasure beta dimension) /
        threshold ^ 2 := hchebyshev
    _ ≤ threeExpectedRetainedVertexCount beta dimension /
        threshold ^ 2 := by
      gcongr
      exact threeRetainedVertexCount_variance_le beta dimension

theorem threeRetainedVertexCount_upper_tail_probability_le
    (dimension : ℕ) :
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        3 * threeRetentionProbability beta dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          threeRetainedVertexCount dimension retained} ≤
      4 / threeExpectedRetainedVertexCount beta dimension := by
  letI : MeasureTheory.IsProbabilityMeasure
      (threeRetentionMeasure beta dimension) :=
    threeRetentionMeasure_isProbability beta dimension
  have hmean := threeExpectedRetainedVertexCount_pos beta dimension
  have hthreshold :
      0 < threeExpectedRetainedVertexCount beta dimension / 2 := by
    positivity
  have hchebyshev := threeRetainedVertexCount_deviation_probability_le beta
    dimension (threeExpectedRetainedVertexCount beta dimension / 2)
    hthreshold
  have hsubset :
      {retained : Set (Bool × HammingWord dimension) |
        3 * threeRetentionProbability beta dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          threeRetainedVertexCount dimension retained} ⊆
      {retained : Set (Bool × HammingWord dimension) |
        threeExpectedRetainedVertexCount beta dimension / 2 ≤
          |threeRetainedVertexCount dimension retained -
            threeExpectedRetainedVertexCount beta dimension|} := by
    intro retained hretained
    change
      threeExpectedRetainedVertexCount beta dimension / 2 ≤
        |threeRetainedVertexCount dimension retained -
          threeExpectedRetainedVertexCount beta dimension|
    have habsolute := le_abs_self
      (threeRetainedVertexCount dimension retained -
        threeExpectedRetainedVertexCount beta dimension)
    rw [threeExpectedRetainedVertexCount_eq] at habsolute ⊢
    change
      3 * threeRetentionProbability beta dimension *
          ((2 ^ dimension : ℕ) : ℝ) ≤
        threeRetainedVertexCount dimension retained at hretained
    nlinarith
  calc
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        3 * threeRetentionProbability beta dimension *
            ((2 ^ dimension : ℕ) : ℝ) ≤
          threeRetainedVertexCount dimension retained} ≤
      (threeRetentionMeasure beta dimension).real
        {retained : Set (Bool × HammingWord dimension) |
          threeExpectedRetainedVertexCount beta dimension / 2 ≤
            |threeRetainedVertexCount dimension retained -
              threeExpectedRetainedVertexCount beta dimension|} :=
        MeasureTheory.measureReal_mono hsubset
    _ ≤ threeExpectedRetainedVertexCount beta dimension /
        (threeExpectedRetainedVertexCount beta dimension / 2) ^ 2 :=
      hchebyshev
    _ = 4 / threeExpectedRetainedVertexCount beta dimension := by
      field_simp [hmean.ne']
      ring

noncomputable def threeExpectedRetainedEdgeCount
    (dimension radius : ℕ) : ℝ :=
  ∑ left : HammingWord dimension,
    ∑ right : HammingWord dimension,
      if hammingDist left right ≤ radius then
        (threeRetentionMeasure beta dimension).real
          {retained : Set (Bool × HammingWord dimension) |
            (false, left) ∈ retained ∧ (true, right) ∈ retained}
      else 0

theorem threeExpectedRetainedEdgeCount_eq
    (dimension radius : ℕ) :
    threeExpectedRetainedEdgeCount beta dimension radius =
      threeRetentionProbability beta dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ) *
        ((∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance : ℕ) : ℝ) := by
  classical
  have hpair (left right : HammingWord dimension) :
      (threeRetentionMeasure beta dimension).real
          {retained : Set (Bool × HammingWord dimension) |
            (false, left) ∈ retained ∧ (true, right) ∈ retained} =
        threeRetentionProbability beta dimension ^ 2 :=
    threeRetentionMeasure_real_contains_pair beta
      dimension (false, left) (true, right) (by simp)
  unfold threeExpectedRetainedEdgeCount
  simp_rw [hpair]
  simpa [mul_assoc, mul_comm, mul_left_comm] using
    hammingWordEdge_sum_const dimension radius
      (threeRetentionProbability beta dimension ^ 2)

theorem threeExpectedRetainedEdgeCount_pos
    (dimension radius : ℕ) :
    0 < threeExpectedRetainedEdgeCount beta dimension radius := by
  have hterm :
      1 ≤ ∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance := by
    have hzero := Finset.single_le_sum
      (s := Finset.range (radius + 1))
      (f := fun distance : ℕ => dimension.choose distance)
      (fun distance _ => Nat.zero_le _)
      (show 0 ∈ Finset.range (radius + 1) by simp)
    simpa using hzero
  have hdegree :
      0 < ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < ∑ distance ∈ Finset.range (radius + 1),
      dimension.choose distance by omega)
  rw [threeExpectedRetainedEdgeCount_eq]
  have hprobability := threeRetentionProbability_pos beta dimension
  positivity

noncomputable def threeExpectedRetainedEdgeSquare
    (dimension radius : ℕ) : ℝ :=
  ∑ firstLeft : HammingWord dimension,
    ∑ firstRight : HammingWord dimension,
      ∑ secondLeft : HammingWord dimension,
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            (threeRetentionMeasure beta dimension).real
              {retained : Set (Bool × HammingWord dimension) |
                (false, firstLeft) ∈ retained ∧
                (true, firstRight) ∈ retained ∧
                (false, secondLeft) ∈ retained ∧
                (true, secondRight) ∈ retained}
          else 0

theorem threeExpectedRetainedEdgeSquare_le_endpoint_decomposition
    (dimension radius : ℕ) :
    threeExpectedRetainedEdgeSquare beta dimension radius ≤
      ∑ firstLeft : HammingWord dimension,
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                threeRetentionProbability beta dimension ^ 4 +
                  (if firstLeft = secondLeft then
                    threeRetentionProbability beta dimension ^ 3 else 0) +
                  (if firstRight = secondRight then
                    threeRetentionProbability beta dimension ^ 3 else 0) +
                  (if firstLeft = secondLeft ∧
                      firstRight = secondRight then
                    threeRetentionProbability beta dimension ^ 2 else 0)
              else 0 := by
  unfold threeExpectedRetainedEdgeSquare
  apply Finset.sum_le_sum
  intro firstLeft _
  apply Finset.sum_le_sum
  intro firstRight _
  apply Finset.sum_le_sum
  intro secondLeft _
  apply Finset.sum_le_sum
  intro secondRight _
  by_cases hedge :
      hammingDist firstLeft firstRight ≤ radius ∧
        hammingDist secondLeft secondRight ≤ radius
  · simp only [hedge]
    exact threeRetentionMeasure_real_contains_edgePair_le beta
      dimension firstLeft firstRight secondLeft secondRight
  · simp [hedge]

theorem threeExpectedRetainedEdgeSquare_le
    (dimension radius : ℕ) :
    threeExpectedRetainedEdgeSquare beta dimension radius ≤
      threeExpectedRetainedEdgeCount beta dimension radius ^ 2 +
        threeExpectedRetainedEdgeCount beta dimension radius +
        2 * threeRetentionProbability beta dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
  classical
  have hpoint
      (firstLeft firstRight secondLeft secondRight : HammingWord dimension) :
      (if hammingDist firstLeft firstRight ≤ radius ∧
          hammingDist secondLeft secondRight ≤ radius then
        threeRetentionProbability beta dimension ^ 4 +
          (if firstLeft = secondLeft then
            threeRetentionProbability beta dimension ^ 3 else 0) +
          (if firstRight = secondRight then
            threeRetentionProbability beta dimension ^ 3 else 0) +
          (if firstLeft = secondLeft ∧ firstRight = secondRight then
            threeRetentionProbability beta dimension ^ 2 else 0)
      else 0) =
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          threeRetentionProbability beta dimension ^ 4 else 0) +
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if firstLeft = secondLeft then
            threeRetentionProbability beta dimension ^ 3 else 0
        else 0) +
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if firstRight = secondRight then
            threeRetentionProbability beta dimension ^ 3 else 0
        else 0) +
        (if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if firstLeft = secondLeft ∧ firstRight = secondRight then
            threeRetentionProbability beta dimension ^ 2 else 0
        else 0) := by
    split <;> simp
  calc
    threeExpectedRetainedEdgeSquare beta dimension radius ≤
      ∑ firstLeft : HammingWord dimension,
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                threeRetentionProbability beta dimension ^ 4 +
                  (if firstLeft = secondLeft then
                    threeRetentionProbability beta dimension ^ 3 else 0) +
                  (if firstRight = secondRight then
                    threeRetentionProbability beta dimension ^ 3 else 0) +
                  (if firstLeft = secondLeft ∧ firstRight = secondRight then
                    threeRetentionProbability beta dimension ^ 2 else 0)
              else 0 :=
        threeExpectedRetainedEdgeSquare_le_endpoint_decomposition beta
          dimension radius
    _ = threeExpectedRetainedEdgeCount beta dimension radius ^ 2 +
        threeExpectedRetainedEdgeCount beta dimension radius +
        2 * threeRetentionProbability beta dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
      simp_rw [hpoint, Finset.sum_add_distrib]
      rw [hammingWordEdgePair_sum_const,
        hammingWordEdgePairSharedLeft_sum_const,
        hammingWordEdgePairSharedRight_sum_const,
        hammingWordEdgePairIdentical_sum_const,
        threeExpectedRetainedEdgeCount_eq]
      ring

theorem threeExpectedRetainedEdgeVariance_le
    (dimension radius : ℕ) :
    threeExpectedRetainedEdgeSquare beta dimension radius -
        threeExpectedRetainedEdgeCount beta dimension radius ^ 2 ≤
      threeExpectedRetainedEdgeCount beta dimension radius +
        2 * threeRetentionProbability beta dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
  have hsecond := threeExpectedRetainedEdgeSquare_le beta dimension radius
  linarith


theorem threeRetainedEdgeCount_integral_eq
    (dimension radius : ℕ) :
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained
        ∂threeRetentionMeasure beta dimension) =
      threeExpectedRetainedEdgeCount beta dimension radius := by
  classical
  unfold hammingRetainedEdgeCount threeExpectedRetainedEdgeCount
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun left _ => threeRetentionMeasure_integrable beta dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ right : HammingWord dimension,
          if hammingDist left right ≤ radius ∧
              (false, left) ∈ retained ∧ (true, right) ∈ retained
          then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro left _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun right _ => threeRetentionMeasure_integrable beta dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if hammingDist left right ≤ radius ∧
            (false, left) ∈ retained ∧ (true, right) ∈ retained
        then (1 : ℝ) else 0))]
  apply Finset.sum_congr rfl
  intro right _
  by_cases hedge : hammingDist left right ≤ radius
  · simp only [hedge, true_and, if_true]
    rw [threeRetentionMeasure_integral_eq_sum,
      threeRetentionMeasure_real_event_eq_sum]
    apply Finset.sum_congr rfl
    intro retained _
    by_cases hretained :
        (false, left) ∈ retained ∧ (true, right) ∈ retained <;>
      simp [hretained]
  · simp [hedge]

open Classical in

theorem threeRetainedEdgeCount_sq_integral_eq
    (dimension radius : ℕ) :
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained ^ 2
        ∂threeRetentionMeasure beta dimension) =
      threeExpectedRetainedEdgeSquare beta dimension radius := by
  classical
  simp_rw [hammingRetainedEdgeCount_sq]
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun firstLeft _ => threeRetentionMeasure_integrable beta dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ firstRight : HammingWord dimension,
          ∑ secondLeft : HammingWord dimension,
            ∑ secondRight : HammingWord dimension,
              if hammingDist firstLeft firstRight ≤ radius ∧
                  hammingDist secondLeft secondRight ≤ radius then
                if (false, firstLeft) ∈ retained ∧
                    (true, firstRight) ∈ retained ∧
                    (false, secondLeft) ∈ retained ∧
                    (true, secondRight) ∈ retained
                then (1 : ℝ) else 0
              else 0))]
  unfold threeExpectedRetainedEdgeSquare
  apply Finset.sum_congr rfl
  intro firstLeft _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun firstRight _ => threeRetentionMeasure_integrable beta dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ secondLeft : HammingWord dimension,
          ∑ secondRight : HammingWord dimension,
            if hammingDist firstLeft firstRight ≤ radius ∧
                hammingDist secondLeft secondRight ≤ radius then
              if (false, firstLeft) ∈ retained ∧
                  (true, firstRight) ∈ retained ∧
                  (false, secondLeft) ∈ retained ∧
                  (true, secondRight) ∈ retained
              then (1 : ℝ) else 0
            else 0))]
  apply Finset.sum_congr rfl
  intro firstRight _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun secondLeft _ => threeRetentionMeasure_integrable beta dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        ∑ secondRight : HammingWord dimension,
          if hammingDist firstLeft firstRight ≤ radius ∧
              hammingDist secondLeft secondRight ≤ radius then
            if (false, firstLeft) ∈ retained ∧
                (true, firstRight) ∈ retained ∧
                (false, secondLeft) ∈ retained ∧
                (true, secondRight) ∈ retained
            then (1 : ℝ) else 0
          else 0))]
  apply Finset.sum_congr rfl
  intro secondLeft _
  rw [MeasureTheory.integral_finsetSum Finset.univ
    (fun secondRight _ => threeRetentionMeasure_integrable beta dimension
      (fun retained : Set (Bool × HammingWord dimension) =>
        if hammingDist firstLeft firstRight ≤ radius ∧
            hammingDist secondLeft secondRight ≤ radius then
          if (false, firstLeft) ∈ retained ∧
              (true, firstRight) ∈ retained ∧
              (false, secondLeft) ∈ retained ∧
              (true, secondRight) ∈ retained
          then (1 : ℝ) else 0
        else 0))]
  apply Finset.sum_congr rfl
  intro secondRight _
  by_cases hedge :
      hammingDist firstLeft firstRight ≤ radius ∧
        hammingDist secondLeft secondRight ≤ radius
  · simp only [hedge]
    rw [threeRetentionMeasure_integral_eq_sum,
      threeRetentionMeasure_real_event_eq_sum]
    apply Finset.sum_congr rfl
    intro retained _
    by_cases hretained :
        (false, firstLeft) ∈ retained ∧
          (true, firstRight) ∈ retained ∧
          (false, secondLeft) ∈ retained ∧
          (true, secondRight) ∈ retained <;>
      simp [hretained]
  · simp [hedge]

theorem threeRetainedEdgeCount_variance_eq
    (dimension radius : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedEdgeCount dimension radius)
        (threeRetentionMeasure beta dimension) =
      threeExpectedRetainedEdgeSquare beta dimension radius -
        threeExpectedRetainedEdgeCount beta dimension radius ^ 2 := by
  letI : MeasureTheory.IsProbabilityMeasure
      (threeRetentionMeasure beta dimension) :=
    threeRetentionMeasure_isProbability beta dimension
  rw [ProbabilityTheory.variance_eq_sub
    (threeRetentionMeasure_memLp_two beta dimension
      (hammingRetainedEdgeCount dimension radius))]
  change
    (∫ retained,
      hammingRetainedEdgeCount dimension radius retained ^ 2
        ∂threeRetentionMeasure beta dimension) -
      (∫ retained,
        hammingRetainedEdgeCount dimension radius retained
          ∂threeRetentionMeasure beta dimension) ^ 2 =
      threeExpectedRetainedEdgeSquare beta dimension radius -
        threeExpectedRetainedEdgeCount beta dimension radius ^ 2
  rw [threeRetainedEdgeCount_sq_integral_eq,
    threeRetainedEdgeCount_integral_eq]

theorem threeRetainedEdgeCount_variance_le
    (dimension radius : ℕ) :
    ProbabilityTheory.variance
        (hammingRetainedEdgeCount dimension radius)
        (threeRetentionMeasure beta dimension) ≤
      threeExpectedRetainedEdgeCount beta dimension radius +
        2 * threeRetentionProbability beta dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2 := by
  rw [threeRetainedEdgeCount_variance_eq]
  exact threeExpectedRetainedEdgeVariance_le beta dimension radius

theorem threeRetainedEdgeCount_deviation_probability_le
    (dimension radius : ℕ) (threshold : ℝ)
    (hthreshold : 0 < threshold) :
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedEdgeCount dimension radius retained -
            threeExpectedRetainedEdgeCount beta dimension radius|} ≤
      (threeExpectedRetainedEdgeCount beta dimension radius +
        2 * threeRetentionProbability beta dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2) /
        threshold ^ 2 := by
  have hchebyshev := threeRetentionMeasure_real_deviation_le beta
    dimension (hammingRetainedEdgeCount dimension radius)
    threshold hthreshold
  rw [threeRetainedEdgeCount_integral_eq] at hchebyshev
  calc
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threshold ≤
          |hammingRetainedEdgeCount dimension radius retained -
            threeExpectedRetainedEdgeCount beta dimension radius|} ≤
      ProbabilityTheory.variance
          (hammingRetainedEdgeCount dimension radius)
          (threeRetentionMeasure beta dimension) /
        threshold ^ 2 := hchebyshev
    _ ≤
      (threeExpectedRetainedEdgeCount beta dimension radius +
        2 * threeRetentionProbability beta dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2) /
        threshold ^ 2 := by
      gcongr
      exact threeRetainedEdgeCount_variance_le beta dimension radius

theorem threeRetainedEdgeCount_lower_tail_probability_le
    (dimension radius : ℕ) :
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          threeExpectedRetainedEdgeCount beta dimension radius / 2} ≤
      4 / threeExpectedRetainedEdgeCount beta dimension radius +
        8 / (threeRetentionProbability beta dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
  letI : MeasureTheory.IsProbabilityMeasure
      (threeRetentionMeasure beta dimension) :=
    threeRetentionMeasure_isProbability beta dimension
  have hmean := threeExpectedRetainedEdgeCount_pos beta dimension radius
  have hthreshold :
      0 < threeExpectedRetainedEdgeCount beta dimension radius / 2 := by
    positivity
  have hchebyshev := threeRetainedEdgeCount_deviation_probability_le beta
    dimension radius
    (threeExpectedRetainedEdgeCount beta dimension radius / 2)
    hthreshold
  have hsubset :
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          threeExpectedRetainedEdgeCount beta dimension radius / 2} ⊆
      {retained : Set (Bool × HammingWord dimension) |
        threeExpectedRetainedEdgeCount beta dimension radius / 2 ≤
          |hammingRetainedEdgeCount dimension radius retained -
            threeExpectedRetainedEdgeCount beta dimension radius|} := by
    intro retained hretained
    change
      threeExpectedRetainedEdgeCount beta dimension radius / 2 ≤
        |hammingRetainedEdgeCount dimension radius retained -
          threeExpectedRetainedEdgeCount beta dimension radius|
    have habsolute := neg_le_abs
      (hammingRetainedEdgeCount dimension radius retained -
        threeExpectedRetainedEdgeCount beta dimension radius)
    change
      hammingRetainedEdgeCount dimension radius retained <
        threeExpectedRetainedEdgeCount beta dimension radius / 2 at hretained
    linarith
  have hdegree_positive :
      0 < ((∑ distance ∈ Finset.range (radius + 1),
        dimension.choose distance : ℕ) : ℝ) := by
    have hterm :
        1 ≤ ∑ distance ∈ Finset.range (radius + 1),
          dimension.choose distance := by
      have hzero := Finset.single_le_sum
        (s := Finset.range (radius + 1))
        (f := fun distance : ℕ => dimension.choose distance)
        (fun distance _ => Nat.zero_le _)
        (show 0 ∈ Finset.range (radius + 1) by simp)
      simpa using hzero
    exact_mod_cast (show 0 < ∑ distance ∈ Finset.range (radius + 1),
      dimension.choose distance by omega)
  have hprobability := threeRetentionProbability_pos beta dimension
  have hwords : 0 < ((2 ^ dimension : ℕ) : ℝ) := by
    positivity
  calc
    (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        hammingRetainedEdgeCount dimension radius retained <
          threeExpectedRetainedEdgeCount beta dimension radius / 2} ≤
      (threeRetentionMeasure beta dimension).real
      {retained : Set (Bool × HammingWord dimension) |
        threeExpectedRetainedEdgeCount beta dimension radius / 2 ≤
          |hammingRetainedEdgeCount dimension radius retained -
            threeExpectedRetainedEdgeCount beta dimension radius|} :=
        MeasureTheory.measureReal_mono hsubset
    _ ≤
      (threeExpectedRetainedEdgeCount beta dimension radius +
        2 * threeRetentionProbability beta dimension ^ 3 *
          ((2 ^ dimension : ℕ) : ℝ) *
          ((∑ distance ∈ Finset.range (radius + 1),
            dimension.choose distance : ℕ) : ℝ) ^ 2) /
        (threeExpectedRetainedEdgeCount beta dimension radius / 2) ^ 2 :=
      hchebyshev
    _ = 4 / threeExpectedRetainedEdgeCount beta dimension radius +
        8 / (threeRetentionProbability beta dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
      rw [threeExpectedRetainedEdgeCount_eq]
      field_simp [hprobability.ne', hwords.ne', hdegree_positive.ne']
      ring

noncomputable def tripleChildVertexFinset
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : TripleLayer parentCount 1 → HammingWord dimension) :
    Finset (Bool × HammingWord dimension) := by
  classical
  exact (Finset.univ : Finset (TripleLayer parentCount 1)).image
    (fun triple => (side, children triple))

theorem tripleChildVertexFinset_card
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (hinjective : Function.Injective children) :
    (tripleChildVertexFinset side children).card = parentCount.choose 3 := by
  classical
  unfold tripleChildVertexFinset
  rw [Finset.card_image_of_injective]
  · rw [Finset.card_univ, tripleLayer_card_succ parentCount 0,
      tripleLayer_card_zero]
  · intro first second hequal
    exact hinjective (congrArg Prod.snd hequal)

def tripleChildRetentionEvent
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : TripleLayer parentCount 1 → HammingWord dimension) :
    Set (Set (Bool × HammingWord dimension)) :=
  {retained | ∀ triple, (side, children triple) ∈ retained}

theorem threeRetentionMeasure_real_tripleChildren
    {parentCount dimension : ℕ}
    (side : Bool)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (hinjective : Function.Injective children) :
    (threeRetentionMeasure beta dimension).real
        (tripleChildRetentionEvent side children) =
      threeRetentionProbability beta dimension ^ (parentCount.choose 3) := by
  classical
  have hevent :
      tripleChildRetentionEvent side children =
        {retained : Set (Bool × HammingWord dimension) |
          ∀ vertex ∈ tripleChildVertexFinset side children,
            vertex ∈ retained} := by
    ext retained
    simp [tripleChildRetentionEvent, tripleChildVertexFinset]
  rw [hevent, threeRetentionMeasure_real_contains_finset,
    tripleChildVertexFinset_card side children hinjective]

noncomputable def badTripleChildRetentionEvent
    {parentCount dimension : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (side : Bool)
    (threshold : ℝ) : Set (Set (Bool × HammingWord dimension)) := by
  classical
  exact
    ⋃ children ∈
        (badTripleChildArrays parents threshold).filter Function.Injective,
      tripleChildRetentionEvent side children

theorem badTripleChildRetentionEvent_real_le
    {parentCount dimension : ℕ}
    (hparents : 3 ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (side : Bool)
    (threshold : ℝ) :
    (threeRetentionMeasure beta dimension).real
        (badTripleChildRetentionEvent parents side threshold) ≤
      ((((parentCount.choose 3 + 1) ^ (4 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 3 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          threeRetentionProbability beta dimension ^
            (parentCount.choose 3) := by
  classical
  let distinctBad :
      Finset (TripleLayer parentCount 1 → HammingWord dimension) :=
    (badTripleChildArrays parents threshold).filter Function.Injective
  have hprobability_nonneg :
      0 ≤ threeRetentionProbability beta dimension ^
        (parentCount.choose 3) :=
    pow_nonneg (threeRetentionProbability_pos beta dimension).le _
  have hcard :
      (distinctBad.card : ℝ) ≤
        ((badTripleChildArrays parents threshold).card : ℝ) := by
    dsimp [distinctBad]
    exact_mod_cast
      Finset.card_filter_le
        (badTripleChildArrays parents threshold) Function.Injective
  calc
    (threeRetentionMeasure beta dimension).real
        (badTripleChildRetentionEvent parents side threshold) =
      (threeRetentionMeasure beta dimension).real
        (⋃ children ∈ distinctBad,
          tripleChildRetentionEvent side children) := by
        rfl
    _ ≤ ∑ children ∈ distinctBad,
          (threeRetentionMeasure beta dimension).real
            (tripleChildRetentionEvent side children) :=
        MeasureTheory.measureReal_biUnion_finset_le
          distinctBad (tripleChildRetentionEvent side)
    _ = ∑ _children ∈ distinctBad,
          threeRetentionProbability beta dimension ^
            (parentCount.choose 3) := by
        apply Finset.sum_congr rfl
        intro children hchildren
        have hinjective : Function.Injective children := by
          have hmembership :
              children ∈
                (badTripleChildArrays parents threshold).filter
                  Function.Injective := by
            simpa only [distinctBad] using hchildren
          exact (Finset.mem_filter.mp hmembership).2
        exact threeRetentionMeasure_real_tripleChildren beta
          side children hinjective
    _ = (distinctBad.card : ℝ) *
          threeRetentionProbability beta dimension ^
            (parentCount.choose 3) := by
        simp [nsmul_eq_mul]
    _ ≤ ((badTripleChildArrays parents threshold).card : ℝ) *
          threeRetentionProbability beta dimension ^
            (parentCount.choose 3) :=
        mul_le_mul_of_nonneg_right hcard hprobability_nonneg
    _ ≤
      ((((parentCount.choose 3 + 1) ^ (4 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 3 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          threeRetentionProbability beta dimension ^
            (parentCount.choose 3) :=
        mul_le_mul_of_nonneg_right
          (badTripleChildArrays_card_le hparents hdimension parents threshold)
          hprobability_nonneg

noncomputable def badTripleLayerRetentionEvent
    (parentCount dimension : ℕ)
    (side : Bool)
    (threshold : ℝ) : Set (Set (Bool × HammingWord dimension)) :=
  ⋃ parents : Fin parentCount → HammingWord dimension,
    badTripleChildRetentionEvent parents side threshold

theorem badTripleLayerRetentionEvent_real_le
    {parentCount dimension : ℕ}
    (hparents : 3 ≤ parentCount)
    (hdimension : 0 < dimension)
    (side : Bool)
    (threshold : ℝ) :
    (threeRetentionMeasure beta dimension).real
        (badTripleLayerRetentionEvent parentCount dimension side threshold) ≤
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 3 + 1) ^ (4 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 3 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          threeRetentionProbability beta dimension ^
            (parentCount.choose 3) := by
  classical
  let bound : ℝ :=
    ((((parentCount.choose 3 + 1) ^ (4 * dimension) : ℕ) : ℝ) *
      Real.exp
        ((parentCount.choose 3 : ℝ) * Real.log 2 *
          (dimension : ℝ) * threshold)) *
        threeRetentionProbability beta dimension ^
          (parentCount.choose 3)
  calc
    (threeRetentionMeasure beta dimension).real
        (badTripleLayerRetentionEvent parentCount dimension side threshold) =
      (threeRetentionMeasure beta dimension).real
        (⋃ parents : Fin parentCount → HammingWord dimension,
          badTripleChildRetentionEvent parents side threshold) := by
        rfl
    _ ≤ ∑ parents : Fin parentCount → HammingWord dimension,
          (threeRetentionMeasure beta dimension).real
            (badTripleChildRetentionEvent parents side threshold) :=
        MeasureTheory.measureReal_iUnion_fintype_le
          (fun parents => badTripleChildRetentionEvent parents side threshold)
    _ ≤ ∑ _parents : Fin parentCount → HammingWord dimension, bound := by
      apply Finset.sum_le_sum
      intro parents _
      exact badTripleChildRetentionEvent_real_le beta
        hparents hdimension parents side threshold
    _ =
      (((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 3 + 1) ^ (4 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 3 : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold)) *
          threeRetentionProbability beta dimension ^
            (parentCount.choose 3) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        hammingParentTuple_card]
      dsimp [bound]
      ring


theorem badTripleLayerRetentionEvent_real_lt_exp_neg
    {parentCount dimension : ℕ}
    (hparents : 4 ≤ parentCount)
    (hdimension : 0 < dimension)
    (hbase :
      (parentCount : ℝ) +
        4 * logTwo ((parentCount.choose 3 + 1 : ℕ) : ℝ) -
          slack * (parentCount.choose 3 : ℝ) < -1)
    (side : Bool) :
    (threeRetentionMeasure beta dimension).real
      (badTripleLayerRetentionEvent parentCount dimension side
        ((beta : ℝ) - slack)) <
      Real.exp (-(dimension : ℝ) * Real.log 2) := by
  have hdimension_real : 0 < (dimension : ℝ) := by
    exact_mod_cast hdimension
  calc
    (threeRetentionMeasure beta dimension).real
      (badTripleLayerRetentionEvent parentCount dimension side
        ((beta : ℝ) - slack)) ≤
      ((((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
        (((parentCount.choose 3 + 1) ^ (4 * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose 3 : ℝ) * Real.log 2 *
            (dimension : ℝ) * ((beta : ℝ) - slack))) *
          threeRetentionProbability beta dimension ^
            (parentCount.choose 3)) :=
        badTripleLayerRetentionEvent_real_le beta
          (by omega) hdimension side ((beta : ℝ) - slack)
    _ = Real.exp
        ((dimension : ℝ) * Real.log 2 *
          ((parentCount : ℝ) +
            4 * logTwo ((parentCount.choose 3 + 1 : ℕ) : ℝ) -
              slack * (parentCount.choose 3 : ℝ))) :=
        by rw [show threeRetentionProbability beta dimension =
            Real.exp (-((beta : ℝ) * (dimension : ℝ) * Real.log 2)) from rfl]
           exact badTripleLayerRetentionBound_eq_exp parentCount dimension
             (beta : ℝ) slack
    _ < Real.exp (-(dimension : ℝ) * Real.log 2) := by
      apply Real.exp_lt_exp.mpr
      have hscaled := mul_lt_mul_of_pos_left hbase
        (mul_pos hdimension_real log_two_pos)
      nlinarith

noncomputable def badTripleLayersRetentionEvent
    {depth : ℕ}
    (layerSizes : Fin depth → ℕ)
    (dimension : ℕ) : Set (Set (Bool × HammingWord dimension)) :=
  ⋃ side : Bool, ⋃ layer : Fin depth,
    badTripleLayerRetentionEvent (layerSizes layer) dimension side
      ((beta : ℝ) - slack)

theorem badTripleLayersRetentionEvent_real_le
    {depth dimension : ℕ}
    (layerSizes : Fin depth → ℕ)
    (hdimension : 0 < dimension)
    (hparents : ∀ layer, 4 ≤ layerSizes layer)
    (hbase : ∀ layer,
      (layerSizes layer : ℝ) +
        4 * logTwo
          (((layerSizes layer).choose 3 + 1 : ℕ) : ℝ) -
          slack * ((layerSizes layer).choose 3 : ℝ) < -1) :
    (threeRetentionMeasure beta dimension).real
        (badTripleLayersRetentionEvent beta slack layerSizes dimension) ≤
      (((2 * depth : ℕ) : ℝ)) *
        Real.exp (-(dimension : ℝ) * Real.log 2) := by
  classical
  let bound : ℝ := Real.exp (-(dimension : ℝ) * Real.log 2)
  calc
    (threeRetentionMeasure beta dimension).real
        (badTripleLayersRetentionEvent beta slack layerSizes dimension) =
      (threeRetentionMeasure beta dimension).real
        (⋃ side : Bool, ⋃ layer : Fin depth,
          badTripleLayerRetentionEvent (layerSizes layer) dimension side
            ((beta : ℝ) - slack)) := by
        rfl
    _ ≤ ∑ side : Bool,
        (threeRetentionMeasure beta dimension).real
          (⋃ layer : Fin depth,
            badTripleLayerRetentionEvent (layerSizes layer) dimension side
              ((beta : ℝ) - slack)) :=
        MeasureTheory.measureReal_iUnion_fintype_le
          (fun side =>
            ⋃ layer : Fin depth,
              badTripleLayerRetentionEvent (layerSizes layer) dimension side
                ((beta : ℝ) - slack))
    _ ≤ ∑ side : Bool, ∑ layer : Fin depth,
          (threeRetentionMeasure beta dimension).real
            (badTripleLayerRetentionEvent
              (layerSizes layer) dimension side
                ((beta : ℝ) - slack)) := by
        apply Finset.sum_le_sum
        intro side _
        exact MeasureTheory.measureReal_iUnion_fintype_le
          (fun layer =>
            badTripleLayerRetentionEvent
              (layerSizes layer) dimension side
                ((beta : ℝ) - slack))
    _ ≤ ∑ _side : Bool, ∑ _layer : Fin depth, bound := by
        apply Finset.sum_le_sum
        intro side _
        apply Finset.sum_le_sum
        intro layer _
        exact (badTripleLayerRetentionEvent_real_lt_exp_neg beta slack
          (hparents layer) hdimension (hbase layer) side).le
    _ = (((2 * depth : ℕ) : ℝ)) *
          Real.exp (-(dimension : ℝ) * Real.log 2) := by
        simp [bound, nsmul_eq_mul]
        ring


theorem exists_threeRetention_outside_event
    (dimension : ℕ)
    (event : Set (Set (Bool × HammingWord dimension)))
    (hsmall : (threeRetentionMeasure beta dimension).real event < 1) :
    ∃ retained : Set (Bool × HammingWord dimension), retained ∉ event := by
  letI : MeasureTheory.IsProbabilityMeasure
      (threeRetentionMeasure beta dimension) :=
    threeRetentionMeasure_isProbability beta dimension
  by_contra hnone
  push Not at hnone
  have hevent : event = Set.univ := Set.eq_univ_of_forall hnone
  rw [hevent] at hsmall
  simp at hsmall



/-! ## The `r = 3` Hamming radius `τ = 2/5` and the ball size `D_m`

Port of `manuscriptHammingRadius` (published line 17594) with
`tau = (√3−1)/2` replaced by `tauThree = 2/5`.  The ball-size machinery
itself (`hammingBall`, `boundedDifferenceSets_card`, `hammingBall_card`,
`hammingBall_card_ge_boundary_binomial`, `exp_binary_entropy_div_le_choose`)
is arity-agnostic and is reused verbatim from the published file. -/

/-- The `r = 3` Hamming radius `⌊(2/5)·m⌋`. -/
noncomputable def threeHammingRadius (dimension : ℕ) : ℕ :=
  ⌊tauThree * (dimension : ℝ)⌋₊

theorem threeHammingRadius_le (dimension : ℕ) :
    (threeHammingRadius dimension : ℝ) ≤ tauThree * (dimension : ℝ) := by
  unfold threeHammingRadius
  refine Nat.floor_le (mul_nonneg ?_ (Nat.cast_nonneg dimension))
  unfold tauThree; norm_num

theorem threeHammingRadius_le_dimension (dimension : ℕ) :
    threeHammingRadius dimension ≤ dimension := by
  have hradius := threeHammingRadius_le dimension
  have hdimension : 0 ≤ (dimension : ℝ) := Nat.cast_nonneg dimension
  have hreal : (threeHammingRadius dimension : ℝ) ≤ (dimension : ℝ) := by
    unfold tauThree at hradius; nlinarith
  exact_mod_cast hreal

theorem threeHammingRadius_ratio_tendsto :
    Tendsto
      (fun dimension : ℕ =>
        (threeHammingRadius dimension : ℝ) / (dimension : ℝ))
      atTop (𝓝 tauThree) := by
  unfold threeHammingRadius
  exact
    (tendsto_nat_floor_mul_div_atTop (R := ℝ)
      (show (0:ℝ) ≤ tauThree by unfold tauThree; norm_num)).comp
      tendsto_natCast_atTop_atTop

theorem threeHammingRadius_binEntropy_tendsto :
    Tendsto
      (fun dimension : ℕ =>
        Real.binEntropy
          ((threeHammingRadius dimension : ℝ) / (dimension : ℝ)))
      atTop (𝓝 (Real.binEntropy tauThree)) :=
  Real.binEntropy_continuous.continuousAt.tendsto.comp
    threeHammingRadius_ratio_tendsto

/-- `D_m ≥ 2^{(h(r_m/m))·m} / (m+1)`, the `2^{(h(τ)+o(1))m}` lower bound. -/
theorem threeHammingBall_card_entropy_lower
    (dimension : ℕ) (word : HammingWord dimension) :
    Real.exp
        ((dimension : ℝ) *
          Real.binEntropy
            ((threeHammingRadius dimension : ℝ) / (dimension : ℝ))) /
        ((dimension + 1 : ℕ) : ℝ) ≤
      ((hammingBall dimension (threeHammingRadius dimension) word).card : ℝ) := by
  calc
    Real.exp
        ((dimension : ℝ) *
          Real.binEntropy
            ((threeHammingRadius dimension : ℝ) / (dimension : ℝ))) /
        ((dimension + 1 : ℕ) : ℝ) ≤
      (dimension.choose (threeHammingRadius dimension) : ℝ) :=
        exp_binary_entropy_div_le_choose dimension
          (threeHammingRadius dimension)
          (threeHammingRadius_le_dimension dimension)
    _ ≤ ((hammingBall dimension (threeHammingRadius dimension) word).card : ℝ) := by
      exact_mod_cast hammingBall_card_ge_boundary_binomial
        dimension (threeHammingRadius dimension) word

theorem eventually_threeHammingRadius_binEntropy_ge
    (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ dimension : ℕ in atTop,
      Real.binEntropy tauThree - loss ≤
        Real.binEntropy
          ((threeHammingRadius dimension : ℝ) / (dimension : ℝ)) := by
  have hneighborhood :
      Set.Ioi (Real.binEntropy tauThree - loss) ∈
        𝓝 (Real.binEntropy tauThree) :=
    Ioi_mem_nhds (by linarith)
  filter_upwards [threeHammingRadius_binEntropy_tendsto hneighborhood]
    with dimension hdimension
  exact (show Real.binEntropy tauThree - loss <
    Real.binEntropy
      ((threeHammingRadius dimension : ℝ) / (dimension : ℝ)) from hdimension).le

/-! ## The sampled edge exponent for `r = 3` -/

/-- `log` of the growth rate of `p²·2^m·D_m`, i.e. `(1 − 2β + h(τ))·log 2`. -/
noncomputable def sampledThreeEdgeEntropyRate : ℝ :=
  (1 - 2 * (beta : ℝ)) * Real.log 2 + Real.binEntropy tauThree

theorem sampledThreeEdgeEntropyRate_gt (eps : ℝ)
    (hbeta : (beta : ℝ) ≤ 9126 / 10000)
    (heps : eps ≤ 1 / 4000) (heps0 : 0 < eps) :
    (1 - (beta : ℝ)) * (5 / 3 + eps) * Real.log 2 <
      sampledThreeEdgeEntropyRate beta := by
  have hkey := threeExponent_product_gt (beta : ℝ) eps hbeta heps heps0
  have hentropy :
      Real.binEntropy tauThree = binaryEntropy tauThree * Real.log 2 := by
    unfold binaryEntropy
    field_simp [log_two_pos.ne']
  have hlog := log_two_pos
  unfold sampledThreeEdgeEntropyRate
  rw [hentropy]
  nlinarith [hkey, hlog]

theorem sampledThreeEdgeEntropyRate_pos
    (hbeta : (beta : ℝ) ≤ 9126 / 10000) :
    0 < sampledThreeEdgeEntropyRate beta := by
  have h := sampledThreeEdgeEntropyRate_gt beta (1/8000) hbeta
    (by norm_num) (by norm_num)
  have hb : (beta : ℝ) ≤ 9126/10000 := hbeta
  have hb0 : (0:ℝ) ≤ (beta : ℝ) := beta.coe_nonneg
  have hlog := log_two_pos
  nlinarith [h, hlog]



/-! ## The whp conjunction

`W_m ≤ 3·p·Q` (`Q = 2^m` words per side), `e_m ≥ ½·p²·Q·D_m` and the
layer-exclusion event all hold simultaneously for some retention set, as
soon as the three failure probabilities sum to less than `1`. -/

theorem exists_good_retention
    {depth dimension : ℕ} (layerSizes : Fin depth → ℕ) (radius : ℕ)
    (hdimension : 0 < dimension)
    (hparents : ∀ layer, 4 ≤ layerSizes layer)
    (hbase : ∀ layer,
      (layerSizes layer : ℝ) +
        4 * logTwo (((layerSizes layer).choose 3 + 1 : ℕ) : ℝ) -
          slack * ((layerSizes layer).choose 3 : ℝ) < -1)
    (hbudget :
      ((2 * depth : ℕ) : ℝ) * Real.exp (-(dimension : ℝ) * Real.log 2) +
        4 / threeExpectedRetainedVertexCount beta dimension +
        (4 / threeExpectedRetainedEdgeCount beta dimension radius +
          8 / (threeRetentionProbability beta dimension *
            ((2 ^ dimension : ℕ) : ℝ))) < 1) :
    ∃ retained : Set (Bool × HammingWord dimension),
      retained ∉
          badTripleLayersRetentionEvent beta slack layerSizes dimension ∧
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
    badTripleLayersRetentionEvent beta slack layerSizes dimension with hlayerBad
  have hlayer :=
    badTripleLayersRetentionEvent_real_le beta slack layerSizes
      hdimension hparents hbase
  have hvertex :=
    threeRetainedVertexCount_upper_tail_probability_le beta dimension
  have hedge :=
    threeRetainedEdgeCount_lower_tail_probability_le beta dimension radius
  have hunion :
      (threeRetentionMeasure beta dimension).real
          (layerBad ∪ (vertexBad ∪ edgeBad)) < 1 := by
    have h1 :=
      MeasureTheory.measureReal_union_le (μ := threeRetentionMeasure beta dimension)
        layerBad (vertexBad ∪ edgeBad)
    have h2 :=
      MeasureTheory.measureReal_union_le (μ := threeRetentionMeasure beta dimension)
        vertexBad edgeBad
    have := hlayer
    linarith [h1, h2, hlayer, hvertex, hedge, hbudget]
  obtain ⟨retained, hretained⟩ :=
    exists_threeRetention_outside_event beta dimension _ hunion
  refine ⟨retained, ?_, ?_, ?_⟩
  · exact fun hmem => hretained (Or.inl hmem)
  · have : retained ∉ vertexBad := fun hmem => hretained (Or.inr (Or.inl hmem))
    simpa [hvertexBad, not_le] using this
  · have : retained ∉ edgeBad := fun hmem => hretained (Or.inr (Or.inr hmem))
    simpa [hedgeBad, not_lt] using this

/-- Restated with the ball-size `D_m` made explicit:
`e_m ≥ ½ · p² · Q · D_m`. -/
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
      hammingRetainedEdgeCount dimension radius retained := by
  rw [threeExpectedRetainedEdgeCount_eq] at hedges
  linarith [hedges]


end ThreeSampling

