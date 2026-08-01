import CompactnessAndDegeneracy

/-!
# Hamming profiles for the `r`-ary layered graph (r-generic)

`r`-generic port of `Profiles3.lean`, which was itself the `r = 3` port of the
`HammingProfiles` counting layer of `CompactnessAndDegeneracy.lean` (`r = 2`).

Everything up to and including `classifiedBooleanWords_card` in the published
file is already generic (stated for an arbitrary classification
`classify : ι -> γ`), so it is *reused verbatim* here.  What is ported below is
the arity-specific tail:

* `(a)` per-coordinate profile count: `#profiles = (M+1)^((r+1)m)` with
  `M = parentCount.choose r` — `rTypeCountProfile_card`;
* `(b)` for a fixed profile, `#child arrays ≤ ∏ C(N_{g,j}, b_{g,j}) ≤ 2^{m M E}`
  — `rChildArraysOfRealizedProfile_card_le` and the union over profiles
  `badRChildArrays_card_le`;
* `(c)` the union-bound exponent identity `badRLayerRetentionBound_eq_exp`,
  stated for an arbitrary retention exponent `beta` and slack `slack` — so the
  window `A_r < beta_r < C_r` enters only downstream, as a hypothesis bundle,
  never as a numeral here.

The parent-type alphabet is `Fin (r+1)`: the type of an `r`-subset at a
coordinate is the *number* `j ∈ {0, …, r}` of its `r` parents carrying a `1`
there.  For `r = 2` the published file used `Fin 3`, for `r = 3`
`Profiles3.lean` used `Fin 4`; the counting-relevant content is identical.

No numeric hypothesis on `r` is needed beyond `r ≤ parentCount` (so that
`C(parentCount, r) > 0`), which appears exactly where `3 ≤ parentCount` did.
-/

open TwoDegenerateGraphs

namespace RGenericProfiles

/-! ## The `r`-subset layer

`TwoDegenerateGraphs.PairLayer` / `ThreeDegenerateProfiles.TripleLayer` with the
card constraint made a variable; definitionally the same as
`DegenerateGraphsR.LayerR` in `LayeredGraphR.lean`. -/

def RLayer (baseSize r : ℕ) : ℕ → Type
  | 0 => Fin baseSize
  | i + 1 => {parents : Finset (RLayer baseSize r i) // parents.card = r}

instance rLayerDecidableEq (baseSize r i : ℕ) :
    DecidableEq (RLayer baseSize r i) := by
  induction i with
  | zero =>
      change DecidableEq (Fin baseSize)
      infer_instance
  | succ i ih =>
      letI := ih
      change DecidableEq
        {parents : Finset (RLayer baseSize r i) // parents.card = r}
      infer_instance

noncomputable instance rLayerFintype (baseSize r i : ℕ) :
    Fintype (RLayer baseSize r i) := by
  classical
  induction i with
  | zero =>
      change Fintype (Fin baseSize)
      infer_instance
  | succ i ih =>
      letI := ih
      change Fintype
        {parents : Finset (RLayer baseSize r i) // parents.card = r}
      infer_instance

theorem rLayer_card_zero (baseSize r : ℕ) :
    Fintype.card (RLayer baseSize r 0) = baseSize := by
  change Fintype.card (Fin baseSize) = baseSize
  simp

theorem rLayer_card_succ (baseSize r i : ℕ) :
    Fintype.card (RLayer baseSize r (i + 1)) =
      (Fintype.card (RLayer baseSize r i)).choose r := by
  classical
  let layerRSubsets : Finset (Finset (RLayer baseSize r i)) :=
    (Finset.univ : Finset (RLayer baseSize r i)).powersetCard r
  let equivalence : RLayer baseSize r (i + 1) ≃ layerRSubsets :=
    { toFun := fun p =>
        ⟨p.val, by
          apply Finset.mem_powersetCard.mpr
          exact ⟨Finset.subset_univ _, p.property⟩⟩
      invFun := fun p => ⟨p.val, (Finset.mem_powersetCard.mp p.property).2⟩
      left_inv := by intro p; rfl
      right_inv := by intro p; rfl }
  calc
    Fintype.card (RLayer baseSize r (i + 1)) = Fintype.card layerRSubsets :=
      Fintype.card_congr equivalence
    _ = layerRSubsets.card := Fintype.card_coe layerRSubsets
    _ = (Fintype.card (RLayer baseSize r i)).choose r := by
      simp [layerRSubsets]

theorem rLayer_one_card (baseSize r : ℕ) :
    Fintype.card (RLayer baseSize r 1) = baseSize.choose r := by
  rw [rLayer_card_succ, rLayer_card_zero]

/-! ## Coordinate bit types

`(a)` The parent-type alphabet has `r+1` letters: `j = #{parents in the
`r`-subset carrying a 1 at this coordinate} ∈ {0, …, r}`. -/

abbrev RBitType (r : ℕ) := Fin (r + 1)

abbrev RTypeCountProfile (parentCount dimension r : ℕ) :=
  RBitType r → Fin dimension → Fin (parentCount.choose r + 1)

/-- `(a)` There are `(M+1)^((r+1)m)` profiles, `M = parentCount.choose r`. -/
theorem rTypeCountProfile_card (parentCount dimension r : ℕ) :
    Fintype.card (RTypeCountProfile parentCount dimension r) =
      (parentCount.choose r + 1) ^ ((r + 1) * dimension) := by
  simp [RTypeCountProfile, pow_mul, Nat.mul_comm]

/-- The type of an `r`-subset at a coordinate: how many of its `r` parents
carry a `1` there. -/
noncomputable def rCoordinateBitType
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (sub : RLayer parentCount r 1) : RBitType r := by
  refine ⟨(sub.val.filter
      (fun parent => parents parent coordinate = true)).card, ?_⟩
  exact lt_of_le_of_lt
    (le_trans (Finset.card_filter_le _ _) (le_of_eq sub.property))
    (by norm_num)

noncomputable def rTypeGroup
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : RBitType r) : Finset (RLayer parentCount r 1) := by
  classical
  exact Finset.univ.filter
    (fun sub => rCoordinateBitType parents coordinate sub = bitType)

noncomputable def rCoordinateClassification
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension) :
    RLayer parentCount r 1 × Fin dimension → (RBitType r) × Fin dimension :=
  fun index =>
    (rCoordinateBitType parents index.2 index.1, index.2)

noncomputable def rCoordinateClassificationFiberEquiv
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (bitType : RBitType r) (coordinate : Fin dimension) :
    ClassificationFiber
        (rCoordinateClassification parents) (bitType, coordinate) ≃
      ↥(rTypeGroup parents coordinate bitType) := by
  classical
  refine
    { toFun := fun index => ⟨index.val.1, ?_⟩
      invFun := fun sub => ⟨(sub.val, coordinate), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have htype := congrArg Prod.fst index.property
    have hcoordinate : index.val.2 = coordinate := by
      simpa [rCoordinateClassification] using
        congrArg Prod.snd index.property
    simp only [rTypeGroup, Finset.mem_filter,
      Finset.mem_univ, true_and]
    simpa [rCoordinateClassification, hcoordinate] using htype
  · have hmembership :
        sub.val ∈
          (Finset.univ.filter
            (fun candidate : RLayer parentCount r 1 =>
              rCoordinateBitType parents coordinate candidate =
                bitType)) := by
      simpa only [rTypeGroup] using sub.property
    have htype := (Finset.mem_filter.mp hmembership).2
    change
      (rCoordinateBitType parents coordinate sub.val, coordinate) =
        (bitType, coordinate)
    exact Prod.ext htype rfl
  · intro index
    apply Subtype.ext
    apply Prod.ext
    · rfl
    · have hcoordinate := congrArg Prod.snd index.property
      simpa [rCoordinateClassification] using hcoordinate.symm
  · intro sub
    apply Subtype.ext
    rfl

theorem rCoordinateClassificationFiber_card
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (bitType : RBitType r) (coordinate : Fin dimension) :
    Fintype.card
      (ClassificationFiber
        (rCoordinateClassification parents) (bitType, coordinate)) =
      (rTypeGroup parents coordinate bitType).card := by
  calc
    Fintype.card
        (ClassificationFiber
          (rCoordinateClassification parents) (bitType, coordinate)) =
        Fintype.card ↥(rTypeGroup parents coordinate bitType) :=
      Fintype.card_congr
        (rCoordinateClassificationFiberEquiv parents bitType coordinate)
    _ = (rTypeGroup parents coordinate bitType).card :=
      Fintype.card_coe _

theorem sum_rTypeGroup_card
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : RBitType r,
      (rTypeGroup parents coordinate bitType).card) =
      parentCount.choose r := by
  classical
  have hmaps :
      (((Finset.univ : Finset (RLayer parentCount r 1)) :
        Set (RLayer parentCount r 1))).MapsTo
          (rCoordinateBitType parents coordinate)
          (Finset.univ : Finset (RBitType r)) := by
    intro sub _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hsubs :
      (Finset.univ : Finset (RLayer parentCount r 1)).card =
        parentCount.choose r := by
    rw [Finset.card_univ, rLayer_one_card]
  calc
    (∑ bitType : RBitType r,
        (rTypeGroup parents coordinate bitType).card) =
      (Finset.univ : Finset (RLayer parentCount r 1)).card := by
        simpa [rTypeGroup] using hpartition.symm
    _ = parentCount.choose r := hsubs

theorem rTypeGroup_card_le
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : RBitType r) :
    (rTypeGroup parents coordinate bitType).card ≤
      parentCount.choose r := by
  classical
  calc
    (rTypeGroup parents coordinate bitType).card ≤
      (Finset.univ : Finset (RLayer parentCount r 1)).card := by
        unfold rTypeGroup
        exact Finset.card_filter_le _ _
    _ = parentCount.choose r := by
      rw [Finset.card_univ, rLayer_one_card]

noncomputable def rTypeGroupChildOnes
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : RBitType r) : Finset (RLayer parentCount r 1) := by
  classical
  exact (rTypeGroup parents coordinate bitType).filter
    (fun sub => children sub coordinate = true)

theorem rTypeGroupChildOnes_card_le
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (bitType : RBitType r) :
    (rTypeGroupChildOnes parents children coordinate bitType).card ≤
      (rTypeGroup parents coordinate bitType).card := by
  classical
  unfold rTypeGroupChildOnes
  exact Finset.card_filter_le _ _

def flattenRChildArray
    {parentCount dimension r : ℕ}
    (children : RLayer parentCount r 1 → HammingWord dimension) :
    RLayer parentCount r 1 × Fin dimension → Bool :=
  fun index => children index.1 index.2

theorem rChildClassificationOnes_card
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (bitType : RBitType r) (coordinate : Fin dimension) :
    (classifiedWordOnes
      (rCoordinateClassification parents) (bitType, coordinate)
      (flattenRChildArray children)).card =
        (rTypeGroupChildOnes parents children coordinate bitType).card := by
  classical
  apply Finset.card_bij (fun index _ => index.1)
  · intro index hindex
    have hclassified :
        index ∈
          (classificationGroup (rCoordinateClassification parents)
            (bitType, coordinate)).filter
              (fun candidate =>
                flattenRChildArray children candidate = true) := by
      simpa only [classifiedWordOnes] using hindex
    have hparts := Finset.mem_filter.mp hclassified
    have hgroup := (Finset.mem_filter.mp hparts.1).2
    have htype := congrArg Prod.fst hgroup
    have hcoordinate := congrArg Prod.snd hgroup
    have hcoord : index.2 = coordinate := by
      simpa [rCoordinateClassification] using hcoordinate
    simp only [rTypeGroupChildOnes, Finset.mem_filter]
    constructor
    · simp only [rTypeGroup, Finset.mem_filter,
        Finset.mem_univ, true_and]
      simpa [rCoordinateClassification, hcoord] using htype
    · simpa [flattenRChildArray, hcoord] using hparts.2
  · intro first hfirst second hsecond hequal
    apply Prod.ext
    · exact hequal
    · have hfirst_group := (Finset.mem_filter.mp hfirst).1
      have hsecond_group := (Finset.mem_filter.mp hsecond).1
      have hfirst_class := (Finset.mem_filter.mp hfirst_group).2
      have hsecond_class := (Finset.mem_filter.mp hsecond_group).2
      have hfirst_coordinate := congrArg Prod.snd hfirst_class
      have hsecond_coordinate := congrArg Prod.snd hsecond_class
      simpa [rCoordinateClassification] using
        hfirst_coordinate.trans hsecond_coordinate.symm
  · intro sub hsub
    refine ⟨(sub, coordinate), ?_, rfl⟩
    have hsub_parts := Finset.mem_filter.mp hsub
    have hsub_type := (Finset.mem_filter.mp hsub_parts.1).2
    change
      (sub, coordinate) ∈
        (classificationGroup (rCoordinateClassification parents)
          (bitType, coordinate)).filter
            (fun index => flattenRChildArray children index = true)
    apply Finset.mem_filter.mpr
    constructor
    · unfold classificationGroup
      apply Finset.mem_filter.mpr
      refine ⟨Finset.mem_univ _, ?_⟩
      exact Prod.ext hsub_type rfl
    · exact hsub_parts.2

noncomputable def rChildCountProfile
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension) :
    RTypeCountProfile parentCount dimension r := by
  intro bitType coordinate
  refine
    ⟨(rTypeGroupChildOnes parents children coordinate bitType).card, ?_⟩
  have hones := rTypeGroupChildOnes_card_le
    parents children coordinate bitType
  have hgroup := rTypeGroup_card_le parents coordinate bitType
  omega

noncomputable def rChildArraysOfProfile
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : RTypeCountProfile parentCount dimension r) :
    Finset (RLayer parentCount r 1 → HammingWord dimension) := by
  classical
  exact Finset.univ.filter
    (fun children => rChildCountProfile parents children = profile)

noncomputable def rChildArraysOfProfileEquiv
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : RTypeCountProfile parentCount dimension r) :
    ↥(rChildArraysOfProfile parents profile) ≃
      ↥(classifiedBooleanWords
        (rCoordinateClassification parents)
        (fun index : (RBitType r) × Fin dimension =>
          (profile index.1 index.2).val)) := by
  classical
  refine
    { toFun := fun children =>
        ⟨flattenRChildArray children.val, ?_⟩
      invFun := fun word =>
        ⟨fun sub coordinate => word.val (sub, coordinate), ?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · have hmembership := children.property
    unfold rChildArraysOfProfile at hmembership
    have hprofile := (Finset.mem_filter.mp hmembership).2
    simp only [classifiedBooleanWords, Finset.mem_filter,
      Finset.mem_univ, true_and]
    rintro ⟨bitType, coordinate⟩
    rw [rChildClassificationOnes_card]
    have hcount := congrArg
      (fun candidate : RTypeCountProfile parentCount dimension r =>
        (candidate bitType coordinate).val) hprofile
    simpa [rChildCountProfile] using hcount
  · simp only [rChildArraysOfProfile, Finset.mem_filter,
      Finset.mem_univ, true_and]
    funext bitType
    funext coordinate
    apply Fin.ext
    change
      (rTypeGroupChildOnes parents
        (fun sub coordinate => word.val (sub, coordinate))
        coordinate bitType).card = (profile bitType coordinate).val
    have hmembership := word.property
    unfold classifiedBooleanWords at hmembership
    have hprofile :=
      (Finset.mem_filter.mp hmembership).2 (bitType, coordinate)
    rw [← rChildClassificationOnes_card]
    have hflatten :
        flattenRChildArray
          (fun sub coordinate => word.val (sub, coordinate)) =
            word.val := by
      funext index
      rcases index with ⟨sub, coordinate⟩
      rfl
    rw [hflatten]
    exact hprofile
  · intro children
    apply Subtype.ext
    funext sub
    funext coordinate
    rfl
  · intro word
    apply Subtype.ext
    funext index
    rcases index with ⟨sub, coordinate⟩
    rfl

/-- `(b)` For a fixed profile, the child arrays realizing it are counted
exactly by a product of binomial coefficients. -/
theorem rChildArraysOfProfile_card
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (profile : RTypeCountProfile parentCount dimension r) :
    (rChildArraysOfProfile parents profile).card =
      ∏ index : (RBitType r) × Fin dimension,
        ((rTypeGroup parents index.2 index.1).card).choose
          (profile index.1 index.2).val := by
  calc
    (rChildArraysOfProfile parents profile).card =
      Fintype.card ↥(rChildArraysOfProfile parents profile) :=
        (Fintype.card_coe _).symm
    _ = Fintype.card
      ↥(classifiedBooleanWords
        (rCoordinateClassification parents)
        (fun index : (RBitType r) × Fin dimension =>
          (profile index.1 index.2).val)) :=
        Fintype.card_congr
          (rChildArraysOfProfileEquiv parents profile)
    _ = (classifiedBooleanWords
        (rCoordinateClassification parents)
        (fun index : (RBitType r) × Fin dimension =>
          (profile index.1 index.2).val)).card :=
        Fintype.card_coe _
    _ = ∏ index : (RBitType r) × Fin dimension,
        (Fintype.card
          (ClassificationFiber
            (rCoordinateClassification parents) index)).choose
          (profile index.1 index.2).val :=
        classifiedBooleanWords_card
          (rCoordinateClassification parents)
          (fun index : (RBitType r) × Fin dimension =>
            (profile index.1 index.2).val)
    _ = ∏ index : (RBitType r) × Fin dimension,
        ((rTypeGroup parents index.2 index.1).card).choose
          (profile index.1 index.2).val := by
      apply Finset.prod_congr rfl
      rintro ⟨bitType, coordinate⟩ _
      rw [rCoordinateClassificationFiber_card]

/-! ## Empirical conditional entropy and the `2^{mME}` bound -/

noncomputable def rCoordinateConditionalEntropy
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension) : ℝ :=
  ∑ bitType : RBitType r,
    ((rTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose r : ℝ) *
      binaryEntropy
        (((rTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
          ((rTypeGroup parents coordinate bitType).card : ℝ))

noncomputable def rChildArrayEntropy
    {parentCount dimension r : ℕ}
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    rCoordinateConditionalEntropy parents children coordinate) /
      (dimension : ℝ)

theorem rCoordinateConditionalEntropy_mass
    {parentCount dimension r : ℕ} (hparents : r ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (parentCount.choose r : ℝ) *
        rCoordinateConditionalEntropy parents children coordinate =
      ∑ bitType : RBitType r,
        ((rTypeGroup parents coordinate bitType).card : ℝ) *
          binaryEntropy
            (((rTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((rTypeGroup parents coordinate bitType).card : ℝ)) := by
  have hsub : 0 < (parentCount.choose r : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  unfold rCoordinateConditionalEntropy
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro bitType _
  field_simp [hsub.ne']

theorem rCoordinateConditionalEntropy_log_mass
    {parentCount dimension r : ℕ} (hparents : r ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : RBitType r,
      ((rTypeGroup parents coordinate bitType).card : ℝ) *
        Real.binEntropy
          (((rTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
            ((rTypeGroup parents coordinate bitType).card : ℝ))) =
      (parentCount.choose r : ℝ) * Real.log 2 *
        rCoordinateConditionalEntropy parents children coordinate := by
  calc
    (∑ bitType : RBitType r,
        ((rTypeGroup parents coordinate bitType).card : ℝ) *
          Real.binEntropy
            (((rTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((rTypeGroup parents coordinate bitType).card : ℝ))) =
      (∑ bitType : RBitType r,
        ((rTypeGroup parents coordinate bitType).card : ℝ) *
          binaryEntropy
            (((rTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
              ((rTypeGroup parents coordinate bitType).card : ℝ))) *
        Real.log 2 := by
          rw [Finset.sum_mul]
          apply Finset.sum_congr rfl
          intro bitType _
          unfold binaryEntropy
          field_simp [Real.log_pos (by norm_num : (1:ℝ) < 2) |>.ne']
    _ = (parentCount.choose r : ℝ) * Real.log 2 *
        rCoordinateConditionalEntropy parents children coordinate := by
      rw [← rCoordinateConditionalEntropy_mass
        hparents parents children coordinate]
      ring

theorem rChildGroup_choose_product_entropy_bound
    {parentCount dimension r : ℕ} (hparents : r ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension) :
    (∏ index : (RBitType r) × Fin dimension,
      ((rTypeGroup parents index.2 index.1).card).choose
        ((rTypeGroupChildOnes parents children
          index.2 index.1).card) : ℝ) ≤
      Real.exp
        ((parentCount.choose r : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            rCoordinateConditionalEntropy parents children
              coordinate)) := by
  have hproduct := choose_product_le_exp_binary_entropy
    (ι := (RBitType r) × Fin dimension)
    (fun index => (rTypeGroup parents index.2 index.1).card)
    (fun index =>
      (rTypeGroupChildOnes parents children index.2 index.1).card)
    (fun index => rTypeGroupChildOnes_card_le
      parents children index.2 index.1)
  have hsum :
      (∑ index : (RBitType r) × Fin dimension,
        ((rTypeGroup parents index.2 index.1).card : ℝ) *
          Real.binEntropy
            (((rTypeGroupChildOnes parents children
                index.2 index.1).card : ℝ) /
              ((rTypeGroup parents index.2 index.1).card : ℝ))) =
        (parentCount.choose r : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            rCoordinateConditionalEntropy parents children
              coordinate) := by
    rw [Fintype.sum_prod_type, Finset.sum_comm]
    simp_rw [rCoordinateConditionalEntropy_log_mass
      hparents parents children]
    rw [Finset.mul_sum]
  rw [hsum] at hproduct
  exact hproduct

/-- `(b)` The child arrays sharing the profile of a given child array number at
most `2^{m M E}` where `E` is that array's average conditional entropy. -/
theorem rChildArraysOfRealizedProfile_card_le
    {parentCount dimension r : ℕ} (hparents : r ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension) :
    ((rChildArraysOfProfile parents
        (rChildCountProfile parents children)).card : ℝ) ≤
      Real.exp
        ((parentCount.choose r : ℝ) * Real.log 2 *
          (∑ coordinate : Fin dimension,
            rCoordinateConditionalEntropy parents children
              coordinate)) := by
  have hcard :
      ((rChildArraysOfProfile parents
        (rChildCountProfile parents children)).card : ℝ) =
        ∏ index : (RBitType r) × Fin dimension,
          (((rTypeGroup parents index.2 index.1).card).choose
            ((rTypeGroupChildOnes parents children
              index.2 index.1).card) : ℝ) := by
    exact_mod_cast
      rChildArraysOfProfile_card parents
        (rChildCountProfile parents children)
  rw [hcard]
  exact rChildGroup_choose_product_entropy_bound
    hparents parents children

/-! ## The union over profiles

`(a) + (b)`: the low-entropy ("bad") child arrays number at most
`(M+1)^{(r+1)m} · 2^{m M · threshold}`, `M = parentCount.choose r`. -/

noncomputable def badRChildArrays
    {parentCount dimension : ℕ} (r : ℕ)
    (parents : Fin parentCount → HammingWord dimension)
    (threshold : ℝ) :
    Finset (RLayer parentCount r 1 → HammingWord dimension) := by
  classical
  exact Finset.univ.filter
    (fun children => rChildArrayEntropy parents children ≤ threshold)

theorem badRChildArrays_card_le
    {parentCount dimension r : ℕ}
    (hparents : r ≤ parentCount)
    (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (threshold : ℝ) :
    ((badRChildArrays r parents threshold).card : ℝ) ≤
      (((parentCount.choose r + 1) ^ ((r + 1) * dimension) : ℕ) : ℝ) *
        Real.exp
          ((parentCount.choose r : ℝ) * Real.log 2 *
            (dimension : ℝ) * threshold) := by
  classical
  let bound : ℝ :=
    Real.exp
      ((parentCount.choose r : ℝ) * Real.log 2 *
        (dimension : ℝ) * threshold)
  have hbound_nonneg : 0 ≤ bound := by
    dsimp [bound]
    exact (Real.exp_pos _).le
  have hmaps :
      ((badRChildArrays r parents threshold :
        Finset (RLayer parentCount r 1 → HammingWord dimension)) :
        Set (RLayer parentCount r 1 → HammingWord dimension)).MapsTo
        (rChildCountProfile parents)
        (Finset.univ :
          Finset (RTypeCountProfile parentCount dimension r)) := by
    intro children _
    exact Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (profile : RTypeCountProfile parentCount dimension r) :
      (((badRChildArrays r parents threshold).filter
        (fun children =>
          rChildCountProfile parents children = profile)).card : ℝ) ≤
        bound := by
    by_cases hnonempty :
        ((badRChildArrays r parents threshold).filter
          (fun children =>
            rChildCountProfile parents children = profile)).Nonempty
    · obtain ⟨children, hchildren⟩ := hnonempty
      have hparts := Finset.mem_filter.mp hchildren
      have hprofile : rChildCountProfile parents children = profile :=
        hparts.2
      have hbad : rChildArrayEntropy parents children ≤ threshold := by
        have hmembership :
            children ∈
              (Finset.univ.filter
                (fun candidate : RLayer parentCount r 1 →
                    HammingWord dimension =>
                  rChildArrayEntropy parents candidate ≤ threshold)) := by
          simpa only [badRChildArrays] using hparts.1
        exact (Finset.mem_filter.mp hmembership).2
      have hsubset :
          (badRChildArrays r parents threshold).filter
              (fun candidate =>
                rChildCountProfile parents candidate = profile) ⊆
            rChildArraysOfProfile parents profile := by
        intro candidate hcandidate
        have hcandidate_profile := (Finset.mem_filter.mp hcandidate).2
        unfold rChildArraysOfProfile
        exact Finset.mem_filter.mpr
          ⟨Finset.mem_univ _, hcandidate_profile⟩
      have hcard :
          (((badRChildArrays r parents threshold).filter
            (fun candidate =>
              rChildCountProfile parents candidate =
                profile)).card : ℝ) ≤
            ((rChildArraysOfProfile parents profile).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsubset
      have hrealized :
          ((rChildArraysOfProfile parents profile).card : ℝ) ≤
            Real.exp
              ((parentCount.choose r : ℝ) * Real.log 2 *
                (∑ coordinate : Fin dimension,
                  rCoordinateConditionalEntropy
                    parents children coordinate)) := by
        rw [← hprofile]
        exact rChildArraysOfRealizedProfile_card_le
          hparents parents children
      have hdimension_real : 0 < (dimension : ℝ) := by
        exact_mod_cast hdimension
      have hsum :
          (∑ coordinate : Fin dimension,
            rCoordinateConditionalEntropy parents children
              coordinate) ≤ (dimension : ℝ) * threshold := by
        unfold rChildArrayEntropy at hbad
        have hcleared := (div_le_iff₀ hdimension_real).mp hbad
        nlinarith
      have hcoefficient :
          0 ≤ (parentCount.choose r : ℝ) * Real.log 2 :=
        mul_nonneg (Nat.cast_nonneg _)
          (Real.log_pos (by norm_num : (1:ℝ) < 2)).le
      have hexponential :
          Real.exp
              ((parentCount.choose r : ℝ) * Real.log 2 *
                (∑ coordinate : Fin dimension,
                  rCoordinateConditionalEntropy
                    parents children coordinate)) ≤ bound := by
        dsimp [bound]
        apply Real.exp_le_exp.mpr
        nlinarith [mul_le_mul_of_nonneg_left hsum hcoefficient]
      exact hcard.trans (hrealized.trans hexponential)
    · have hempty :
          (badRChildArrays r parents threshold).filter
            (fun children =>
              rChildCountProfile parents children = profile) = ∅ :=
          Finset.not_nonempty_iff_eq_empty.mp hnonempty
      simpa [hempty] using hbound_nonneg
  calc
    ((badRChildArrays r parents threshold).card : ℝ) =
        ∑ profile : RTypeCountProfile parentCount dimension r,
          (((badRChildArrays r parents threshold).filter
            (fun children =>
              rChildCountProfile parents children =
                profile)).card : ℝ) := by
      exact_mod_cast hpartition
    _ ≤ ∑ _profile : RTypeCountProfile parentCount dimension r, bound := by
      exact Finset.sum_le_sum (fun profile _ => hfiber profile)
    _ = (((parentCount.choose r + 1) ^ ((r + 1) * dimension) : ℕ) : ℝ) *
          Real.exp
            ((parentCount.choose r : ℝ) * Real.log 2 *
              (dimension : ℝ) * threshold) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
        rTypeCountProfile_card]

/-! ## `(c)` The union-bound exponent

Parent arrays number `2^{mL}`; profiles `(M+1)^{(r+1)m}`; bad child arrays per
profile `2^{mM(β-δ)}`; each such child array survives retention with
probability `p^M = 2^{-βmM}`.  Multiplying gives exactly

`exp( m · log 2 · [ L + (r+1)·log₂(M+1) − δ·M ] )`,  `M = parentCount.choose r`,

which is the `r`-generic form of `THEOREM_r3.md` step 5.  This is an identity, so
it is proved here for an arbitrary retention exponent `beta` and slack `slack`
(the published `r = 2` version hardwires `midpointBeta`/`entropySlack`). -/
theorem badRLayerRetentionBound_eq_exp
    (parentCount dimension r : ℕ) (beta slack : ℝ) :
    ((((2 ^ (dimension * parentCount) : ℕ) : ℝ) *
      (((parentCount.choose r + 1) ^ ((r + 1) * dimension) : ℕ) : ℝ) *
      Real.exp
        ((parentCount.choose r : ℝ) * Real.log 2 *
          (dimension : ℝ) * (beta - slack))) *
        Real.exp (-(beta * (dimension : ℝ) * Real.log 2)) ^
          (parentCount.choose r)) =
      Real.exp
        ((dimension : ℝ) * Real.log 2 *
          ((parentCount : ℝ) +
            ((r : ℝ) + 1) * logTwo ((parentCount.choose r + 1 : ℕ) : ℝ) -
              slack * (parentCount.choose r : ℝ))) := by
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
      (((parentCount.choose r + 1) ^ ((r + 1) * dimension) : ℕ) : ℝ) =
        Real.exp
          ((((r + 1) * dimension : ℕ) : ℝ) *
            Real.log ((parentCount.choose r + 1 : ℕ) : ℝ)) := by
    calc
      (((parentCount.choose r + 1) ^ ((r + 1) * dimension) : ℕ) : ℝ) =
          (((parentCount.choose r + 1 : ℕ) : ℝ)) ^ ((r + 1) * dimension) := by
            norm_cast
      _ = Real.exp
          ((((r + 1) * dimension : ℕ) : ℝ) *
            Real.log ((parentCount.choose r + 1 : ℕ) : ℝ)) := by
            rw [Real.exp_nat_mul, Real.exp_log (by positivity)]
  have hretention :
      Real.exp (-(beta * (dimension : ℝ) * Real.log 2)) ^
          (parentCount.choose r) =
        Real.exp
          ((parentCount.choose r : ℝ) *
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

end RGenericProfiles
