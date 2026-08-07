import Sampling3
import Kernel3

/-!
# The `r = 3` empirical kernel bridge and the layer-exclusion argument

Port of the two published `r = 2` blocks of `CompactnessAndDegeneracy.lean`
(lines 13318–14330, the `pairCoordinateKernel` / `empirical*` family, and lines
16837–17590, the `pairGraphCopy*` potential machinery) to `r = 3`.

See `research/results_M_lean_assembly.md`.
-/

namespace ThreeBridge

open Finset TwoDegenerateGraphs ThreeDegenerateProfiles ThreeDegenerateGraphs
open scoped BigOperators

/-! ## Part 0: a Vandermonde-style splitting lemma

The number of `n`-subsets of `s` containing exactly `j` points satisfying a
predicate `p` is `C(|s ∩ p|, j) · C(|s ∖ p|, n - j)`. -/

theorem card_powersetCard_filter_pred {α : Type*} [DecidableEq α]
    (s : Finset α) (p : α → Prop) [DecidablePred p] (n j : ℕ) (hjn : j ≤ n) :
    (((s.powersetCard n).filter (fun u => (u.filter p).card = j))).card =
      (s.filter p).card.choose j *
        (s.filter (fun x => ¬ p x)).card.choose (n - j) := by
  classical
  rw [← Finset.card_powersetCard, ← Finset.card_powersetCard,
    ← Finset.card_product]
  refine Finset.card_bij'
    (fun u _ => (u.filter p, u.filter (fun x => ¬ p x)))
    (fun P _ => P.1 ∪ P.2)
    ?_ ?_ ?_ ?_
  · intro u hu
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hu
    obtain ⟨⟨hsub, hcard⟩, hj⟩ := hu
    rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
    have hsplit : (u.filter p).card + (u.filter (fun x => ¬ p x)).card = u.card :=
      Finset.card_filter_add_card_filter_not (p := p)
    refine ⟨⟨Finset.filter_subset_filter p hsub, hj⟩,
      Finset.filter_subset_filter _ hsub, ?_⟩
    · show (u.filter (fun x => ¬ p x)).card = n - j
      omega
  · rintro ⟨P, Q⟩ hPQ
    rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
      at hPQ
    obtain ⟨⟨hP, hPcard⟩, hQ, hQcard⟩ := hPQ
    simp only at hP hPcard hQ hQcard
    have hPp : ∀ x ∈ P, p x := fun x hx => (Finset.mem_filter.mp (hP hx)).2
    have hQp : ∀ x ∈ Q, ¬ p x := fun x hx => (Finset.mem_filter.mp (hQ hx)).2
    have hdisj : Disjoint P Q :=
      Finset.disjoint_left.mpr fun x hx hx' => hQp x hx' (hPp x hx)
    have hfP : (P ∪ Q).filter p = P := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hpx⟩
        · exact hx
        · exact absurd hpx (hQp x hx)
      · intro hx; exact ⟨Or.inl hx, hPp x hx⟩
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    refine ⟨⟨fun x hx => ?_, ?_⟩, ?_⟩
    · rcases Finset.mem_union.mp hx with h | h
      · exact Finset.mem_of_mem_filter _ (hP h)
      · exact Finset.mem_of_mem_filter _ (hQ h)
    · rw [Finset.card_union_of_disjoint hdisj]; omega
    · rw [hfP]; exact hPcard
  · intro u hu
    simp only
    ext x
    simp only [Finset.mem_union, Finset.mem_filter]
    tauto
  · rintro ⟨P, Q⟩ hPQ
    rw [Finset.mem_product, Finset.mem_powersetCard, Finset.mem_powersetCard]
      at hPQ
    obtain ⟨⟨hP, hPcard⟩, hQ, hQcard⟩ := hPQ
    simp only at hP hQ
    have hPp : ∀ x ∈ P, p x := fun x hx => (Finset.mem_filter.mp (hP hx)).2
    have hQp : ∀ x ∈ Q, ¬ p x := fun x hx => (Finset.mem_filter.mp (hQ hx)).2
    have hfP : (P ∪ Q).filter p = P := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hpx⟩
        · exact hx
        · exact absurd hpx (hQp x hx)
      · intro hx; exact ⟨Or.inl hx, hPp x hx⟩
    have hfQ : (P ∪ Q).filter (fun x => ¬ p x) = Q := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_union]
      constructor
      · rintro ⟨hx | hx, hpx⟩
        · exact absurd (hPp x hx) hpx
        · exact hx
      · intro hx; exact ⟨Or.inr hx, hQp x hx⟩
    simp only [Prod.mk.injEq]
    exact ⟨hfP, hfQ⟩

/-! ## Part 1: the four type-group cardinalities

Write `k` for the number of parents carrying a `1` at the coordinate.  The
group of triples of type `j` has `C(k, j) · C(L - k, 3 - j)` members. -/

theorem cast_choose_two (k : ℕ) :
    ((k.choose 2 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) / 2 := by
  rw [Nat.cast_choose_two]

theorem cast_choose_three (k : ℕ) :
    ((k.choose 3 : ℕ) : ℝ) = (k : ℝ) * ((k : ℝ) - 1) * ((k : ℝ) - 2) / 6 := by
  induction k with
  | zero => simp
  | succ n ih =>
      have hstep : (n + 1).choose 3 = n.choose 2 + n.choose 3 :=
        Nat.choose_succ_succ' n 2
      rw [hstep]
      have h2 := cast_choose_two n
      push_cast at ih h2 ⊢
      rw [ih, h2]
      ring

/-- The number of ones among the three ordered outcomes. -/
def tripleBitTypeOfOutcomes : Bool → Bool → Bool → TripleBitType
  | false, false, false => 0
  | true, false, false => 1
  | false, true, false => 1
  | false, false, true => 1
  | true, true, false => 2
  | true, false, true => 2
  | false, true, true => 2
  | true, true, true => 3

variable {parentCount dimension : ℕ}

theorem tripleTypeGroup_card
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) (bitType : TripleBitType) :
    (tripleTypeGroup parents coordinate bitType).card =
      (pairParentCoordinateOneCount parents coordinate).choose bitType.val *
        (parentCount - pairParentCoordinateOneCount parents coordinate).choose
          (3 - bitType.val) := by
  classical
  have honescard :
      ((Finset.univ : Finset (Fin parentCount)).filter
        (fun parent => parents parent coordinate = true)).card =
        pairParentCoordinateOneCount parents coordinate := rfl
  have hzerocard :
      ((Finset.univ : Finset (Fin parentCount)).filter
        (fun parent => ¬ (parents parent coordinate = true))).card =
        parentCount - pairParentCoordinateOneCount parents coordinate := by
    have hpartition :=
      Finset.card_filter_add_card_filter_not
        (s := (Finset.univ : Finset (Fin parentCount)))
        (p := fun parent => parents parent coordinate = true)
    rw [honescard] at hpartition
    have huniv : (Finset.univ : Finset (Fin parentCount)).card = parentCount := by
      simp
    omega
  have hsplit := card_powersetCard_filter_pred
    (Finset.univ : Finset (Fin parentCount))
    (fun parent => parents parent coordinate = true) 3 bitType.val
    (by omega)
  rw [honescard, hzerocard] at hsplit
  rw [← hsplit]
  refine Finset.card_bij (fun T _ => (T.val : Finset (Fin parentCount))) ?_ ?_ ?_
  · intro T hT
    have htype : tripleCoordinateBitType parents coordinate T = bitType :=
      (Finset.mem_filter.mp hT).2
    have hval : (T.val.filter
        (fun parent => parents parent coordinate = true)).card = bitType.val :=
      congrArg Fin.val htype
    rw [Finset.mem_filter, Finset.mem_powersetCard]
    exact ⟨⟨Finset.subset_univ _, T.property⟩, hval⟩
  · intro T _ S _ heq
    exact Subtype.ext heq
  · intro u hu
    rw [Finset.mem_filter, Finset.mem_powersetCard] at hu
    refine ⟨⟨u, hu.1.2⟩, ?_, rfl⟩
    simp only [tripleTypeGroup, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.ext hu.2

/-! ### The four group cardinalities, in real form -/

section GroupCards

variable (parents : Fin parentCount → HammingWord dimension)
  (coordinate : Fin dimension)

theorem cast_parent_sub :
    ((parentCount - pairParentCoordinateOneCount parents coordinate : ℕ) : ℝ) =
      (parentCount : ℝ) -
        (pairParentCoordinateOneCount parents coordinate : ℝ) :=
  Nat.cast_sub (pairParentCoordinateOneCount_le parents coordinate)

theorem group_card_zero :
    ((tripleTypeGroup parents coordinate 0).card : ℝ) =
      ((parentCount : ℝ) - (pairParentCoordinateOneCount parents coordinate : ℝ)) *
        (((parentCount : ℝ) -
          (pairParentCoordinateOneCount parents coordinate : ℝ)) - 1) *
        (((parentCount : ℝ) -
          (pairParentCoordinateOneCount parents coordinate : ℝ)) - 2) / 6 := by
  rw [tripleTypeGroup_card]
  show (((pairParentCoordinateOneCount parents coordinate).choose 0 *
    (parentCount - pairParentCoordinateOneCount parents coordinate).choose 3 : ℕ) : ℝ) = _
  rw [Nat.choose_zero_right, Nat.cast_mul, Nat.cast_one, one_mul,
    cast_choose_three, cast_parent_sub]

theorem group_card_one :
    ((tripleTypeGroup parents coordinate 1).card : ℝ) =
      (pairParentCoordinateOneCount parents coordinate : ℝ) *
        (((parentCount : ℝ) -
          (pairParentCoordinateOneCount parents coordinate : ℝ)) *
          (((parentCount : ℝ) -
            (pairParentCoordinateOneCount parents coordinate : ℝ)) - 1) / 2) := by
  rw [tripleTypeGroup_card]
  show (((pairParentCoordinateOneCount parents coordinate).choose 1 *
    (parentCount - pairParentCoordinateOneCount parents coordinate).choose 2 : ℕ) : ℝ) = _
  rw [Nat.choose_one_right, Nat.cast_mul, cast_choose_two, cast_parent_sub]

theorem group_card_two :
    ((tripleTypeGroup parents coordinate 2).card : ℝ) =
      ((pairParentCoordinateOneCount parents coordinate : ℝ) *
        ((pairParentCoordinateOneCount parents coordinate : ℝ) - 1) / 2) *
        ((parentCount : ℝ) -
          (pairParentCoordinateOneCount parents coordinate : ℝ)) := by
  rw [tripleTypeGroup_card]
  show (((pairParentCoordinateOneCount parents coordinate).choose 2 *
    (parentCount - pairParentCoordinateOneCount parents coordinate).choose 1 : ℕ) : ℝ) = _
  rw [Nat.choose_one_right, Nat.cast_mul, cast_choose_two, cast_parent_sub]

theorem group_card_three :
    ((tripleTypeGroup parents coordinate 3).card : ℝ) =
      (pairParentCoordinateOneCount parents coordinate : ℝ) *
        ((pairParentCoordinateOneCount parents coordinate : ℝ) - 1) *
        ((pairParentCoordinateOneCount parents coordinate : ℝ) - 2) / 6 := by
  rw [tripleTypeGroup_card]
  show (((pairParentCoordinateOneCount parents coordinate).choose 3 *
    (parentCount - pairParentCoordinateOneCount parents coordinate).choose 0 : ℕ) : ℝ) = _
  rw [Nat.choose_zero_right, Nat.cast_mul, Nat.cast_one, mul_one,
    cast_choose_three]

end GroupCards

/-! ## Part 2: the without-replacement mass in terms of the type groups

An ordered triple of *distinct* parent slots with outcome pattern `(l, m, r)`
of type `j` has without-replacement mass `|G_j| / C(L,3) · j!(3-j)!/6`; the
weight is `1` for the two homogeneous types and `1/3` for the two mixed ones. -/

/-- The multiplicity weight `j!(3-j)!/6`. -/
noncomputable def tripleOutcomeWeight (l m r : Bool) : ℝ :=
  if l = m ∧ m = r then 1 else 1 / 3

theorem worMass_eq_tripleTypeGroup
    (hparents : 3 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) (l m r : Bool) :
    withoutReplacementBinaryTripleMass parentCount
        (pairParentCoordinateOneCount parents coordinate) l m r =
      ((tripleTypeGroup parents coordinate
          (tripleBitTypeOfOutcomes l m r)).card : ℝ) /
        (parentCount.choose 3 : ℝ) * tripleOutcomeWeight l m r := by
  have hN : (3 : ℝ) ≤ (parentCount : ℝ) := by exact_mod_cast hparents
  have hchoose : ((parentCount.choose 3 : ℕ) : ℝ) =
      (parentCount : ℝ) * ((parentCount : ℝ) - 1) * ((parentCount : ℝ) - 2) / 6 :=
    cast_choose_three parentCount
  have hD : (0 : ℝ) <
      (parentCount : ℝ) * ((parentCount : ℝ) - 1) * ((parentCount : ℝ) - 2) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hg0 := group_card_zero parents coordinate
  have hg1 := group_card_one parents coordinate
  have hg2 := group_card_two parents coordinate
  have hg3 := group_card_three parents coordinate
  cases l <;> cases m <;> cases r <;>
    simp only [tripleBitTypeOfOutcomes, tripleOutcomeWeight,
      withoutReplacementBinaryTripleMass, empiricalBinaryOutcomeCount,
      if_true, if_false, and_true, and_false,
      Bool.false_eq_true, reduceCtorEq] <;>
    rw [hchoose] <;>
    [rw [hg0]; rw [hg1]; rw [hg1]; rw [hg2]; rw [hg1]; rw [hg2]; rw [hg2];
      rw [hg3]] <;>
    field_simp <;> ring

/-! ## Part 3: expectations under the without-replacement law -/

noncomputable def worTripleExpectation (parentCount oneCount : ℕ)
    (f : Bool → Bool → Bool → ℝ) : ℝ :=
  ∑ l : Bool, ∑ m : Bool, ∑ r : Bool,
    withoutReplacementBinaryTripleMass parentCount oneCount l m r * f l m r

noncomputable def iidTripleExpectation (q : ℝ) (f : Bool → Bool → Bool → ℝ) : ℝ :=
  ∑ l : Bool, ∑ m : Bool, ∑ r : Bool,
    independentBinaryTripleMass q l m r * f l m r

theorem sum_triple_prod (f : Bool → Bool → Bool → ℝ) :
    ∑ x : Bool × Bool × Bool, f x.1 x.2.1 x.2.2 =
      ∑ l : Bool, ∑ m : Bool, ∑ r : Bool, f l m r := by
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl fun l _ => Fintype.sum_prod_type _

theorem worMass_nonneg
    (hparents : 3 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) (l m r : Bool) :
    0 ≤ withoutReplacementBinaryTripleMass parentCount
      (pairParentCoordinateOneCount parents coordinate) l m r := by
  rw [worMass_eq_tripleTypeGroup hparents parents coordinate]
  have hchoose : (0 : ℝ) < (parentCount.choose 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  have hweight : 0 ≤ tripleOutcomeWeight l m r := by
    unfold tripleOutcomeWeight; split <;> norm_num
  have hcard : (0 : ℝ) ≤
      ((tripleTypeGroup parents coordinate
        (tripleBitTypeOfOutcomes l m r)).card : ℝ) := by positivity
  exact mul_nonneg (div_nonneg hcard hchoose.le) hweight

/-- The coupling error between the without-replacement and the i.i.d. law, on
any `[0,1]`-valued observable. -/
theorem worTripleExpectation_error
    (hparents : 10 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (f : Bool → Bool → Bool → ℝ)
    (hf0 : ∀ l m r, 0 ≤ f l m r) (hf1 : ∀ l m r, f l m r ≤ 1) :
    |worTripleExpectation parentCount
        (pairParentCoordinateOneCount parents coordinate) f -
      iidTripleExpectation
        ((pairParentCoordinateOneCount parents coordinate : ℝ) /
          (parentCount : ℝ)) f| ≤ 4 / (parentCount : ℝ) := by
  classical
  set oneCount := pairParentCoordinateOneCount parents coordinate with hone
  have h3 : 3 ≤ parentCount := by omega
  have hones : oneCount ≤ parentCount := pairParentCoordinateOneCount_le _ _
  have hNpos : (0 : ℝ) < (parentCount : ℝ) := by
    have : (10 : ℝ) ≤ (parentCount : ℝ) := by exact_mod_cast hparents
    linarith
  set q : ℝ := (oneCount : ℝ) / (parentCount : ℝ) with hq
  set c : ℝ := (parentCount : ℝ) ^ 3 /
    ((parentCount : ℝ) * ((parentCount : ℝ) - 1) * ((parentCount : ℝ) - 2)) with hc
  have hD : (0 : ℝ) <
      (parentCount : ℝ) * ((parentCount : ℝ) - 1) * ((parentCount : ℝ) - 2) := by
    have : (10 : ℝ) ≤ (parentCount : ℝ) := by exact_mod_cast hparents
    exact mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hqnonneg : 0 ≤ q := by rw [hq]; positivity
  have hqone : q ≤ 1 := by
    rw [hq]; exact (div_le_one hNpos).mpr (by exact_mod_cast hones)
  have hcone : 1 ≤ c := by
    rw [hc, le_div_iff₀ hD]
    have : (10 : ℝ) ≤ (parentCount : ℝ) := by exact_mod_cast hparents
    nlinarith
  have hdom := abs_expectation_sub_le_of_dominated
    (ι := Bool × Bool × Bool)
    (fun x => withoutReplacementBinaryTripleMass parentCount oneCount
      x.1 x.2.1 x.2.2)
    (fun x => independentBinaryTripleMass q x.1 x.2.1 x.2.2)
    c (fun x => f x.1 x.2.1 x.2.2)
    (fun x => worMass_nonneg h3 parents coordinate _ _ _)
    (fun x => independentBinaryTripleMass_nonneg hqnonneg hqone _ _ _)
    (by
      rw [sum_triple_prod
        (fun l m r => withoutReplacementBinaryTripleMass parentCount oneCount l m r)]
      exact withoutReplacementBinaryTripleMass_sum h3)
    (by
      rw [sum_triple_prod (fun l m r => independentBinaryTripleMass q l m r)]
      exact independentBinaryTripleMass_sum q)
    (fun x => withoutReplacementBinaryTripleMass_le h3 hones _ _ _)
    (fun x => hf0 _ _ _) (fun x => hf1 _ _ _) hcone
  rw [sum_triple_prod
      (fun l m r => withoutReplacementBinaryTripleMass parentCount oneCount l m r * f l m r),
    sum_triple_prod (fun l m r => independentBinaryTripleMass q l m r * f l m r)] at hdom
  exact hdom.trans (domination_constant_le parentCount hparents)

/-! ## Part 4: the coordinate kernel -/

noncomputable def tripleChildCoordinateOneCount
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : ℕ :=
  (booleanWordOnes (fun triple => children triple coordinate)).card

theorem sum_tripleTypeGroupChildOnes_card
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : TripleBitType,
      (tripleTypeGroupChildOnes parents children coordinate bitType).card) =
      tripleChildCoordinateOneCount children coordinate := by
  classical
  set support : Finset (TripleLayer parentCount 1) :=
    booleanWordOnes (fun triple => children triple coordinate) with hsupport
  have hmaps :
      ((support : Finset (TripleLayer parentCount 1)) :
        Set (TripleLayer parentCount 1)).MapsTo
          (tripleCoordinateBitType parents coordinate)
          (Finset.univ : Finset TripleBitType) := fun _ _ => Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (bitType : TripleBitType) :
      support.filter
        (fun triple =>
          tripleCoordinateBitType parents coordinate triple = bitType) =
      tripleTypeGroupChildOnes parents children coordinate bitType := by
    ext triple
    simp [hsupport, booleanWordOnes, tripleTypeGroupChildOnes, tripleTypeGroup,
      and_comm]
  calc
    (∑ bitType : TripleBitType,
      (tripleTypeGroupChildOnes parents children coordinate bitType).card) =
        ∑ bitType : TripleBitType,
          (support.filter
            (fun triple =>
              tripleCoordinateBitType parents coordinate triple =
                bitType)).card := by
        exact Finset.sum_congr rfl fun bitType _ => by rw [hfiber]
    _ = support.card := hpartition.symm
    _ = tripleChildCoordinateOneCount children coordinate := rfl

noncomputable def tripleCoordinateKernel
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) : BinaryTripleKernel where
  parentProbability :=
    (pairParentCoordinateOneCount parents coordinate : ℝ) / (parentCount : ℝ)
  parentProbability_nonneg := by positivity
  parentProbability_le_one := by
    have hpositive : (0 : ℝ) < (parentCount : ℝ) := by exact_mod_cast hparents
    exact (div_le_one hpositive).mpr
      (by exact_mod_cast pairParentCoordinateOneCount_le parents coordinate)
  childProbability l m r :=
    ((tripleTypeGroupChildOnes parents children coordinate
      (tripleBitTypeOfOutcomes l m r)).card : ℝ) /
        ((tripleTypeGroup parents coordinate
          (tripleBitTypeOfOutcomes l m r)).card : ℝ)
  childProbability_nonneg := by intro l m r; positivity
  childProbability_le_one := by
    intro l m r
    set bitType := tripleBitTypeOfOutcomes l m r with hbit
    have hle := tripleTypeGroupChildOnes_card_le parents children coordinate bitType
    by_cases hzero : (tripleTypeGroup parents coordinate bitType).card = 0
    · rw [hzero]; simp
    · have hpositive :
          (0 : ℝ) < ((tripleTypeGroup parents coordinate bitType).card : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      exact (div_le_one hpositive).mpr (by exact_mod_cast hle)

theorem tripleCoordinateKernel_childProbability
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) (l m r : Bool) :
    (tripleCoordinateKernel hparents parents children coordinate).childProbability
        l m r =
      ((tripleTypeGroupChildOnes parents children coordinate
        (tripleBitTypeOfOutcomes l m r)).card : ℝ) /
          ((tripleTypeGroup parents coordinate
            (tripleBitTypeOfOutcomes l m r)).card : ℝ) := rfl

/-- Any observable that only depends on the *type* of the ordered triple has
without-replacement expectation the type-weighted average. -/
theorem worTripleExpectation_of_type
    (hparents : 3 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (f : Bool → Bool → Bool → ℝ) (g : TripleBitType → ℝ)
    (hf : ∀ l m r, f l m r = g (tripleBitTypeOfOutcomes l m r)) :
    worTripleExpectation parentCount
        (pairParentCoordinateOneCount parents coordinate) f =
      ∑ bitType : TripleBitType,
        ((tripleTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 3 : ℝ) * g bitType := by
  unfold worTripleExpectation
  simp_rw [worMass_eq_tripleTypeGroup hparents parents coordinate, hf]
  rw [Fin.sum_univ_four]
  simp only [Fintype.sum_bool, tripleBitTypeOfOutcomes, tripleOutcomeWeight,
    Bool.false_eq_true, reduceCtorEq, and_true, and_false,
    if_true, if_false]
  ring

/-! ### The three empirical functionals -/

theorem group_prob_mul_ratio
    (hparents : 3 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) (bitType : TripleBitType) :
    ((tripleTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 3 : ℝ) *
      (((tripleTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
        ((tripleTypeGroup parents coordinate bitType).card : ℝ)) =
      ((tripleTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
        (parentCount.choose 3 : ℝ) := by
  have hchoose : (0 : ℝ) < (parentCount.choose 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  by_cases hgroup : (tripleTypeGroup parents coordinate bitType).card = 0
  · have hchild : (tripleTypeGroupChildOnes parents children
        coordinate bitType).card = 0 := by
      have hle := tripleTypeGroupChildOnes_card_le parents children coordinate bitType
      omega
    simp [hgroup, hchild]
  · have hgroup_real :
        ((tripleTypeGroup parents coordinate bitType).card : ℝ) ≠ 0 := by
      exact_mod_cast hgroup
    field_simp

theorem group_prob_mul_complement
    (hparents : 3 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) (bitType : TripleBitType) :
    ((tripleTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 3 : ℝ) *
      (1 - ((tripleTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
        ((tripleTypeGroup parents coordinate bitType).card : ℝ)) =
      (((tripleTypeGroup parents coordinate bitType).card : ℝ) -
        ((tripleTypeGroupChildOnes parents children coordinate bitType).card : ℝ)) /
        (parentCount.choose 3 : ℝ) := by
  have h := group_prob_mul_ratio hparents parents children coordinate bitType
  calc ((tripleTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 3 : ℝ) *
      (1 - ((tripleTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
        ((tripleTypeGroup parents coordinate bitType).card : ℝ)) =
      ((tripleTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 3 : ℝ) -
        (((tripleTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 3 : ℝ) *
          (((tripleTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
            ((tripleTypeGroup parents coordinate bitType).card : ℝ))) := by ring
    _ = ((tripleTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 3 : ℝ) -
        ((tripleTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
          (parentCount.choose 3 : ℝ) := by rw [h]
    _ = _ := by ring

theorem tripleCoordinateKernel_worConditionalEntropy
    (hparents : 3 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    worTripleExpectation parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (fun l m r => binaryEntropy
          ((tripleCoordinateKernel (by omega) parents children
            coordinate).childProbability l m r)) =
      tripleCoordinateConditionalEntropy parents children coordinate := by
  have h := worTripleExpectation_of_type hparents parents coordinate
    (fun l m r => binaryEntropy
      ((tripleCoordinateKernel (by omega : 0 < parentCount) parents children
        coordinate).childProbability l m r))
    (fun bitType => binaryEntropy
      (((tripleTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
        ((tripleTypeGroup parents coordinate bitType).card : ℝ)))
    (fun l m r => rfl)
  rw [h]
  rfl

theorem tripleCoordinateKernel_worChildMarginal
    (hparents : 3 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    worTripleExpectation parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (tripleCoordinateKernel (by omega) parents children
          coordinate).childProbability =
      (tripleChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose 3 : ℝ) := by
  have h := worTripleExpectation_of_type hparents parents coordinate
    (tripleCoordinateKernel (by omega : 0 < parentCount) parents children
      coordinate).childProbability
    (fun bitType =>
      ((tripleTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
        ((tripleTypeGroup parents coordinate bitType).card : ℝ))
    (fun l m r => rfl)
  rw [h]
  calc
    (∑ bitType : TripleBitType,
      ((tripleTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose 3 : ℝ) *
          (((tripleTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
            ((tripleTypeGroup parents coordinate bitType).card : ℝ))) =
      ∑ bitType : TripleBitType,
        ((tripleTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
          (parentCount.choose 3 : ℝ) :=
      Finset.sum_congr rfl fun bitType _ =>
        group_prob_mul_ratio hparents parents children coordinate bitType
    _ = (tripleChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose 3 : ℝ) := by
      rw [← Finset.sum_div]
      congr 1
      exact_mod_cast sum_tripleTypeGroupChildOnes_card parents children coordinate

/-! ### Mismatch counts and the average disagreement -/

noncomputable def tripleMismatchCount
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (triple : TripleLayer parentCount 1) : ℕ := by
  classical
  exact (triple.val.filter
    (fun parent => parents parent coordinate ≠ children triple coordinate)).card

theorem tripleMismatchCount_eq
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (triple : TripleLayer parentCount 1) :
    tripleMismatchCount parents children coordinate triple =
      if children triple coordinate = true
        then 3 - (tripleCoordinateBitType parents coordinate triple).val
        else (tripleCoordinateBitType parents coordinate triple).val := by
  classical
  have hj : (tripleCoordinateBitType parents coordinate triple).val =
      (triple.val.filter (fun p => parents p coordinate = true)).card := rfl
  have hsplit :
      (triple.val.filter (fun p => parents p coordinate = true)).card +
        (triple.val.filter (fun p => ¬ (parents p coordinate = true))).card =
          triple.val.card :=
    Finset.card_filter_add_card_filter_not (s := triple.val)
      (fun p => parents p coordinate = true)
  rw [triple.property] at hsplit
  cases hc : children triple coordinate
  · have hfilter :
        triple.val.filter
          (fun parent => parents parent coordinate ≠ children triple coordinate) =
        triple.val.filter (fun p => parents p coordinate = true) := by
      apply Finset.filter_congr
      intro x _
      rw [hc]
      simp
    show (triple.val.filter
      (fun parent => parents parent coordinate ≠
        children triple coordinate)).card = _
    rw [hfilter]
    simp [hj]
  · have hfilter :
        triple.val.filter
          (fun parent => parents parent coordinate ≠ children triple coordinate) =
        triple.val.filter (fun p => ¬ (parents p coordinate = true)) := by
      apply Finset.filter_congr
      intro x _
      rw [hc]
    show (triple.val.filter
      (fun parent => parents parent coordinate ≠
        children triple coordinate)).card = _
    rw [hfilter]
    simp only [if_true]
    omega

theorem sum_tripleMismatchCount
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ triple : TripleLayer parentCount 1,
      (tripleMismatchCount parents children coordinate triple : ℝ)) =
      ∑ bitType : TripleBitType,
        ((bitType.val : ℝ) *
            (((tripleTypeGroup parents coordinate bitType).card : ℝ) -
              ((tripleTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ)) +
          (3 - (bitType.val : ℝ)) *
            ((tripleTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ)) := by
  classical
  have hmaps :
      (((Finset.univ : Finset (TripleLayer parentCount 1)) :
        Set (TripleLayer parentCount 1))).MapsTo
          (tripleCoordinateBitType parents coordinate)
          (Finset.univ : Finset TripleBitType) := fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun triple => (tripleMismatchCount parents children coordinate triple : ℝ))]
  refine Finset.sum_congr rfl fun bitType _ => ?_
  have hgroup :
      (Finset.univ.filter
        (fun triple : TripleLayer parentCount 1 =>
          tripleCoordinateBitType parents coordinate triple = bitType)) =
        tripleTypeGroup parents coordinate bitType := by
    simp [tripleTypeGroup]
  rw [hgroup]
  have honesle :=
    tripleTypeGroupChildOnes_card_le parents children coordinate bitType
  have hj3 : bitType.val ≤ 3 := by omega
  have hc3 : ((3 - bitType.val : ℕ) : ℝ) = 3 - (bitType.val : ℝ) := by
    rw [Nat.cast_sub hj3]; norm_num
  have hones :
      (tripleTypeGroup parents coordinate bitType).filter
        (fun triple => children triple coordinate = true) =
      tripleTypeGroupChildOnes parents children coordinate bitType := by
    simp [tripleTypeGroupChildOnes]
  have hcard :
      ((tripleTypeGroup parents coordinate bitType).filter
        (fun triple => ¬ (children triple coordinate = true))).card =
        (tripleTypeGroup parents coordinate bitType).card -
          (tripleTypeGroupChildOnes parents children coordinate bitType).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := tripleTypeGroup parents coordinate bitType)
      (fun triple => children triple coordinate = true)
    rw [hones] at hsplit
    omega
  have hconst1 : ∀ triple ∈
      tripleTypeGroupChildOnes parents children coordinate bitType,
      (tripleMismatchCount parents children coordinate triple : ℝ) =
        3 - (bitType.val : ℝ) := by
    intro triple htriple
    have hmem : triple ∈ (tripleTypeGroup parents coordinate bitType).filter
        (fun t => children t coordinate = true) := by rw [hones]; exact htriple
    obtain ⟨hgrp, hchild⟩ := Finset.mem_filter.mp hmem
    have htype : tripleCoordinateBitType parents coordinate triple = bitType :=
      (Finset.mem_filter.mp hgrp).2
    rw [tripleMismatchCount_eq, hchild, htype]
    simp only [if_true]
    exact hc3
  have hconst2 : ∀ triple ∈
      (tripleTypeGroup parents coordinate bitType).filter
        (fun triple => ¬ (children triple coordinate = true)),
      (tripleMismatchCount parents children coordinate triple : ℝ) =
        (bitType.val : ℝ) := by
    intro triple htriple
    obtain ⟨hgrp, hchild⟩ := Finset.mem_filter.mp htriple
    have htype : tripleCoordinateBitType parents coordinate triple = bitType :=
      (Finset.mem_filter.mp hgrp).2
    have hfalse : children triple coordinate = false := by
      cases hcv : children triple coordinate
      · rfl
      · exact absurd hcv hchild
    rw [tripleMismatchCount_eq, hfalse, htype]
    simp
  rw [← Finset.sum_filter_add_sum_filter_not
    (tripleTypeGroup parents coordinate bitType)
    (fun triple => children triple coordinate = true)]
  rw [hones, Finset.sum_congr rfl hconst1, Finset.sum_congr rfl hconst2,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hcard,
    Nat.cast_sub honesle]
  ring


theorem tripleCoordinateKernel_worAverageDisagreement
    (hparents : 3 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    worTripleExpectation parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (fun l m r =>
          (BinaryPairKernel.bitDisagreementProbability l
              ((tripleCoordinateKernel (by omega : 0 < parentCount) parents
                children coordinate).childProbability l m r) +
            BinaryPairKernel.bitDisagreementProbability m
              ((tripleCoordinateKernel (by omega : 0 < parentCount) parents
                children coordinate).childProbability l m r) +
            BinaryPairKernel.bitDisagreementProbability r
              ((tripleCoordinateKernel (by omega : 0 < parentCount) parents
                children coordinate).childProbability l m r)) / 3) =
      (∑ triple : TripleLayer parentCount 1,
        (tripleMismatchCount parents children coordinate triple : ℝ)) /
        (3 * (parentCount.choose 3 : ℝ)) := by
  have hchoose : (0 : ℝ) < (parentCount.choose 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  have h := worTripleExpectation_of_type hparents parents coordinate
    (fun l m r =>
      (BinaryPairKernel.bitDisagreementProbability l
          ((tripleCoordinateKernel (by omega : 0 < parentCount) parents
            children coordinate).childProbability l m r) +
        BinaryPairKernel.bitDisagreementProbability m
          ((tripleCoordinateKernel (by omega : 0 < parentCount) parents
            children coordinate).childProbability l m r) +
        BinaryPairKernel.bitDisagreementProbability r
          ((tripleCoordinateKernel (by omega : 0 < parentCount) parents
            children coordinate).childProbability l m r)) / 3)
    (fun bitType =>
      ((bitType.val : ℝ) *
          (1 - ((tripleTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
            ((tripleTypeGroup parents coordinate bitType).card : ℝ)) +
        (3 - (bitType.val : ℝ)) *
          (((tripleTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
            ((tripleTypeGroup parents coordinate bitType).card : ℝ))) / 3)
    (by
      intro l m r
      cases l <;> cases m <;> cases r <;>
        simp only [tripleBitTypeOfOutcomes,
          BinaryPairKernel.bitDisagreementProbability,
          tripleCoordinateKernel_childProbability,
          if_true, if_false, Bool.false_eq_true] <;>
        norm_num <;> try ring)
  rw [h]
  have hterm : ∀ bitType : TripleBitType,
      ((tripleTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 3 : ℝ) *
        (((bitType.val : ℝ) *
            (1 - ((tripleTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
              ((tripleTypeGroup parents coordinate bitType).card : ℝ)) +
          (3 - (bitType.val : ℝ)) *
            (((tripleTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
              ((tripleTypeGroup parents coordinate bitType).card : ℝ))) / 3) =
        ((bitType.val : ℝ) *
            (((tripleTypeGroup parents coordinate bitType).card : ℝ) -
              ((tripleTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ)) +
          (3 - (bitType.val : ℝ)) *
            ((tripleTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ)) / (3 * (parentCount.choose 3 : ℝ)) := by
    intro bitType
    have hr := group_prob_mul_ratio hparents parents children coordinate bitType
    have hcpl := group_prob_mul_complement hparents parents children coordinate bitType
    calc ((tripleTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose 3 : ℝ) *
        (((bitType.val : ℝ) *
            (1 - ((tripleTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
              ((tripleTypeGroup parents coordinate bitType).card : ℝ)) +
          (3 - (bitType.val : ℝ)) *
            (((tripleTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
              ((tripleTypeGroup parents coordinate bitType).card : ℝ))) / 3) =
        ((bitType.val : ℝ) *
            (((tripleTypeGroup parents coordinate bitType).card : ℝ) /
              (parentCount.choose 3 : ℝ) *
              (1 - ((tripleTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
                ((tripleTypeGroup parents coordinate bitType).card : ℝ))) +
          (3 - (bitType.val : ℝ)) *
            (((tripleTypeGroup parents coordinate bitType).card : ℝ) /
              (parentCount.choose 3 : ℝ) *
              (((tripleTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ) /
                ((tripleTypeGroup parents coordinate bitType).card : ℝ)))) / 3 := by
          ring
      _ = ((bitType.val : ℝ) *
            ((((tripleTypeGroup parents coordinate bitType).card : ℝ) -
              ((tripleTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ)) /
              (parentCount.choose 3 : ℝ)) +
          (3 - (bitType.val : ℝ)) *
            (((tripleTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
              (parentCount.choose 3 : ℝ))) / 3 := by rw [hcpl, hr]
      _ = _ := by field_simp
  rw [Finset.sum_congr rfl (fun bitType _ => hterm bitType), ← Finset.sum_div,
    ← sum_tripleMismatchCount parents children coordinate]

theorem sum_tripleMismatchCount_eq_hammingDist
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension) :
    (∑ coordinate : Fin dimension,
      ∑ triple : TripleLayer parentCount 1,
        tripleMismatchCount parents children coordinate triple) =
      ∑ triple : TripleLayer parentCount 1,
        ∑ parent ∈ triple.val,
          hammingDist (parents parent) (children triple) := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun triple _ => ?_
  have hcount (coordinate : Fin dimension) :
      tripleMismatchCount parents children coordinate triple =
        ∑ parent ∈ triple.val,
          if parents parent coordinate ≠ children triple coordinate
            then 1 else 0 := by
    change (triple.val.filter
      (fun parent =>
        parents parent coordinate ≠ children triple coordinate)).card = _
    exact (Finset.sum_boole _ _).symm
  simp_rw [hcount]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun parent _ => ?_
  change (∑ coordinate : Fin dimension,
      if parents parent coordinate ≠ children triple coordinate
        then 1 else 0) =
    ((Finset.univ : Finset (Fin dimension)).filter
      (fun coordinate =>
        parents parent coordinate ≠ children triple coordinate)).card
  exact Finset.sum_boole _ _

/-! ## Part 5: the per-coordinate ledger bound -/

theorem tripleChildCoordinateOneCount_le
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    tripleChildCoordinateOneCount children coordinate ≤ parentCount.choose 3 := by
  classical
  unfold tripleChildCoordinateOneCount booleanWordOnes
  calc (Finset.univ.filter
      (fun triple : TripleLayer parentCount 1 =>
        children triple coordinate = true)).card ≤
        (Finset.univ : Finset (TripleLayer parentCount 1)).card :=
      Finset.card_filter_le _ _
    _ = parentCount.choose 3 := by
      rw [Finset.card_univ, tripleLayer_one_card]

theorem tripleCoordinateConditionalEntropy_empirical_bound
    (hparents : 10 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    tripleCoordinateConditionalEntropy parents children coordinate ≤
      17 / 80 + (7 / 4) *
          ((∑ triple : TripleLayer parentCount 1,
            (tripleMismatchCount parents children coordinate triple : ℝ)) /
            (3 * (parentCount.choose 3 : ℝ))) +
        (binaryEntropy
            ((tripleChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose 3 : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2 +
      worCorrection parentCount := by
  classical
  have h3 : 3 ≤ parentCount := by omega
  have hpos : 0 < parentCount := by omega
  have hNreal : (10 : ℝ) ≤ (parentCount : ℝ) := by exact_mod_cast hparents
  have hchoose : (0 : ℝ) < (parentCount.choose 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos h3
  set kernel := tripleCoordinateKernel hpos parents children coordinate
    with hkernel
  set childMean : ℝ :=
    (tripleChildCoordinateOneCount children coordinate : ℝ) /
      (parentCount.choose 3 : ℝ) with hchildMeandef
  -- the entropy observable
  have hEeq := tripleCoordinateKernel_worConditionalEntropy h3 parents children
    coordinate
  have hEerr := worTripleExpectation_error hparents parents coordinate
    (fun l m r => binaryEntropy (kernel.childProbability l m r))
    (fun l m r => binaryEntropy_nonneg (kernel.childProbability_nonneg l m r)
      (kernel.childProbability_le_one l m r))
    (fun l m r => binaryEntropy_le_one _)
  have hEiid : iidTripleExpectation
      ((pairParentCoordinateOneCount parents coordinate : ℝ) / (parentCount : ℝ))
      (fun l m r => binaryEntropy (kernel.childProbability l m r)) =
      kernel.conditionalEntropy := rfl
  rw [hEiid, hEeq] at hEerr
  -- the marginal observable
  have hMeq := tripleCoordinateKernel_worChildMarginal h3 parents children coordinate
  have hMerr := worTripleExpectation_error hparents parents coordinate
    kernel.childProbability kernel.childProbability_nonneg
    kernel.childProbability_le_one
  have hMiid : iidTripleExpectation
      ((pairParentCoordinateOneCount parents coordinate : ℝ) / (parentCount : ℝ))
      kernel.childProbability = kernel.childMarginal := rfl
  rw [hMiid, hMeq] at hMerr
  -- the disagreement observable
  have hDeq := tripleCoordinateKernel_worAverageDisagreement h3 parents children
    coordinate
  have hDobs : ∀ l m r : Bool,
      0 ≤ (BinaryPairKernel.bitDisagreementProbability l
            (kernel.childProbability l m r) +
          BinaryPairKernel.bitDisagreementProbability m
            (kernel.childProbability l m r) +
          BinaryPairKernel.bitDisagreementProbability r
            (kernel.childProbability l m r)) / 3 ∧
        (BinaryPairKernel.bitDisagreementProbability l
            (kernel.childProbability l m r) +
          BinaryPairKernel.bitDisagreementProbability m
            (kernel.childProbability l m r) +
          BinaryPairKernel.bitDisagreementProbability r
            (kernel.childProbability l m r)) / 3 ≤ 1 := by
    intro l m r
    have h0 := kernel.childProbability_nonneg l m r
    have h1 := kernel.childProbability_le_one l m r
    unfold BinaryPairKernel.bitDisagreementProbability
    cases l <;> cases m <;> cases r <;> constructor <;> simp <;> linarith
  have hDerr := worTripleExpectation_error hparents parents coordinate
    (fun l m r =>
      (BinaryPairKernel.bitDisagreementProbability l
          (kernel.childProbability l m r) +
        BinaryPairKernel.bitDisagreementProbability m
          (kernel.childProbability l m r) +
        BinaryPairKernel.bitDisagreementProbability r
          (kernel.childProbability l m r)) / 3)
    (fun l m r => (hDobs l m r).1) (fun l m r => (hDobs l m r).2)
  have hDiid : iidTripleExpectation
      ((pairParentCoordinateOneCount parents coordinate : ℝ) / (parentCount : ℝ))
      (fun l m r =>
        (BinaryPairKernel.bitDisagreementProbability l
            (kernel.childProbability l m r) +
          BinaryPairKernel.bitDisagreementProbability m
            (kernel.childProbability l m r) +
          BinaryPairKernel.bitDisagreementProbability r
            (kernel.childProbability l m r)) / 3) =
      kernel.averageDisagreement := rfl
  rw [hDiid, hDeq] at hDerr
  -- bounds for the ledger
  have hchildMean0 : 0 ≤ childMean := by rw [hchildMeandef]; positivity
  have hchildMean1 : childMean ≤ 1 := by
    rw [hchildMeandef]
    exact (div_le_one hchoose).mpr
      (by exact_mod_cast tripleChildCoordinateOneCount_le children coordinate)
  have hfourL : 4 / (parentCount : ℝ) ≤ 1 / 2 := by
    rw [div_le_div_iff₀ (by linarith) (by norm_num)]
    linarith
  have hfourpos : (0 : ℝ) < 4 / (parentCount : ℝ) := by positivity
  have habs : |childMean - kernel.childMarginal| ≤ 4 / (parentCount : ℝ) := hMerr
  have hcont : binaryEntropy |childMean - kernel.childMarginal| ≤
      binaryEntropy (4 / (parentCount : ℝ)) :=
    binaryEntropy_mono_on_half _ _ (abs_nonneg _) habs (by linarith)
  have hledger := ledger_inequality parentCount hparents kernel
    (tripleCoordinateConditionalEntropy parents children coordinate)
    ((∑ triple : TripleLayer parentCount 1,
      (tripleMismatchCount parents children coordinate triple : ℝ)) /
      (3 * (parentCount.choose 3 : ℝ)))
    childMean hchildMean0 hchildMean1
    (by linarith [(abs_le.mp hEerr).2])
    (by linarith [(abs_le.mp hDerr).1])
    (habs.trans hfourL) hcont
  have hparentProb : kernel.parentProbability =
      (pairParentCoordinateOneCount parents coordinate : ℝ) /
        (parentCount : ℝ) := rfl
  rw [hparentProb] at hledger
  exact hledger

/-! ## Part 6: array-level potentials, disagreement and the ledger -/

noncomputable def tripleParentArrayEntropyPotential
    (parents : Fin parentCount → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      ((pairParentCoordinateOneCount parents coordinate : ℝ) /
        (parentCount : ℝ))) / (dimension : ℝ)

noncomputable def tripleChildArrayEntropyPotential
    (children : TripleLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      ((tripleChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose 3 : ℝ))) / (dimension : ℝ)

noncomputable def tripleChildArrayAverageDisagreement
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    (∑ triple : TripleLayer parentCount 1,
      (tripleMismatchCount parents children coordinate triple : ℝ)) /
      (3 * (parentCount.choose 3 : ℝ))) / (dimension : ℝ)

theorem tripleChildArrayEntropy_empirical_bound
    (hparents : 10 ≤ parentCount) (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension) :
    tripleChildArrayEntropy parents children ≤
      17 / 80 + (7 / 4) *
          tripleChildArrayAverageDisagreement parents children +
        (tripleChildArrayEntropyPotential children -
          tripleParentArrayEntropyPotential parents) / 2 +
      worCorrection parentCount := by
  have hdim : (0 : ℝ) < (dimension : ℝ) := by exact_mod_cast hdimension
  set E : Fin dimension → ℝ :=
    fun coordinate =>
      tripleCoordinateConditionalEntropy parents children coordinate with hE
  set D : Fin dimension → ℝ :=
    fun coordinate =>
      (∑ triple : TripleLayer parentCount 1,
        (tripleMismatchCount parents children coordinate triple : ℝ)) /
        (3 * (parentCount.choose 3 : ℝ)) with hD
  set Hc : Fin dimension → ℝ :=
    fun coordinate =>
      binaryEntropy
        ((tripleChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose 3 : ℝ)) with hHc
  set Hp : Fin dimension → ℝ :=
    fun coordinate =>
      binaryEntropy
        ((pairParentCoordinateOneCount parents coordinate : ℝ) /
          (parentCount : ℝ)) with hHp
  have hpointwise : ∀ coordinate : Fin dimension,
      E coordinate ≤ 17 / 80 + (7 / 4) * D coordinate +
        (Hc coordinate - Hp coordinate) / 2 + worCorrection parentCount :=
    fun coordinate =>
      tripleCoordinateConditionalEntropy_empirical_bound hparents parents
        children coordinate
  have hsum : (∑ coordinate : Fin dimension, E coordinate) ≤
      ∑ coordinate : Fin dimension,
        (17 / 80 + (7 / 4) * D coordinate +
          (Hc coordinate - Hp coordinate) / 2 + worCorrection parentCount) :=
    Finset.sum_le_sum fun coordinate _ => hpointwise coordinate
  have hexpand :
      (∑ coordinate : Fin dimension,
        (17 / 80 + (7 / 4) * D coordinate +
          (Hc coordinate - Hp coordinate) / 2 + worCorrection parentCount)) =
        (dimension : ℝ) * (17 / 80) + (7 / 4) *
          (∑ coordinate : Fin dimension, D coordinate) +
          ((∑ coordinate : Fin dimension, Hc coordinate) -
            (∑ coordinate : Fin dimension, Hp coordinate)) / 2 +
          (dimension : ℝ) * worCorrection parentCount := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
    ring
  rw [hexpand] at hsum
  show (∑ coordinate : Fin dimension, E coordinate) / (dimension : ℝ) ≤ _
  unfold tripleChildArrayAverageDisagreement tripleChildArrayEntropyPotential
    tripleParentArrayEntropyPotential
  rw [div_le_iff₀ hdim]
  have hrhs :
      (17 / 80 + (7 / 4) *
          ((∑ coordinate : Fin dimension, D coordinate) / (dimension : ℝ)) +
        (((∑ coordinate : Fin dimension, Hc coordinate) / (dimension : ℝ)) -
          ((∑ coordinate : Fin dimension, Hp coordinate) / (dimension : ℝ))) / 2 +
        worCorrection parentCount) * (dimension : ℝ) =
      (dimension : ℝ) * (17 / 80) + (7 / 4) *
        (∑ coordinate : Fin dimension, D coordinate) +
        ((∑ coordinate : Fin dimension, Hc coordinate) -
          (∑ coordinate : Fin dimension, Hp coordinate)) / 2 +
        (dimension : ℝ) * worCorrection parentCount := by
    field_simp
  rw [hrhs]
  exact hsum

theorem tripleChildArrayAverageDisagreement_le_radius
    (hparents : 3 ≤ parentCount) (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (children : TripleLayer parentCount 1 → HammingWord dimension)
    (radius : ℕ)
    (hedges : ∀ (triple : TripleLayer parentCount 1)
      (parent : TripleLayer parentCount 0),
        parent ∈ triple.val →
          hammingDist (parents parent) (children triple) ≤ radius) :
    tripleChildArrayAverageDisagreement parents children ≤
      (radius : ℝ) / (dimension : ℝ) := by
  classical
  have hchoose : (0 : ℝ) < (parentCount.choose 3 : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  have hdim : (0 : ℝ) < (dimension : ℝ) := by exact_mod_cast hdimension
  have htotal :
      (∑ coordinate : Fin dimension,
        ∑ triple : TripleLayer parentCount 1,
          tripleMismatchCount parents children coordinate triple) ≤
        3 * parentCount.choose 3 * radius := by
    calc (∑ coordinate : Fin dimension,
        ∑ triple : TripleLayer parentCount 1,
          tripleMismatchCount parents children coordinate triple) =
        ∑ triple : TripleLayer parentCount 1,
          ∑ parent ∈ triple.val,
            hammingDist (parents parent) (children triple) :=
        sum_tripleMismatchCount_eq_hammingDist parents children
      _ ≤ ∑ triple : TripleLayer parentCount 1,
            ∑ _parent ∈ triple.val, radius := by
        refine Finset.sum_le_sum fun triple _ => ?_
        exact Finset.sum_le_sum fun parent hparent => hedges triple parent hparent
      _ = ∑ _triple : TripleLayer parentCount 1, 3 * radius := by
        refine Finset.sum_congr rfl fun triple _ => ?_
        simp [triple.property]
      _ = 3 * parentCount.choose 3 * radius := by
        simp [tripleLayer_one_card, Nat.mul_assoc, Nat.mul_comm]
  have htotal_real :
      (∑ coordinate : Fin dimension,
        ((∑ triple : TripleLayer parentCount 1,
          tripleMismatchCount parents children coordinate triple : ℕ) : ℝ)) ≤
        3 * (parentCount.choose 3 : ℝ) * (radius : ℝ) := by
    exact_mod_cast htotal
  have hcast : ∀ coordinate : Fin dimension,
      (∑ triple : TripleLayer parentCount 1,
        (tripleMismatchCount parents children coordinate triple : ℝ)) =
      ((∑ triple : TripleLayer parentCount 1,
        tripleMismatchCount parents children coordinate triple : ℕ) : ℝ) := by
    intro coordinate; push_cast; rfl
  unfold tripleChildArrayAverageDisagreement
  simp_rw [hcast]
  rw [← Finset.sum_div]
  apply (div_le_div_iff_of_pos_right hdim).mpr
  apply (div_le_iff₀ (by positivity : (0:ℝ) < 3 * (parentCount.choose 3 : ℝ))).mpr
  nlinarith

end ThreeBridge
