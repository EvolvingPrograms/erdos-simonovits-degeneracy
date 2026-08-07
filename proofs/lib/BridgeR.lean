import ProfilesR
import KernelR

/-!
# `BridgeR.lean` — the `r`-generic empirical-array → kernel bridge

Generalizes `Bridge3.lean` from `r = 3` to arbitrary `r`.  The `2^r` outcome
enumeration of the `r = 3` file (`Bool → Bool → Bool`, `Fin.sum_univ_four`,
`cases l <;> cases m <;> cases r`) is replaced throughout by the popcount-fibre
machinery of `KernelR` (`popcountFibre`, `sum_fibrewise`,
`sum_choose_descFactorial`).  **No proof in this file case-splits on a bit.**

Contents:

* §0 the Vandermonde splitting lemma (arity-free, restated from `Bridge3` so
  that this file need not import it);
* §1 the type-group cardinality `|G_j| = C(k,j)·C(L−k,r−j)`;
* §2 balancedness of the `r`-subset design (`Kernel3` 484–579, generalized:
  each index lies in `C(L−1,r−1)` of the `r`-subsets);
* §3 the without-replacement mass in terms of the type groups, with weight
  `j!(r−j)!/r!`;
* §4 the without-replacement / i.i.d. expectations and their coupling error;
* §5 the coordinate kernel, its three empirical functionals, mismatch counts
  and the per-coordinate ledger bound;
* §6 array-level potentials and the array ledger bound;
* §7 the exclusion ledger: the generic potential induction with the
  `depth · increment > 1` hypothesis.

See `research/results_Z_lean_bridgeR.md`.
-/

namespace RGenericBridge

open Finset TwoDegenerateGraphs RGenericProfiles RGenericKernel
open scoped BigOperators

/-! ## §0 A Vandermonde-style splitting lemma

The number of `n`-subsets of `s` containing exactly `j` points satisfying a
predicate `p` is `C(|s ∩ p|, j) · C(|s ∖ p|, n − j)`.

Arity-free — identical to `ThreeBridge.card_powersetCard_filter_pred`, restated
here so `BridgeR` does not have to import the `r = 3` tree.  **The `j ≤ n`
hypothesis is essential** (without it the `n − j` truncation makes the
right-hand side wrong). -/
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
      Finset.card_filter_add_card_filter_not (s := u) (p := p)
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

/-! ## §1 The type-group cardinality (Vandermonde)

Write `k` for the number of parents carrying a `1` at the coordinate.  The
group of `r`-subsets of type `j` has `C(k, j) · C(L − k, r − j)` members.
This single lemma replaces `Bridge3.group_card_{zero,one,two,three}` and the
`cast_choose_two` / `cast_choose_three` polynomial expansions. -/

variable {parentCount dimension r : ℕ}

/-- The bit type of an *ordered* parent word: its popcount. Replaces
`Bridge3.tripleBitTypeOfOutcomes`. -/
def rBitTypeOfWord (x : Fin r → Bool) : RBitType r :=
  ⟨popcount x, popcount_lt_succ x⟩

@[simp] theorem rBitTypeOfWord_val (x : Fin r → Bool) :
    (rBitTypeOfWord x).val = popcount x := rfl

theorem bitType_le (bitType : RBitType r) : bitType.val ≤ r :=
  Nat.lt_succ_iff.mp bitType.isLt

theorem rTypeGroup_card
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) (bitType : RBitType r) :
    (rTypeGroup parents coordinate bitType).card =
      (pairParentCoordinateOneCount parents coordinate).choose bitType.val *
        (parentCount - pairParentCoordinateOneCount parents coordinate).choose
          (r - bitType.val) := by
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
    (fun parent => parents parent coordinate = true) r bitType.val
    (bitType_le bitType)
  rw [honescard, hzerocard] at hsplit
  rw [← hsplit]
  refine Finset.card_bij (fun T _ => (T.val : Finset (Fin parentCount))) ?_ ?_ ?_
  · intro T hT
    have htype : rCoordinateBitType parents coordinate T = bitType :=
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
    simp only [rTypeGroup, Finset.mem_filter, Finset.mem_univ, true_and]
    exact Fin.ext hu.2

/-! ## §2 Balancedness of the `r`-subset design

Each element of `Fin L` lies in exactly `C(L−1, r−1)` of the `r`-element
subsets, so the parent index seen at a uniformly chosen (child, slot) pair is
*uniform* on `Fin L`.  Generalization of `Kernel3` lines 484–579
(`card_threeSubsets_containing`, `sum_threeSubsets_slots`,
`card_slots_identity`, `threeSubset_slot_marginal`). -/

/-- **The balancedness fact.**  A fixed index lies in exactly `C(L−1, r−1)` of
the `r`-element subsets of `Fin L`. -/
theorem card_rSubsets_containing {L r : ℕ} (hr : 1 ≤ r) (a : Fin L) :
    (((univ : Finset (Fin L)).powersetCard r).filter (fun S => a ∈ S)).card
      = (L - 1).choose (r - 1) := by
  classical
  have hcard : ((univ : Finset (Fin L)).erase a).card = L - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
      Fintype.card_fin]
  have hbij :
      (((univ : Finset (Fin L)).powersetCard r).filter (fun S => a ∈ S)).card
        = (((univ : Finset (Fin L)).erase a).powersetCard (r - 1)).card := by
    refine Finset.card_bij' (fun S _ => S.erase a) (fun T _ => insert a T)
      ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS
      obtain ⟨⟨-, hSr⟩, ha⟩ := hS
      refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
      · intro y hy
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1, Finset.mem_univ y⟩
      · rw [Finset.card_erase_of_mem ha, hSr]
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      obtain ⟨hTsub, hTr⟩ := hT
      have haT : a ∉ T := fun h => (Finset.mem_erase.mp (hTsub h)).1 rfl
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      refine ⟨⟨Finset.subset_univ _, ?_⟩, Finset.mem_insert_self a T⟩
      rw [Finset.card_insert_of_notMem haT, hTr]
      omega
    · intro S hS
      simp only [Finset.mem_filter] at hS
      exact Finset.insert_erase hS.2
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      have haT : a ∉ T := fun h => (Finset.mem_erase.mp (hT.1 h)).1 rfl
      exact Finset.erase_insert haT
  rw [hbij, Finset.card_powersetCard, hcard]

/-- Double counting over the `r`-subset design: summing any weight over all
(child, slot) pairs is `C(L−1, r−1)` times summing it over the parent layer. -/
theorem sum_rSubsets_slots {L r : ℕ} (hr : 1 ≤ r) (f : Fin L → ℝ) :
    ∑ S ∈ (univ : Finset (Fin L)).powersetCard r, ∑ a ∈ S, f a
      = ((L - 1).choose (r - 1) : ℝ) * ∑ a : Fin L, f a := by
  classical
  have hswap :
      ∑ S ∈ (univ : Finset (Fin L)).powersetCard r, ∑ a ∈ S, f a
        = ∑ a : Fin L,
            ∑ S ∈ (univ : Finset (Fin L)).powersetCard r,
              (if a ∈ S then f a else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hswap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const,
    card_rSubsets_containing hr a, nsmul_eq_mul]

/-- `L · C(L−1, r−1) = r · C(L, r)`: the design has `C(L,r)` children, each
with `r` slots, and the induced index distribution is uniform on `Fin L`. -/
theorem card_slots_identity {L r : ℕ} (hL : 1 ≤ L) (hr : 1 ≤ r) :
    L * (L - 1).choose (r - 1) = r * L.choose r := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq n k)

/-- The multiplicity weight `j!(r−j)!/r!`. -/
noncomputable def rOutcomeWeight (r j : ℕ) : ℝ :=
  ((Nat.factorial j * Nat.factorial (r - j) : ℕ) : ℝ) / ((Nat.factorial r : ℕ) : ℝ)

/-- `C(r,j) · j!(r−j)!/r! = 1` for `j ≤ r`. -/
theorem choose_mul_rOutcomeWeight {r j : ℕ} (hj : j ≤ r) :
    (r.choose j : ℝ) * rOutcomeWeight r j = 1 := by
  have hfac : (0 : ℝ) < ((Nat.factorial r : ℕ) : ℝ) := by
    exact_mod_cast r.factorial_pos
  have hnat : r.choose j * (Nat.factorial j * Nat.factorial (r - j)) = Nat.factorial r := by
    rw [← Nat.mul_assoc]
    exact Nat.choose_mul_factorial_mul_factorial hj
  have := congrArg (Nat.cast : ℕ → ℝ) hnat
  push_cast at this ⊢
  unfold rOutcomeWeight
  push_cast
  field_simp
  linarith [this]

/-- The pure `Nat` identity behind `worMass_eq_rTypeGroup`. -/
theorem worMass_nat_identity (r j k L : ℕ) :
    (k.descFactorial j * (L - k).descFactorial (r - j)) * (L.choose r * Nat.factorial r) =
      (k.choose j * (L - k).choose (r - j)) * (Nat.factorial j * Nat.factorial (r - j)) *
        L.descFactorial r := by
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose]
  ring

theorem worMass_eq_rTypeGroup
    (hparents : r ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension) (x : Fin r → Bool) :
    withoutReplacementBinaryRMass r parentCount
        (pairParentCoordinateOneCount parents coordinate) x =
      ((rTypeGroup parents coordinate (rBitTypeOfWord x)).card : ℝ) /
        (parentCount.choose r : ℝ) * rOutcomeWeight r (popcount x) := by
  classical
  set k := pairParentCoordinateOneCount parents coordinate with hk
  set j := popcount x with hj
  have hchoose : (0 : ℝ) < (parentCount.choose r : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  have hdesc : (0 : ℝ) < ((parentCount.descFactorial r : ℕ) : ℝ) :=
    descFactorial_pos_cast hparents
  have hfac : (0 : ℝ) < ((Nat.factorial r : ℕ) : ℝ) := by exact_mod_cast r.factorial_pos
  have hgroup := rTypeGroup_card (r := r) parents coordinate (rBitTypeOfWord x)
  rw [withoutReplacementBinaryRMass, hgroup]
  have hnat := congrArg (Nat.cast (R := ℝ))
    (worMass_nat_identity r j k parentCount)
  push_cast at hnat
  unfold rOutcomeWeight
  simp only [rBitTypeOfWord_val, ← hj, ← hk]
  push_cast
  field_simp
  linarith [hnat]

/-! ## §4 Expectations under the without-replacement and i.i.d. laws -/

noncomputable def worRExpectation (r parentCount oneCount : ℕ)
    (f : (Fin r → Bool) → ℝ) : ℝ :=
  ∑ x : Fin r → Bool,
    withoutReplacementBinaryRMass r parentCount oneCount x * f x

noncomputable def iidRExpectation (r : ℕ) (q : ℝ)
    (f : (Fin r → Bool) → ℝ) : ℝ :=
  ∑ x : Fin r → Bool, independentBinaryRMass q x * f x

/-- The coupling error between the without-replacement and the i.i.d. law, on
any `[0,1]`-valued observable.  The `r = 3` constant `4/L` (`L ≥ 10`) becomes
`r²/L` at threshold `L ≥ r²` — see `results_X_lean_kernelR.md` §3. -/
theorem worRExpectation_error
    (hr : 1 ≤ r) (hL : r ^ 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (f : (Fin r → Bool) → ℝ)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∀ x, f x ≤ 1) :
    |worRExpectation r parentCount
        (pairParentCoordinateOneCount parents coordinate) f -
      iidRExpectation r
        ((pairParentCoordinateOneCount parents coordinate : ℝ) /
          (parentCount : ℝ)) f| ≤ (r : ℝ) ^ 2 / (parentCount : ℝ) :=
  withoutReplacement_expectation_error hr hL
    (pairParentCoordinateOneCount_le parents coordinate) f hf0 hf1

/-- The popcount fibre, viewed through `rBitTypeOfWord`. -/
theorem filter_rBitTypeOfWord (bitType : RBitType r) :
    (univ.filter fun x : Fin r → Bool => rBitTypeOfWord x = bitType) =
      popcountFibre r bitType.val := by
  ext x
  simp [popcountFibre, rBitTypeOfWord, Fin.ext_iff]

/-- **The fibrewise regrouping over bit types.**  Replaces
`Fin.sum_univ_four` + the eight-branch `cases` of `Bridge3`. -/
theorem sum_over_bitTypes (F : (Fin r → Bool) → ℝ) (G : RBitType r → ℝ)
    (hF : ∀ x, F x = G (rBitTypeOfWord x)) :
    (∑ x : Fin r → Bool, F x) =
      ∑ bitType : RBitType r, (r.choose bitType.val : ℝ) * G bitType := by
  classical
  have hmaps : ∀ x ∈ (univ : Finset (Fin r → Bool)),
      rBitTypeOfWord x ∈ (univ : Finset (RBitType r)) := fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps F]
  refine Finset.sum_congr rfl fun bitType _ => ?_
  rw [filter_rBitTypeOfWord]
  have hconst : ∀ x ∈ popcountFibre r bitType.val, F x = G bitType := by
    intro x hx
    rw [hF x]
    congr 1
    exact Fin.ext (mem_popcountFibre.mp hx)
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, popcountFibre_card,
    nsmul_eq_mul]

/-- Any observable depending only on the *type* of the word has
without-replacement expectation the type-weighted average.  This is the
`r`-generic `Bridge3.worTripleExpectation_of_type`. -/
theorem worRExpectation_of_type
    (hparents : r ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (coordinate : Fin dimension)
    (f : (Fin r → Bool) → ℝ) (g : RBitType r → ℝ)
    (hf : ∀ x, f x = g (rBitTypeOfWord x)) :
    worRExpectation r parentCount
        (pairParentCoordinateOneCount parents coordinate) f =
      ∑ bitType : RBitType r,
        ((rTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose r : ℝ) * g bitType := by
  classical
  have hstep := sum_over_bitTypes
    (F := fun x => withoutReplacementBinaryRMass r parentCount
      (pairParentCoordinateOneCount parents coordinate) x * f x)
    (G := fun bitType =>
      ((rTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose r : ℝ) * rOutcomeWeight r bitType.val * g bitType)
    (by
      intro x
      rw [worMass_eq_rTypeGroup hparents parents coordinate x, hf x]
      simp only [rBitTypeOfWord_val])
  rw [worRExpectation, hstep]
  refine Finset.sum_congr rfl fun bitType _ => ?_
  have hw := choose_mul_rOutcomeWeight (bitType_le bitType)
  calc (r.choose bitType.val : ℝ) *
        (((rTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose r : ℝ) * rOutcomeWeight r bitType.val * g bitType)
      = ((r.choose bitType.val : ℝ) * rOutcomeWeight r bitType.val) *
        (((rTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose r : ℝ) * g bitType) := by ring
    _ = _ := by rw [hw, one_mul]

/-! ## §5 The coordinate kernel -/

noncomputable def rChildCoordinateOneCount
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension) : ℕ :=
  (booleanWordOnes (fun sub => children sub coordinate)).card

theorem sum_rTypeGroupChildOnes_card
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ bitType : RBitType r,
      (rTypeGroupChildOnes parents children coordinate bitType).card) =
      rChildCoordinateOneCount children coordinate := by
  classical
  set support : Finset (RLayer parentCount r 1) :=
    booleanWordOnes (fun sub => children sub coordinate) with hsupport
  have hmaps :
      ((support : Finset (RLayer parentCount r 1)) :
        Set (RLayer parentCount r 1)).MapsTo
          (rCoordinateBitType parents coordinate)
          (Finset.univ : Finset (RBitType r)) := fun _ _ => Finset.mem_univ _
  have hpartition := Finset.card_eq_sum_card_fiberwise hmaps
  have hfiber (bitType : RBitType r) :
      support.filter
        (fun sub => rCoordinateBitType parents coordinate sub = bitType) =
      rTypeGroupChildOnes parents children coordinate bitType := by
    ext sub
    simp [hsupport, booleanWordOnes, rTypeGroupChildOnes, rTypeGroup, and_comm]
  calc
    (∑ bitType : RBitType r,
      (rTypeGroupChildOnes parents children coordinate bitType).card) =
        ∑ bitType : RBitType r,
          (support.filter
            (fun sub =>
              rCoordinateBitType parents coordinate sub = bitType)).card :=
        Finset.sum_congr rfl fun bitType _ => by rw [hfiber]
    _ = support.card := hpartition.symm
    _ = rChildCoordinateOneCount children coordinate := rfl

noncomputable def rCoordinateKernel
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension) : BinaryRKernel r where
  parentProbability :=
    (pairParentCoordinateOneCount parents coordinate : ℝ) / (parentCount : ℝ)
  parentProbability_nonneg := by positivity
  parentProbability_le_one := by
    have hpositive : (0 : ℝ) < (parentCount : ℝ) := by exact_mod_cast hparents
    exact (div_le_one hpositive).mpr
      (by exact_mod_cast pairParentCoordinateOneCount_le parents coordinate)
  childProbability x :=
    ((rTypeGroupChildOnes parents children coordinate
      (rBitTypeOfWord x)).card : ℝ) /
        ((rTypeGroup parents coordinate (rBitTypeOfWord x)).card : ℝ)
  childProbability_nonneg := by intro x; positivity
  childProbability_le_one := by
    intro x
    set bitType := rBitTypeOfWord x with hbit
    have hle := rTypeGroupChildOnes_card_le parents children coordinate bitType
    by_cases hzero : (rTypeGroup parents coordinate bitType).card = 0
    · rw [hzero]; simp
    · have hpositive :
          (0 : ℝ) < ((rTypeGroup parents coordinate bitType).card : ℝ) := by
        exact_mod_cast Nat.pos_of_ne_zero hzero
      exact (div_le_one hpositive).mpr (by exact_mod_cast hle)

theorem rCoordinateKernel_childProbability
    (hparents : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension) (x : Fin r → Bool) :
    (rCoordinateKernel hparents parents children coordinate).childProbability x =
      ((rTypeGroupChildOnes parents children coordinate
        (rBitTypeOfWord x)).card : ℝ) /
          ((rTypeGroup parents coordinate (rBitTypeOfWord x)).card : ℝ) := rfl

theorem group_prob_mul_ratio
    (hparents : r ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension) (bitType : RBitType r) :
    ((rTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose r : ℝ) *
      (((rTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
        ((rTypeGroup parents coordinate bitType).card : ℝ)) =
      ((rTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
        (parentCount.choose r : ℝ) := by
  have hchoose : (0 : ℝ) < (parentCount.choose r : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  by_cases hgroup : (rTypeGroup parents coordinate bitType).card = 0
  · have hchild : (rTypeGroupChildOnes parents children
        coordinate bitType).card = 0 := by
      have hle := rTypeGroupChildOnes_card_le parents children coordinate bitType
      omega
    simp [hgroup, hchild]
  · have hgroup_real :
        ((rTypeGroup parents coordinate bitType).card : ℝ) ≠ 0 := by
      exact_mod_cast hgroup
    field_simp

theorem group_prob_mul_complement
    (hparents : r ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension) (bitType : RBitType r) :
    ((rTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose r : ℝ) *
      (1 - ((rTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
        ((rTypeGroup parents coordinate bitType).card : ℝ)) =
      (((rTypeGroup parents coordinate bitType).card : ℝ) -
        ((rTypeGroupChildOnes parents children coordinate bitType).card : ℝ)) /
        (parentCount.choose r : ℝ) := by
  have h := group_prob_mul_ratio hparents parents children coordinate bitType
  have hexp : ((rTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose r : ℝ) *
      (1 - ((rTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
        ((rTypeGroup parents coordinate bitType).card : ℝ)) =
      ((rTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose r : ℝ) -
        (((rTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose r : ℝ) *
          (((rTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
            ((rTypeGroup parents coordinate bitType).card : ℝ))) := by ring
  rw [hexp, h]
  ring

theorem rCoordinateKernel_worConditionalEntropy
    (hparents : r ≤ parentCount) (hpos : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    worRExpectation r parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (fun x => binaryEntropy
          ((rCoordinateKernel hpos parents children
            coordinate).childProbability x)) =
      rCoordinateConditionalEntropy parents children coordinate := by
  have h := worRExpectation_of_type hparents parents coordinate
    (fun x => binaryEntropy
      ((rCoordinateKernel hpos parents children coordinate).childProbability x))
    (fun bitType => binaryEntropy
      (((rTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
        ((rTypeGroup parents coordinate bitType).card : ℝ)))
    (fun x => rfl)
  rw [h]
  rfl

theorem rCoordinateKernel_worChildMarginal
    (hparents : r ≤ parentCount) (hpos : 0 < parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    worRExpectation r parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (rCoordinateKernel hpos parents children coordinate).childProbability =
      (rChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose r : ℝ) := by
  have h := worRExpectation_of_type hparents parents coordinate
    (rCoordinateKernel hpos parents children coordinate).childProbability
    (fun bitType =>
      ((rTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
        ((rTypeGroup parents coordinate bitType).card : ℝ))
    (fun x => rfl)
  rw [h]
  calc
    (∑ bitType : RBitType r,
      ((rTypeGroup parents coordinate bitType).card : ℝ) /
        (parentCount.choose r : ℝ) *
          (((rTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
            ((rTypeGroup parents coordinate bitType).card : ℝ))) =
      ∑ bitType : RBitType r,
        ((rTypeGroupChildOnes parents children coordinate bitType).card : ℝ) /
          (parentCount.choose r : ℝ) :=
      Finset.sum_congr rfl fun bitType _ =>
        group_prob_mul_ratio hparents parents children coordinate bitType
    _ = (rChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose r : ℝ) := by
      rw [← Finset.sum_div]
      congr 1
      exact_mod_cast sum_rTypeGroupChildOnes_card parents children coordinate

/-! ### Mismatch counts and the average disagreement -/

noncomputable def rMismatchCount
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (sub : RLayer parentCount r 1) : ℕ := by
  classical
  exact (sub.val.filter
    (fun parent => parents parent coordinate ≠ children sub coordinate)).card

theorem rMismatchCount_eq
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension)
    (sub : RLayer parentCount r 1) :
    rMismatchCount parents children coordinate sub =
      if children sub coordinate = true
        then r - (rCoordinateBitType parents coordinate sub).val
        else (rCoordinateBitType parents coordinate sub).val := by
  classical
  have hj : (rCoordinateBitType parents coordinate sub).val =
      (sub.val.filter (fun p => parents p coordinate = true)).card := rfl
  have hsplit :
      (sub.val.filter (fun p => parents p coordinate = true)).card +
        (sub.val.filter (fun p => ¬ (parents p coordinate = true))).card =
          sub.val.card :=
    Finset.card_filter_add_card_filter_not (s := sub.val)
      (fun p => parents p coordinate = true)
  rw [sub.property] at hsplit
  cases hc : children sub coordinate
  · have hfilter :
        sub.val.filter
          (fun parent => parents parent coordinate ≠ children sub coordinate) =
        sub.val.filter (fun p => parents p coordinate = true) := by
      apply Finset.filter_congr
      intro x _
      rw [hc]
      simp
    show (sub.val.filter
      (fun parent => parents parent coordinate ≠ children sub coordinate)).card = _
    rw [hfilter]
    simp [hj]
  · have hfilter :
        sub.val.filter
          (fun parent => parents parent coordinate ≠ children sub coordinate) =
        sub.val.filter (fun p => ¬ (parents p coordinate = true)) := by
      apply Finset.filter_congr
      intro x _
      rw [hc]
    show (sub.val.filter
      (fun parent => parents parent coordinate ≠ children sub coordinate)).card = _
    rw [hfilter]
    simp only [if_true]
    omega

theorem sum_rMismatchCount
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    (∑ sub : RLayer parentCount r 1,
      (rMismatchCount parents children coordinate sub : ℝ)) =
      ∑ bitType : RBitType r,
        ((bitType.val : ℝ) *
            (((rTypeGroup parents coordinate bitType).card : ℝ) -
              ((rTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ)) +
          ((r : ℝ) - (bitType.val : ℝ)) *
            ((rTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ)) := by
  classical
  have hmaps :
      (((Finset.univ : Finset (RLayer parentCount r 1)) :
        Set (RLayer parentCount r 1))).MapsTo
          (rCoordinateBitType parents coordinate)
          (Finset.univ : Finset (RBitType r)) := fun _ _ => Finset.mem_univ _
  rw [← Finset.sum_fiberwise_of_maps_to hmaps
    (fun sub => (rMismatchCount parents children coordinate sub : ℝ))]
  refine Finset.sum_congr rfl fun bitType _ => ?_
  have hgroup :
      (Finset.univ.filter
        (fun sub : RLayer parentCount r 1 =>
          rCoordinateBitType parents coordinate sub = bitType)) =
        rTypeGroup parents coordinate bitType := by
    simp [rTypeGroup]
  rw [hgroup]
  have honesle :=
    rTypeGroupChildOnes_card_le parents children coordinate bitType
  have hjr : bitType.val ≤ r := bitType_le bitType
  have hcr : ((r - bitType.val : ℕ) : ℝ) = (r : ℝ) - (bitType.val : ℝ) := by
    rw [Nat.cast_sub hjr]
  have hones :
      (rTypeGroup parents coordinate bitType).filter
        (fun sub => children sub coordinate = true) =
      rTypeGroupChildOnes parents children coordinate bitType := by
    simp [rTypeGroupChildOnes]
  have hcard :
      ((rTypeGroup parents coordinate bitType).filter
        (fun sub => ¬ (children sub coordinate = true))).card =
        (rTypeGroup parents coordinate bitType).card -
          (rTypeGroupChildOnes parents children coordinate bitType).card := by
    have hsplit := Finset.card_filter_add_card_filter_not
      (s := rTypeGroup parents coordinate bitType)
      (fun sub => children sub coordinate = true)
    rw [hones] at hsplit
    omega
  have hconst1 : ∀ sub ∈
      rTypeGroupChildOnes parents children coordinate bitType,
      (rMismatchCount parents children coordinate sub : ℝ) =
        (r : ℝ) - (bitType.val : ℝ) := by
    intro sub hsub
    have hmem : sub ∈ (rTypeGroup parents coordinate bitType).filter
        (fun t => children t coordinate = true) := by rw [hones]; exact hsub
    obtain ⟨hgrp, hchild⟩ := Finset.mem_filter.mp hmem
    have htype : rCoordinateBitType parents coordinate sub = bitType :=
      (Finset.mem_filter.mp hgrp).2
    rw [rMismatchCount_eq, hchild, htype]
    simp only [if_true]
    exact hcr
  have hconst2 : ∀ sub ∈
      (rTypeGroup parents coordinate bitType).filter
        (fun sub => ¬ (children sub coordinate = true)),
      (rMismatchCount parents children coordinate sub : ℝ) =
        (bitType.val : ℝ) := by
    intro sub hsub
    obtain ⟨hgrp, hchild⟩ := Finset.mem_filter.mp hsub
    have htype : rCoordinateBitType parents coordinate sub = bitType :=
      (Finset.mem_filter.mp hgrp).2
    have hfalse : children sub coordinate = false := by
      cases hcv : children sub coordinate
      · rfl
      · exact absurd hcv hchild
    rw [rMismatchCount_eq, hfalse, htype]
    simp
  rw [← Finset.sum_filter_add_sum_filter_not
    (rTypeGroup parents coordinate bitType)
    (fun sub => children sub coordinate = true)]
  rw [hones, Finset.sum_congr rfl hconst1, Finset.sum_congr rfl hconst2,
    Finset.sum_const, Finset.sum_const, nsmul_eq_mul, nsmul_eq_mul, hcard,
    Nat.cast_sub honesle]
  ring

theorem rCoordinateKernel_worAverageDisagreement
    (hparents : r ≤ parentCount) (hpos : 0 < parentCount) (hr : 0 < r)
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    worRExpectation r parentCount
        (pairParentCoordinateOneCount parents coordinate)
        (fun x =>
          (∑ i, BinaryPairKernel.bitDisagreementProbability (x i)
            ((rCoordinateKernel hpos parents children
              coordinate).childProbability x)) / (r : ℝ)) =
      (∑ sub : RLayer parentCount r 1,
        (rMismatchCount parents children coordinate sub : ℝ)) /
        ((r : ℝ) * (parentCount.choose r : ℝ)) := by
  have hchoose : (0 : ℝ) < (parentCount.choose r : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have h := worRExpectation_of_type hparents parents coordinate
    (fun x =>
      (∑ i, BinaryPairKernel.bitDisagreementProbability (x i)
        ((rCoordinateKernel hpos parents children
          coordinate).childProbability x)) / (r : ℝ))
    (fun bitType =>
      ((bitType.val : ℝ) *
          (1 - ((rTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
            ((rTypeGroup parents coordinate bitType).card : ℝ)) +
        ((r : ℝ) - (bitType.val : ℝ)) *
          (((rTypeGroupChildOnes parents children
            coordinate bitType).card : ℝ) /
            ((rTypeGroup parents coordinate bitType).card : ℝ))) / (r : ℝ))
    (by
      intro x
      rw [sum_bitDisagreement x
        ((rCoordinateKernel hpos parents children coordinate).childProbability x)]
      have hcast : ((r - popcount x : ℕ) : ℝ) = (r : ℝ) - (popcount x : ℝ) :=
        Nat.cast_sub (popcount_le x)
      rw [hcast]
      simp only [rCoordinateKernel_childProbability, rBitTypeOfWord_val]
      try ring)
  rw [h]
  have hterm : ∀ bitType : RBitType r,
      ((rTypeGroup parents coordinate bitType).card : ℝ) /
          (parentCount.choose r : ℝ) *
        (((bitType.val : ℝ) *
            (1 - ((rTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
              ((rTypeGroup parents coordinate bitType).card : ℝ)) +
          ((r : ℝ) - (bitType.val : ℝ)) *
            (((rTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ) /
              ((rTypeGroup parents coordinate bitType).card : ℝ))) / (r : ℝ)) =
        ((bitType.val : ℝ) *
            (((rTypeGroup parents coordinate bitType).card : ℝ) -
              ((rTypeGroupChildOnes parents children
                coordinate bitType).card : ℝ)) +
          ((r : ℝ) - (bitType.val : ℝ)) *
            ((rTypeGroupChildOnes parents children
              coordinate bitType).card : ℝ)) /
          ((r : ℝ) * (parentCount.choose r : ℝ)) := by
    intro bitType
    have hrat := group_prob_mul_ratio hparents parents children coordinate bitType
    have hcpl := group_prob_mul_complement hparents parents children coordinate bitType
    set A := ((rTypeGroup parents coordinate bitType).card : ℝ)
    set B := ((rTypeGroupChildOnes parents children coordinate bitType).card : ℝ)
    set C := (parentCount.choose r : ℝ)
    have hstep : A / C * (((bitType.val : ℝ) * (1 - B / A) +
        ((r : ℝ) - (bitType.val : ℝ)) * (B / A)) / (r : ℝ)) =
        ((bitType.val : ℝ) * (A / C * (1 - B / A)) +
          ((r : ℝ) - (bitType.val : ℝ)) * (A / C * (B / A))) / (r : ℝ) := by
      ring
    rw [hstep, hrat, hcpl]
    field_simp
  rw [Finset.sum_congr rfl (fun bitType _ => hterm bitType), ← Finset.sum_div,
    ← sum_rMismatchCount parents children coordinate]

theorem sum_rMismatchCount_eq_hammingDist
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension) :
    (∑ coordinate : Fin dimension,
      ∑ sub : RLayer parentCount r 1,
        rMismatchCount parents children coordinate sub) =
      ∑ sub : RLayer parentCount r 1,
        ∑ parent ∈ sub.val,
          hammingDist (parents parent) (children sub) := by
  classical
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun sub _ => ?_
  have hcount (coordinate : Fin dimension) :
      rMismatchCount parents children coordinate sub =
        ∑ parent ∈ sub.val,
          if parents parent coordinate ≠ children sub coordinate
            then 1 else 0 := by
    change (sub.val.filter
      (fun parent =>
        parents parent coordinate ≠ children sub coordinate)).card = _
    exact (Finset.sum_boole _ _).symm
  simp_rw [hcount]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun parent _ => ?_
  change (∑ coordinate : Fin dimension,
      if parents parent coordinate ≠ children sub coordinate
        then 1 else 0) =
    ((Finset.univ : Finset (Fin dimension)).filter
      (fun coordinate =>
        parents parent coordinate ≠ children sub coordinate)).card
  exact Finset.sum_boole _ _

/-! ### The per-coordinate ledger bound -/

theorem rChildCoordinateOneCount_le
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    rChildCoordinateOneCount children coordinate ≤ parentCount.choose r := by
  classical
  unfold rChildCoordinateOneCount booleanWordOnes
  calc (Finset.univ.filter
      (fun sub : RLayer parentCount r 1 =>
        children sub coordinate = true)).card ≤
        (Finset.univ : Finset (RLayer parentCount r 1)).card :=
      Finset.card_filter_le _ _
    _ = parentCount.choose r := by
      rw [Finset.card_univ, rLayer_one_card]

/-- **The per-coordinate empirical ledger bound**, `r`-generic.
All arity-specific analysis sits in `hbound : TypeEntropyBound r A lam`.
The threshold is `2r² ≤ L` — strictly stronger than the kernel's own `r² ≤ L`,
because the modulus-of-continuity step needs `r²/L ≤ 1/2`.  At `r = 3` this is
`L ≥ 18`, versus the published `L ≥ 10`. -/
theorem rCoordinateConditionalEntropy_empirical_bound
    {A lam : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam)
    (hbound : TypeEntropyBound r A lam)
    (hL : 2 * r ^ 2 ≤ parentCount)
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (coordinate : Fin dimension) :
    rCoordinateConditionalEntropy parents children coordinate ≤
      A + lam *
          ((∑ sub : RLayer parentCount r 1,
            (rMismatchCount parents children coordinate sub : ℝ)) /
            ((r : ℝ) * (parentCount.choose r : ℝ))) +
        (binaryEntropy
            ((rChildCoordinateOneCount children coordinate : ℝ) /
              (parentCount.choose r : ℝ)) -
          binaryEntropy
            ((pairParentCoordinateOneCount parents coordinate : ℝ) /
              (parentCount : ℝ))) / 2 +
      worCorrectionR r parentCount lam := by
  classical
  have hr1 : 1 ≤ r := hr
  have hsq : r ^ 2 ≤ parentCount := by nlinarith [hr, sq_nonneg r]
  have hrL : r ≤ parentCount := le_trans (Nat.le_self_pow (by omega) r) hsq
  have hpos : 0 < parentCount := lt_of_lt_of_le hr hrL
  have hNreal : (0 : ℝ) < (parentCount : ℝ) := by exact_mod_cast hpos
  have hchoose : (0 : ℝ) < (parentCount.choose r : ℝ) := by
    exact_mod_cast Nat.choose_pos hrL
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  set kernel := rCoordinateKernel hpos parents children coordinate with hkernel
  set childMean : ℝ :=
    (rChildCoordinateOneCount children coordinate : ℝ) /
      (parentCount.choose r : ℝ) with hchildMeandef
  -- the entropy observable
  have hEeq := rCoordinateKernel_worConditionalEntropy hrL hpos parents children
    coordinate
  have hEerr := worRExpectation_error hr1 hsq parents coordinate
    (fun x => binaryEntropy (kernel.childProbability x))
    (fun x => binaryEntropy_nonneg (kernel.childProbability_nonneg x)
      (kernel.childProbability_le_one x))
    (fun x => binaryEntropy_le_one _)
  have hEiid : iidRExpectation r
      ((pairParentCoordinateOneCount parents coordinate : ℝ) / (parentCount : ℝ))
      (fun x => binaryEntropy (kernel.childProbability x)) =
      kernel.conditionalEntropy := rfl
  rw [hEiid, hEeq] at hEerr
  -- the marginal observable
  have hMeq := rCoordinateKernel_worChildMarginal hrL hpos parents children coordinate
  have hMerr := worRExpectation_error hr1 hsq parents coordinate
    kernel.childProbability kernel.childProbability_nonneg
    kernel.childProbability_le_one
  have hMiid : iidRExpectation r
      ((pairParentCoordinateOneCount parents coordinate : ℝ) / (parentCount : ℝ))
      kernel.childProbability = kernel.childMarginal := rfl
  rw [hMiid, hMeq] at hMerr
  -- the disagreement observable
  have hDeq := rCoordinateKernel_worAverageDisagreement hrL hpos hr parents children
    coordinate
  have hDobs : ∀ x : Fin r → Bool,
      0 ≤ (∑ i, BinaryPairKernel.bitDisagreementProbability (x i)
            (kernel.childProbability x)) / (r : ℝ) ∧
        (∑ i, BinaryPairKernel.bitDisagreementProbability (x i)
            (kernel.childProbability x)) / (r : ℝ) ≤ 1 := by
    intro x
    have h0 := kernel.childProbability_nonneg x
    have h1 := kernel.childProbability_le_one x
    have hsum := sum_bitDisagreement x (kernel.childProbability x)
    have hcast : ((r - popcount x : ℕ) : ℝ) = (r : ℝ) - (popcount x : ℝ) :=
      Nat.cast_sub (popcount_le x)
    rw [hcast] at hsum
    have hple : (popcount x : ℝ) ≤ (r : ℝ) := by
      exact_mod_cast popcount_le x
    have hp0 : (0 : ℝ) ≤ (popcount x : ℝ) := Nat.cast_nonneg _
    constructor
    · rw [hsum]
      apply div_nonneg _ hrr.le
      nlinarith
    · rw [hsum, div_le_one hrr]
      nlinarith
  have hDerr := worRExpectation_error hr1 hsq parents coordinate
    (fun x =>
      (∑ i, BinaryPairKernel.bitDisagreementProbability (x i)
        (kernel.childProbability x)) / (r : ℝ))
    (fun x => (hDobs x).1) (fun x => (hDobs x).2)
  have hDiid : iidRExpectation r
      ((pairParentCoordinateOneCount parents coordinate : ℝ) / (parentCount : ℝ))
      (fun x =>
        (∑ i, BinaryPairKernel.bitDisagreementProbability (x i)
          (kernel.childProbability x)) / (r : ℝ)) =
      kernel.averageDisagreement := rfl
  rw [hDiid, hDeq] at hDerr
  -- bounds for the ledger
  have hchildMean0 : 0 ≤ childMean := by rw [hchildMeandef]; positivity
  have hchildMean1 : childMean ≤ 1 := by
    rw [hchildMeandef]
    exact (div_le_one hchoose).mpr
      (by exact_mod_cast rChildCoordinateOneCount_le children coordinate)
  have hrsqL : (r : ℝ) ^ 2 / (parentCount : ℝ) ≤ 1 / 2 := by
    have hcast : 2 * (r : ℝ) ^ 2 ≤ (parentCount : ℝ) := by exact_mod_cast hL
    rw [div_le_div_iff₀ hNreal (by norm_num)]
    linarith
  have hrsqpos : (0 : ℝ) ≤ (r : ℝ) ^ 2 / (parentCount : ℝ) := by positivity
  have habs : |childMean - kernel.childMarginal| ≤
      (r : ℝ) ^ 2 / (parentCount : ℝ) := hMerr
  have hrsqL' : (r : ℝ) ^ 2 / (parentCount : ℝ) ≤ (2 : ℝ)⁻¹ := by
    rw [inv_eq_one_div]; exact hrsqL
  have hcont : binaryEntropy |childMean - kernel.childMarginal| ≤
      binaryEntropy ((r : ℝ) ^ 2 / (parentCount : ℝ)) :=
    binaryEntropy_mono_on_half _ _ (abs_nonneg _) habs hrsqL'
  have hledger := ledger_inequality hr hlam hbound parentCount kernel
    (rCoordinateConditionalEntropy parents children coordinate)
    ((∑ sub : RLayer parentCount r 1,
      (rMismatchCount parents children coordinate sub : ℝ)) /
      ((r : ℝ) * (parentCount.choose r : ℝ)))
    childMean hchildMean0 hchildMean1
    (by linarith [(abs_le.mp hEerr).2])
    (by linarith [(abs_le.mp hDerr).1])
    (habs.trans hrsqL) hcont
  have hparentProb : kernel.parentProbability =
      (pairParentCoordinateOneCount parents coordinate : ℝ) /
        (parentCount : ℝ) := rfl
  rw [hparentProb] at hledger
  exact hledger

/-! ## §6 Array-level potentials, disagreement and the ledger -/

noncomputable def rParentArrayEntropyPotential
    (parents : Fin parentCount → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      ((pairParentCoordinateOneCount parents coordinate : ℝ) /
        (parentCount : ℝ))) / (dimension : ℝ)

noncomputable def rChildArrayEntropyPotential (r : ℕ)
    (children : RLayer parentCount r 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      ((rChildCoordinateOneCount children coordinate : ℝ) /
        (parentCount.choose r : ℝ))) / (dimension : ℝ)

noncomputable def rChildArrayAverageDisagreement (r : ℕ)
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension) : ℝ :=
  (∑ coordinate : Fin dimension,
    (∑ sub : RLayer parentCount r 1,
      (rMismatchCount parents children coordinate sub : ℝ)) /
      ((r : ℝ) * (parentCount.choose r : ℝ))) / (dimension : ℝ)

theorem rChildArrayEntropy_empirical_bound
    {A lam : ℝ} (hr : 0 < r) (hlam : 0 ≤ lam)
    (hbound : TypeEntropyBound r A lam)
    (hL : 2 * r ^ 2 ≤ parentCount) (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension) :
    rChildArrayEntropy parents children ≤
      A + lam * rChildArrayAverageDisagreement r parents children +
        (rChildArrayEntropyPotential r children -
          rParentArrayEntropyPotential parents) / 2 +
      worCorrectionR r parentCount lam := by
  have hdim : (0 : ℝ) < (dimension : ℝ) := by exact_mod_cast hdimension
  set E : Fin dimension → ℝ :=
    fun coordinate =>
      rCoordinateConditionalEntropy parents children coordinate with hE
  set D : Fin dimension → ℝ :=
    fun coordinate =>
      (∑ sub : RLayer parentCount r 1,
        (rMismatchCount parents children coordinate sub : ℝ)) /
        ((r : ℝ) * (parentCount.choose r : ℝ)) with hD
  set Hc : Fin dimension → ℝ :=
    fun coordinate =>
      binaryEntropy
        ((rChildCoordinateOneCount children coordinate : ℝ) /
          (parentCount.choose r : ℝ)) with hHc
  set Hp : Fin dimension → ℝ :=
    fun coordinate =>
      binaryEntropy
        ((pairParentCoordinateOneCount parents coordinate : ℝ) /
          (parentCount : ℝ)) with hHp
  have hpointwise : ∀ coordinate : Fin dimension,
      E coordinate ≤ A + lam * D coordinate +
        (Hc coordinate - Hp coordinate) / 2 + worCorrectionR r parentCount lam :=
    fun coordinate =>
      rCoordinateConditionalEntropy_empirical_bound hr hlam hbound hL parents
        children coordinate
  have hsum : (∑ coordinate : Fin dimension, E coordinate) ≤
      ∑ coordinate : Fin dimension,
        (A + lam * D coordinate +
          (Hc coordinate - Hp coordinate) / 2 + worCorrectionR r parentCount lam) :=
    Finset.sum_le_sum fun coordinate _ => hpointwise coordinate
  have hexpand :
      (∑ coordinate : Fin dimension,
        (A + lam * D coordinate +
          (Hc coordinate - Hp coordinate) / 2 + worCorrectionR r parentCount lam)) =
        (dimension : ℝ) * A + lam *
          (∑ coordinate : Fin dimension, D coordinate) +
          ((∑ coordinate : Fin dimension, Hc coordinate) -
            (∑ coordinate : Fin dimension, Hp coordinate)) / 2 +
          (dimension : ℝ) * worCorrectionR r parentCount lam := by
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib,
      ← Finset.mul_sum, ← Finset.sum_div, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  rw [hexpand] at hsum
  show (∑ coordinate : Fin dimension, E coordinate) / (dimension : ℝ) ≤ _
  unfold rChildArrayAverageDisagreement rChildArrayEntropyPotential
    rParentArrayEntropyPotential
  rw [div_le_iff₀ hdim]
  have hrhs :
      (A + lam *
          ((∑ coordinate : Fin dimension, D coordinate) / (dimension : ℝ)) +
        (((∑ coordinate : Fin dimension, Hc coordinate) / (dimension : ℝ)) -
          ((∑ coordinate : Fin dimension, Hp coordinate) / (dimension : ℝ))) / 2 +
        worCorrectionR r parentCount lam) * (dimension : ℝ) =
      (dimension : ℝ) * A + lam *
        (∑ coordinate : Fin dimension, D coordinate) +
        ((∑ coordinate : Fin dimension, Hc coordinate) -
          (∑ coordinate : Fin dimension, Hp coordinate)) / 2 +
        (dimension : ℝ) * worCorrectionR r parentCount lam := by
    field_simp
  rw [hrhs]
  exact hsum

theorem rChildArrayAverageDisagreement_le_radius
    (hr : 0 < r) (hparents : r ≤ parentCount) (hdimension : 0 < dimension)
    (parents : Fin parentCount → HammingWord dimension)
    (children : RLayer parentCount r 1 → HammingWord dimension)
    (radius : ℕ)
    (hedges : ∀ (sub : RLayer parentCount r 1)
      (parent : RLayer parentCount r 0),
        parent ∈ sub.val →
          hammingDist (parents parent) (children sub) ≤ radius) :
    rChildArrayAverageDisagreement r parents children ≤
      (radius : ℝ) / (dimension : ℝ) := by
  classical
  have hchoose : (0 : ℝ) < (parentCount.choose r : ℝ) := by
    exact_mod_cast Nat.choose_pos hparents
  have hdim : (0 : ℝ) < (dimension : ℝ) := by exact_mod_cast hdimension
  have hrr : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have htotal :
      (∑ coordinate : Fin dimension,
        ∑ sub : RLayer parentCount r 1,
          rMismatchCount parents children coordinate sub) ≤
        r * parentCount.choose r * radius := by
    calc (∑ coordinate : Fin dimension,
        ∑ sub : RLayer parentCount r 1,
          rMismatchCount parents children coordinate sub) =
        ∑ sub : RLayer parentCount r 1,
          ∑ parent ∈ sub.val,
            hammingDist (parents parent) (children sub) :=
        sum_rMismatchCount_eq_hammingDist parents children
      _ ≤ ∑ sub : RLayer parentCount r 1,
            ∑ _parent ∈ sub.val, radius := by
        refine Finset.sum_le_sum fun sub _ => ?_
        exact Finset.sum_le_sum fun parent hparent => hedges sub parent hparent
      _ = ∑ _sub : RLayer parentCount r 1, r * radius := by
        refine Finset.sum_congr rfl fun sub _ => ?_
        simp [sub.property]
      _ = r * parentCount.choose r * radius := by
        simp only [Finset.sum_const, Finset.card_univ, rLayer_one_card,
          smul_eq_mul]
        ring
  have htotal_real :
      (∑ coordinate : Fin dimension,
        ((∑ sub : RLayer parentCount r 1,
          rMismatchCount parents children coordinate sub : ℕ) : ℝ)) ≤
        (r : ℝ) * (parentCount.choose r : ℝ) * (radius : ℝ) := by
    exact_mod_cast htotal
  have hcast : ∀ coordinate : Fin dimension,
      (∑ sub : RLayer parentCount r 1,
        (rMismatchCount parents children coordinate sub : ℝ)) =
      ((∑ sub : RLayer parentCount r 1,
        rMismatchCount parents children coordinate sub : ℕ) : ℝ) := by
    intro coordinate; push_cast; rfl
  unfold rChildArrayAverageDisagreement
  simp_rw [hcast]
  rw [← Finset.sum_div]
  apply (div_le_div_iff_of_pos_right hdim).mpr
  apply (div_le_iff₀ (by positivity :
    (0:ℝ) < (r : ℝ) * (parentCount.choose r : ℝ))).mpr
  nlinarith

/-! ## §7 The exclusion ledger

The `depth · increment > 1` contradiction.  Arity-free; restated here so that
`AssemblyR` (which owns the `SimpleGraph.Copy` transport — see the status note
in `results_Z_lean_bridgeR.md`) can consume it without importing `Theorem12r3`. -/

/-- **The generic potential induction.**  A `[0,1]`-valued potential cannot
gain more than `gap` per layer for `depth` layers if `depth · gap > 1`. -/
theorem potential_layers_impossible (depth : ℕ) (potential : ℕ → ℝ) (gap : ℝ)
    (hrange : ∀ i ≤ depth, 0 ≤ potential i ∧ potential i ≤ 1)
    (hincrement : ∀ i < depth, gap < potential (i + 1) - potential i)
    (hdepth : 1 < (depth : ℝ) * gap) : False := by
  have htotal : ∀ i ≤ depth, (i : ℝ) * gap ≤ potential i - potential 0 := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
        have hprevious := ih (by omega)
        have hnext := (hincrement i (by omega)).le
        push_cast
        linarith
  have hstart := (hrange 0 (by omega)).1
  have hfinish := (hrange depth le_rfl).2
  have hsum := htotal depth le_rfl
  linarith

/-- The per-layer potential increment forced by the exclusion, `r`-generic.
`entropyLowerEndpoint = A + lam·τ_r` is the ledger constant in bits. -/
noncomputable def potentialIncrement (beta slack entropyLowerEndpoint : ℝ) : ℝ :=
  2 * (beta - 2 * slack - entropyLowerEndpoint)

/-- **One layer of the exclusion ledger**, `r`-generic version of
`Theorem12r3.potential_increment_three`.  `error` is the without-replacement
correction `worCorrectionR r L lam`, which must be below `slack` — that is the
constraint forcing `L ≥ max(2r², counting threshold)` at instantiation. -/
theorem potential_increment
    (beta slack entropyLowerEndpoint : ℝ)
    (potentialBefore potentialAfter conditionalEntropy error : ℝ)
    (herror : error < slack)
    (hlower : beta - slack < conditionalEntropy)
    (hupper : conditionalEntropy ≤
      entropyLowerEndpoint + (potentialAfter - potentialBefore) / 2 + error) :
    potentialIncrement beta slack entropyLowerEndpoint <
      potentialAfter - potentialBefore := by
  unfold potentialIncrement
  linarith

/-! ### Layer sizes: `L ≤ C(L, r)`

The `r`-generic `Theorem12r3.le_choose_three_of_four`. -/
theorem le_choose_of_succ_le {size : ℕ} (hr : 1 ≤ r) (hsize : r + 1 ≤ size) :
    size ≤ size.choose r := by
  rcases Nat.eq_or_lt_of_le hr with hr1 | hr1
  · -- r = 1
    subst_vars
    simp
  · -- 2 ≤ r
    have hr2 : 2 ≤ r := hr1
    induction size, hsize using Nat.le_induction with
    | base =>
        have h1 : (r + 1).choose r = r + 1 := by
          have hsym := Nat.choose_symm (n := r + 1) (k := 1) (by omega)
          simp
        omega
    | succ n hn ih =>
        have hstep : (n + 1).choose r = n.choose (r - 1) + n.choose r := by
          obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
          simpa using Nat.choose_succ_succ' n k
        have hprev : n.choose (r - 1) ≥ 1 :=
          Nat.choose_pos (by omega)
        omega

theorem rLayer_card_ge_base (baseSize i : ℕ) (hr : 1 ≤ r)
    (hbase : r + 1 ≤ baseSize) :
    baseSize ≤ Fintype.card (RLayer baseSize r i) := by
  induction i with
  | zero => rw [rLayer_card_zero]
  | succ i ih =>
      rw [rLayer_card_succ]
      exact ih.trans (le_choose_of_succ_le hr (by omega))

end RGenericBridge
