import CompactnessAndDegeneracy

/-!
# The `r`-generic kernel bridge (`BinaryRKernel`)

`r`-generic port of `Kernel3.lean` (namespace `ThreeDegenerateGraphs`), which
was the `r = 3` port of the `BinaryPairKernel` development inside
`CompactnessAndDegeneracy.lean`.

Executing Recommendation 1 of `research/results_U_generic_survey.md`:

* **§1 the popcount-fibre lemma.**  A sum over `Fin r → Bool` collapses to a
  sum over the `r+1` popcount fibres weighted by `C(r,j)`, and the same with
  per-coordinate i.i.d. weights.  This is what replaces every
  `cases l <;> cases m <;> cases r`/`Fintype.univ_bool` enumeration of the
  `r = 3` file: **nothing below ever case-splits on the `r` bits.**
* **§2 the kernel.**  `BinaryRKernel r` with child law
  `childProbability : (Fin r → Bool) → ℝ`; its marginal, conditional entropy
  and average disagreement; the type-collapse `H(Z | X⃗) ≤ Σⱼ P(j) h(pⱼ)` by
  Jensen on each fibre; the bound itself, and its extension past the boundary
  cases `v ∈ {0,1}` by smoothing.
* **§3 without-replacement**, redesigned around `Nat.descFactorial` (the
  `r = 3` file's `L(L-1)(L-2)` and `interval_cases` proofs do not port).
* **§4 the `r`-generic ledger inequality.**

**The entropy input is a hypothesis.**  `Entropy3.conditional_entropy_bound`
(with `A₀ = 17/80`, `λ = 7/4`, `α = 1/2`) is `r = 3`-specific.  Everything here
is stated relative to `TypeEntropyBound r A lam`, the per-type inequality
`Σⱼ P(j) h(pⱼ) ≤ A·log 2 + λ·log 2·d + (h(v) − h(q))/2`, supplied per `r`.

**Checking.**
```
cd proofs
lake env sh -c 'LEAN_PATH="$LEAN_PATH:$PWD/erdos-degeneracy" lean erdos-degeneracy/KernelR.lean'
```
-/

open TwoDegenerateGraphs Finset

namespace RGenericKernel

/-! ## §1 The popcount fibration of `Fin r → Bool`

The single lemma flagged by the survey as unblocking both `KernelR` and
`BridgeR`. -/

/-- The number of `1`s of a Boolean word of length `r`. -/
def popcount {r : ℕ} (x : Fin r → Bool) : ℕ :=
  (univ.filter fun i => x i = true).card

theorem popcount_le {r : ℕ} (x : Fin r → Bool) : popcount x ≤ r := by
  classical
  simpa [popcount] using
    (card_filter_le (univ : Finset (Fin r)) fun i => x i = true).trans_eq
      (by simp)

theorem popcount_lt_succ {r : ℕ} (x : Fin r → Bool) : popcount x < r + 1 :=
  Nat.lt_succ_of_le (popcount_le x)

/-- The popcount fibre. -/
noncomputable def popcountFibre (r j : ℕ) : Finset (Fin r → Bool) :=
  univ.filter fun x => popcount x = j

theorem mem_popcountFibre {r j : ℕ} {x : Fin r → Bool} :
    x ∈ popcountFibre r j ↔ popcount x = j := by
  simp [popcountFibre]

/-- **The fibre count.**  `#{x : Fin r → Bool // popcount x = j} = C(r, j)`. -/
theorem popcountFibre_card (r j : ℕ) :
    (popcountFibre r j).card = r.choose j := by
  classical
  have hbij :
      (popcountFibre r j).card =
        ((univ : Finset (Fin r)).powersetCard j).card := by
    refine Finset.card_bij'
      (fun x _ => (univ.filter fun i => x i = true))
      (fun S _ => fun i => decide (i ∈ S)) ?_ ?_ ?_ ?_
    · intro x hx
      rw [mem_popcountFibre] at hx
      exact Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, hx⟩
    · intro S hS
      rw [Finset.mem_powersetCard] at hS
      rw [mem_popcountFibre]
      have : (univ.filter fun i => (decide (i ∈ S)) = true) = S := by
        ext i; simp
      simpa [popcount, this] using hS.2
    · intro x _
      funext i
      simp
    · intro S _
      ext i
      simp
  rw [hbij, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]

/-- **The popcount-fibre lemma.**  Any function of the popcount sums over
`Fin r → Bool` as a binomially weighted sum over `{0, …, r}`. -/
theorem sum_bool_word_popcount {M : Type*} [AddCommMonoid M]
    (r : ℕ) (g : ℕ → M) :
    (∑ x : Fin r → Bool, g (popcount x)) =
      ∑ j ∈ range (r + 1), (r.choose j) • g j := by
  classical
  have hmaps :
      ∀ x ∈ (univ : Finset (Fin r → Bool)), popcount x ∈ range (r + 1) :=
    fun x _ => Finset.mem_range.mpr (popcount_lt_succ x)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfib : (univ.filter fun x : Fin r → Bool => popcount x = j) =
      popcountFibre r j := rfl
  rw [hfib]
  have hconst : ∀ x ∈ popcountFibre r j, g (popcount x) = g j :=
    fun x hx => by rw [mem_popcountFibre.mp hx]
  rw [Finset.sum_congr rfl hconst, Finset.sum_const, popcountFibre_card]

/-- Real-valued form of `sum_bool_word_popcount`. -/
theorem sum_bool_word_popcount_real (r : ℕ) (g : ℕ → ℝ) :
    (∑ x : Fin r → Bool, g (popcount x)) =
      ∑ j ∈ range (r + 1), (r.choose j : ℝ) * g j := by
  rw [sum_bool_word_popcount r g]
  exact Finset.sum_congr rfl fun j _ => by rw [nsmul_eq_mul]

/-! ### The i.i.d. product weight -/

/-- The per-coordinate i.i.d. weight of a Boolean word depends only on its
popcount. -/
theorem prod_ite_eq_pow_popcount {r : ℕ} (w0 w1 : ℝ) (x : Fin r → Bool) :
    (∏ i, if x i then w1 else w0) = w1 ^ popcount x * w0 ^ (r - popcount x) := by
  classical
  have hsplit :
      (∏ i, if x i then w1 else w0) =
        (∏ i ∈ univ.filter fun i => x i = true, if x i then w1 else w0) *
          (∏ i ∈ univ.filter fun i => ¬ (x i = true), if x i then w1 else w0) :=
    (Finset.prod_filter_mul_prod_filter_not _ _ _).symm
  have hone : (∏ i ∈ univ.filter fun i => x i = true, if x i then w1 else w0)
      = w1 ^ popcount x := by
    have hpt : ∀ i ∈ univ.filter fun i => x i = true,
        (if x i then w1 else w0) = w1 := by
      intro i hi
      simp [(Finset.mem_filter.mp hi).2]
    rw [Finset.prod_congr rfl hpt, Finset.prod_const]
    rfl
  have hzero : (∏ i ∈ univ.filter fun i => ¬ (x i = true), if x i then w1 else w0)
      = w0 ^ (r - popcount x) := by
    have hpt : ∀ i ∈ univ.filter fun i => ¬ (x i = true),
        (if x i then w1 else w0) = w0 := by
      intro i hi
      have h := (Finset.mem_filter.mp hi).2
      simp only [Bool.not_eq_true] at h
      simp [h]
    rw [Finset.prod_congr rfl hpt, Finset.prod_const]
    congr 1
    have hcount := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin r))) (p := fun i => x i = true)
    have hr : (univ : Finset (Fin r)).card = r := by simp
    rw [hr] at hcount
    have : popcount x + (univ.filter fun i => ¬ (x i = true)).card = r := by
      simpa [popcount] using hcount
    omega
  rw [hsplit, hone, hzero]

/-- **The weighted popcount-fibre lemma.**  With per-coordinate i.i.d. weights
`w1` (on `true`) and `w0` (on `false`). -/
theorem sum_bool_word_weighted (r : ℕ) (w0 w1 : ℝ) (g : ℕ → ℝ) :
    (∑ x : Fin r → Bool, (∏ i, if x i then w1 else w0) * g (popcount x)) =
      ∑ j ∈ range (r + 1),
        (r.choose j : ℝ) * (w1 ^ j * w0 ^ (r - j) * g j) := by
  have hstep :
      (∑ x : Fin r → Bool, (∏ i, if x i then w1 else w0) * g (popcount x)) =
        ∑ x : Fin r → Bool,
          (fun j => w1 ^ j * w0 ^ (r - j) * g j) (popcount x) :=
    Finset.sum_congr rfl fun x _ => by rw [prod_ite_eq_pow_popcount]
  rw [hstep]
  exact sum_bool_word_popcount_real r (fun j => w1 ^ j * w0 ^ (r - j) * g j)

/-- **The fibrewise regrouping.**  For an arbitrary observable `f` (not just a
function of the popcount), the i.i.d. weight is constant on fibres and factors
out.  This is the form actually used by the kernel. -/
theorem sum_fibrewise (r : ℕ) (w0 w1 : ℝ) (f : (Fin r → Bool) → ℝ) :
    (∑ x : Fin r → Bool, w1 ^ popcount x * w0 ^ (r - popcount x) * f x) =
      ∑ j ∈ range (r + 1),
        w1 ^ j * w0 ^ (r - j) * ∑ x ∈ popcountFibre r j, f x := by
  classical
  have hmaps :
      ∀ x ∈ (univ : Finset (Fin r → Bool)), popcount x ∈ range (r + 1) :=
    fun x _ => Finset.mem_range.mpr (popcount_lt_succ x)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfib : (univ.filter fun x : Fin r → Bool => popcount x = j) =
      popcountFibre r j := rfl
  rw [hfib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun x hx => ?_
  rw [mem_popcountFibre.mp hx]

/-! ## §2 The `r`-generic kernel -/

/-- Analogue of `TwoDegenerateGraphs.independentBinaryPairMass` and of
`ThreeDegenerateGraphs.independentBinaryTripleMass`. -/
def independentBinaryRMass {r : ℕ} (q : ℝ) (x : Fin r → Bool) : ℝ :=
  ∏ i, binaryCoinMass q (x i)

theorem independentBinaryRMass_eq {r : ℕ} (q : ℝ) (x : Fin r → Bool) :
    independentBinaryRMass q x =
      q ^ popcount x * (1 - q) ^ (r - popcount x) := by
  have : independentBinaryRMass q x = ∏ i, if x i then q else 1 - q :=
    Finset.prod_congr rfl fun i _ => rfl
  rw [this, prod_ite_eq_pow_popcount]

theorem independentBinaryRMass_nonneg {r : ℕ} {q : ℝ}
    (hqzero : 0 ≤ q) (hqone : q ≤ 1) (x : Fin r → Bool) :
    0 ≤ independentBinaryRMass q x := by
  rw [independentBinaryRMass_eq]
  have : (0 : ℝ) ≤ 1 - q := by linarith
  positivity

theorem independentBinaryRMass_sum (r : ℕ) (q : ℝ) :
    (∑ x : Fin r → Bool, independentBinaryRMass (r := r) q x) = 1 := by
  have key := sum_bool_word_weighted r (1 - q) q (fun _ => (1 : ℝ))
  have hrw : (∑ x : Fin r → Bool, independentBinaryRMass (r := r) q x) =
      ∑ x : Fin r → Bool, (∏ i, if x i then q else 1 - q) * (1 : ℝ) := by
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [mul_one]
    exact Finset.prod_congr rfl fun i _ => rfl
  refine hrw.trans (key.trans ?_)
  have hbinom := add_pow q (1 - q) r
  simp only [mul_one]
  rw [show (∑ j ∈ range (r + 1), (r.choose j : ℝ) * (q ^ j * (1 - q) ^ (r - j))) =
      ∑ j ∈ range (r + 1), q ^ j * (1 - q) ^ (r - j) * (r.choose j : ℝ) from
    Finset.sum_congr rfl fun j _ => by ring, ← hbinom]
  simp

/-! ### Type averages and Jensen on a fibre -/

/-- The total of an observable over the popcount-`j` fibre. -/
noncomputable def typeSum {r : ℕ} (f : (Fin r → Bool) → ℝ) (j : ℕ) : ℝ :=
  ∑ x ∈ popcountFibre r j, f x

/-- The average of an observable over the popcount-`j` fibre; for the child law
this is the type-conditional probability `pⱼ`. -/
noncomputable def typeAvg {r : ℕ} (f : (Fin r → Bool) → ℝ) (j : ℕ) : ℝ :=
  typeSum f j / (r.choose j : ℝ)

theorem popcountFibre_eq_empty_of_choose_zero {r j : ℕ} (h : r.choose j = 0) :
    popcountFibre r j = ∅ :=
  Finset.card_eq_zero.mp (by rw [popcountFibre_card, h])

theorem typeSum_eq_mul {r j : ℕ} (f : (Fin r → Bool) → ℝ) :
    typeSum f j = (r.choose j : ℝ) * typeAvg f j := by
  unfold typeAvg
  rcases Nat.eq_zero_or_pos (r.choose j) with h | h
  · rw [h]
    simp [typeSum, popcountFibre_eq_empty_of_choose_zero h]
  · have hne : (r.choose j : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr h.ne'
    field_simp

theorem typeSum_affine {r j : ℕ} (f : (Fin r → Bool) → ℝ) (a b : ℝ) :
    typeSum (fun x => a * (1 - f x) + b * f x) j =
      (r.choose j : ℝ) * (a * (1 - typeAvg f j) + b * typeAvg f j) := by
  have hpt : ∀ x ∈ popcountFibre r j,
      a * (1 - f x) + b * f x = a + (b - a) * f x := fun x _ => by ring
  unfold typeSum
  rw [Finset.sum_congr rfl hpt, Finset.sum_add_distrib, Finset.sum_const,
    ← Finset.mul_sum, popcountFibre_card, nsmul_eq_mul]
  rw [show (∑ x ∈ popcountFibre r j, f x) = typeSum f j from rfl, typeSum_eq_mul]
  ring

theorem typeSum_one {r : ℕ} (j : ℕ) :
    typeSum (fun _ : Fin r → Bool => (1 : ℝ)) j = (r.choose j : ℝ) := by
  simp [typeSum, popcountFibre_card]

theorem typeAvg_nonneg {r j : ℕ} {f : (Fin r → Bool) → ℝ}
    (h0 : ∀ x, 0 ≤ f x) : 0 ≤ typeAvg f j :=
  div_nonneg (Finset.sum_nonneg fun x _ => h0 x) (Nat.cast_nonneg _)

theorem typeAvg_le_one {r j : ℕ} {f : (Fin r → Bool) → ℝ}
    (h1 : ∀ x, f x ≤ 1) : typeAvg f j ≤ 1 := by
  unfold typeAvg
  rcases Nat.eq_zero_or_pos (r.choose j) with h | h
  · rw [h]; simp
  · have hpos : (0 : ℝ) < (r.choose j : ℝ) := by exact_mod_cast h
    refine (div_le_one hpos).mpr ?_
    calc typeSum f j ≤ ∑ _x ∈ popcountFibre r j, (1 : ℝ) :=
          Finset.sum_le_sum fun x _ => h1 x
      _ = (r.choose j : ℝ) := by simp [popcountFibre_card]

/-- **Jensen on a popcount fibre.**  The type collapse: replacing the `C(r,j)`
ordered outcomes of type `j` by their average can only increase the entropy. -/
theorem typeSum_binEntropy_le {r j : ℕ} (f : (Fin r → Bool) → ℝ)
    (h0 : ∀ x, 0 ≤ f x) (h1 : ∀ x, f x ≤ 1) :
    typeSum (fun x => Real.binEntropy (f x)) j ≤
      (r.choose j : ℝ) * Real.binEntropy (typeAvg f j) := by
  rcases Nat.eq_zero_or_pos (r.choose j) with h | h
  · rw [h]
    simp [typeSum, popcountFibre_eq_empty_of_choose_zero h]
  · have hpos : (0 : ℝ) < (r.choose j : ℝ) := by exact_mod_cast h
    have hconcave : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) Real.binEntropy :=
      Real.strictConcave_binEntropy.concaveOn
    have hw : ∑ _x ∈ popcountFibre r j, (1 / (r.choose j : ℝ)) = 1 := by
      rw [Finset.sum_const, popcountFibre_card, nsmul_eq_mul]
      field_simp
    have hjensen := hconcave.le_map_sum
      (t := popcountFibre r j) (w := fun _ => 1 / (r.choose j : ℝ)) (p := f)
      (fun x _ => by positivity) hw (fun x _ => ⟨h0 x, h1 x⟩)
    simp only [smul_eq_mul] at hjensen
    have harg : (∑ x ∈ popcountFibre r j, (1 / (r.choose j : ℝ)) * f x) =
        typeAvg f j := by
      rw [← Finset.mul_sum]
      unfold typeAvg typeSum
      ring
    rw [harg, ← Finset.mul_sum] at hjensen
    have := mul_le_mul_of_nonneg_left hjensen hpos.le
    rw [← mul_assoc] at this
    calc typeSum (fun x => Real.binEntropy (f x)) j
        = (r.choose j : ℝ) * (1 / (r.choose j : ℝ)) *
            ∑ x ∈ popcountFibre r j, Real.binEntropy (f x) := by
          rw [mul_one_div, div_self hpos.ne', one_mul]; rfl
      _ ≤ (r.choose j : ℝ) * Real.binEntropy (typeAvg f j) := this

/-- The disagreement count of a Boolean word is affine in the child
probability, with coefficients depending only on the popcount. -/
theorem sum_bitDisagreement {r : ℕ} (x : Fin r → Bool) (z : ℝ) :
    (∑ i, BinaryPairKernel.bitDisagreementProbability (x i) z) =
      (popcount x : ℝ) * (1 - z) + ((r - popcount x : ℕ) : ℝ) * z := by
  classical
  have hsplit :
      (∑ i, BinaryPairKernel.bitDisagreementProbability (x i) z) =
        (∑ i ∈ univ.filter fun i => x i = true,
            BinaryPairKernel.bitDisagreementProbability (x i) z) +
          (∑ i ∈ univ.filter fun i => ¬ (x i = true),
            BinaryPairKernel.bitDisagreementProbability (x i) z) :=
    (Finset.sum_filter_add_sum_filter_not _ _ _).symm
  have hone : (∑ i ∈ univ.filter fun i => x i = true,
      BinaryPairKernel.bitDisagreementProbability (x i) z) =
        (popcount x : ℝ) * (1 - z) := by
    have hpt : ∀ i ∈ univ.filter fun i => x i = true,
        BinaryPairKernel.bitDisagreementProbability (x i) z = 1 - z := by
      intro i hi
      simp [BinaryPairKernel.bitDisagreementProbability,
        (Finset.mem_filter.mp hi).2]
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul]
    rfl
  have hzero : (∑ i ∈ univ.filter fun i => ¬ (x i = true),
      BinaryPairKernel.bitDisagreementProbability (x i) z) =
        ((r - popcount x : ℕ) : ℝ) * z := by
    have hpt : ∀ i ∈ univ.filter fun i => ¬ (x i = true),
        BinaryPairKernel.bitDisagreementProbability (x i) z = z := by
      intro i hi
      have h := (Finset.mem_filter.mp hi).2
      simp only [Bool.not_eq_true] at h
      simp [BinaryPairKernel.bitDisagreementProbability, h]
    rw [Finset.sum_congr rfl hpt, Finset.sum_const, nsmul_eq_mul]
    congr 2
    have hcount := Finset.card_filter_add_card_filter_not
      (s := (univ : Finset (Fin r))) (p := fun i => x i = true)
    have hr : (univ : Finset (Fin r)).card = r := by simp
    rw [hr] at hcount
    have : popcount x + (univ.filter fun i => ¬ (x i = true)).card = r := by
      simpa [popcount] using hcount
    omega
  rw [hsplit, hone, hzero]

/-- The `r`-generic analogue of `BinaryPairKernel` / `BinaryTripleKernel`.
The child law is an arbitrary (not necessarily exchangeable) conditional
probability over *ordered* parent words `Fin r → Bool`. -/
structure BinaryRKernel (r : ℕ) where
  parentProbability : ℝ
  parentProbability_nonneg : 0 ≤ parentProbability
  parentProbability_le_one : parentProbability ≤ 1
  childProbability : (Fin r → Bool) → ℝ
  childProbability_nonneg : ∀ x, 0 ≤ childProbability x
  childProbability_le_one : ∀ x, childProbability x ≤ 1

namespace BinaryRKernel

variable {r : ℕ}

noncomputable def childMarginal (kernel : BinaryRKernel r) : ℝ :=
  ∑ x : Fin r → Bool,
    independentBinaryRMass kernel.parentProbability x * kernel.childProbability x

/-- `H(Z | X⃗)` in **bits**. -/
noncomputable def conditionalEntropy (kernel : BinaryRKernel r) : ℝ :=
  ∑ x : Fin r → Bool,
    independentBinaryRMass kernel.parentProbability x *
      binaryEntropy (kernel.childProbability x)

/-- `d = (1/r) Σₐ P(Xₐ ≠ Z)`. -/
noncomputable def averageDisagreement (kernel : BinaryRKernel r) : ℝ :=
  ∑ x : Fin r → Bool,
    independentBinaryRMass kernel.parentProbability x *
      ((∑ i, BinaryPairKernel.bitDisagreementProbability (x i)
          (kernel.childProbability x)) / (r : ℝ))

theorem childMarginal_nonneg (kernel : BinaryRKernel r) :
    0 ≤ kernel.childMarginal :=
  Finset.sum_nonneg fun x _ =>
    mul_nonneg
      (independentBinaryRMass_nonneg kernel.parentProbability_nonneg
        kernel.parentProbability_le_one x)
      (kernel.childProbability_nonneg x)

theorem childMarginal_le_one (kernel : BinaryRKernel r) :
    kernel.childMarginal ≤ 1 := by
  calc kernel.childMarginal
      ≤ ∑ x : Fin r → Bool,
          independentBinaryRMass kernel.parentProbability x * 1 :=
        Finset.sum_le_sum fun x _ =>
          mul_le_mul_of_nonneg_left (kernel.childProbability_le_one x)
            (independentBinaryRMass_nonneg kernel.parentProbability_nonneg
              kernel.parentProbability_le_one x)
    _ = 1 := by
        simpa using independentBinaryRMass_sum r kernel.parentProbability

/-! ### The type collapse

Three normal forms replacing `Kernel3`'s `*_eq_eight_outcomes`: the marginal
and the disagreement are *linear* in the child law, so the collapse to the
`r+1` type numbers is an identity; the entropy is *concave*, so the collapse is
an inequality (Jensen). -/

/-- `pⱼ = P(Z = 1 | popcount X⃗ = j)`, the type-conditional child probability. -/
noncomputable def typeProbability (kernel : BinaryRKernel r) (j : ℕ) : ℝ :=
  typeAvg kernel.childProbability j

/-- `P(popcount X⃗ = j) = C(r,j) qʲ (1−q)^{r−j}`. -/
noncomputable def typeWeight (kernel : BinaryRKernel r) (j : ℕ) : ℝ :=
  (r.choose j : ℝ) * kernel.parentProbability ^ j *
    (1 - kernel.parentProbability) ^ (r - j)

theorem typeProbability_nonneg (kernel : BinaryRKernel r) (j : ℕ) :
    0 ≤ kernel.typeProbability j :=
  typeAvg_nonneg kernel.childProbability_nonneg

theorem typeProbability_le_one (kernel : BinaryRKernel r) (j : ℕ) :
    kernel.typeProbability j ≤ 1 :=
  typeAvg_le_one kernel.childProbability_le_one

theorem typeWeight_nonneg (kernel : BinaryRKernel r) (j : ℕ) :
    0 ≤ kernel.typeWeight j := by
  have h : (0 : ℝ) ≤ 1 - kernel.parentProbability := by
    linarith [kernel.parentProbability_le_one]
  unfold typeWeight
  have := kernel.parentProbability_nonneg
  positivity

/-- **Normal form 1.**  The child marginal in terms of the `r+1` type numbers. -/
theorem childMarginal_eq_types (kernel : BinaryRKernel r) :
    kernel.childMarginal =
      ∑ j ∈ range (r + 1), kernel.typeWeight j * kernel.typeProbability j := by
  have hmass : ∀ x : Fin r → Bool,
      independentBinaryRMass kernel.parentProbability x *
          kernel.childProbability x =
        kernel.parentProbability ^ popcount x *
          (1 - kernel.parentProbability) ^ (r - popcount x) *
          kernel.childProbability x :=
    fun x => by rw [independentBinaryRMass_eq]
  rw [childMarginal, Finset.sum_congr rfl (fun x _ => hmass x),
    sum_fibrewise r (1 - kernel.parentProbability) kernel.parentProbability]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [show (∑ x ∈ popcountFibre r j, kernel.childProbability x) =
      typeSum kernel.childProbability j from rfl, typeSum_eq_mul]
  unfold typeWeight typeProbability
  ring

/-- **Normal form 2.**  The average disagreement in terms of the type numbers.
`Σᵢ P(Xᵢ ≠ Z)` on the popcount-`j` fibre is `j(1−pⱼ) + (r−j)pⱼ`. -/
theorem averageDisagreement_eq_types (hr : 0 < r) (kernel : BinaryRKernel r) :
    (r : ℝ) * kernel.averageDisagreement =
      ∑ j ∈ range (r + 1), kernel.typeWeight j *
        ((j : ℝ) * (1 - kernel.typeProbability j) +
          ((r - j : ℕ) : ℝ) * kernel.typeProbability j) := by
  have hrne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hstep : ∀ x : Fin r → Bool,
      (r : ℝ) * (independentBinaryRMass kernel.parentProbability x *
          ((∑ i, BinaryPairKernel.bitDisagreementProbability (x i)
              (kernel.childProbability x)) / (r : ℝ))) =
        kernel.parentProbability ^ popcount x *
          (1 - kernel.parentProbability) ^ (r - popcount x) *
          ((popcount x : ℝ) * (1 - kernel.childProbability x) +
            ((r - popcount x : ℕ) : ℝ) * kernel.childProbability x) := by
    intro x
    rw [independentBinaryRMass_eq, sum_bitDisagreement]
    field_simp
  rw [averageDisagreement, Finset.mul_sum,
    Finset.sum_congr rfl (fun x _ => hstep x),
    sum_fibrewise r (1 - kernel.parentProbability) kernel.parentProbability]
  refine Finset.sum_congr rfl fun j _ => ?_
  have hfib : (∑ x ∈ popcountFibre r j,
      ((popcount x : ℝ) * (1 - kernel.childProbability x) +
        ((r - popcount x : ℕ) : ℝ) * kernel.childProbability x)) =
      typeSum (fun x => (j : ℝ) * (1 - kernel.childProbability x) +
        ((r - j : ℕ) : ℝ) * kernel.childProbability x) j := by
    refine Finset.sum_congr rfl fun x hx => ?_
    rw [mem_popcountFibre.mp hx]
  rw [hfib, typeSum_affine]
  unfold typeWeight typeProbability
  ring

/-- **Normal form 3** (an *inequality*: Jensen).  The conditional entropy is at
most the type-collapsed entropy. -/
theorem conditionalEntropy_mul_log_two_le (kernel : BinaryRKernel r) :
    kernel.conditionalEntropy * Real.log 2 ≤
      ∑ j ∈ range (r + 1),
        kernel.typeWeight j * Real.binEntropy (kernel.typeProbability j) := by
  have hq : (0 : ℝ) ≤ kernel.parentProbability := kernel.parentProbability_nonneg
  have hq' : (0 : ℝ) ≤ 1 - kernel.parentProbability := by
    linarith [kernel.parentProbability_le_one]
  have hlhs : kernel.conditionalEntropy * Real.log 2 =
      ∑ x : Fin r → Bool,
        kernel.parentProbability ^ popcount x *
          (1 - kernel.parentProbability) ^ (r - popcount x) *
          Real.binEntropy (kernel.childProbability x) := by
    rw [conditionalEntropy, Finset.sum_mul]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [independentBinaryRMass_eq]
    unfold binaryEntropy
    field_simp
  rw [hlhs, sum_fibrewise r (1 - kernel.parentProbability) kernel.parentProbability]
  refine Finset.sum_le_sum fun j _ => ?_
  have hnn : (0 : ℝ) ≤ kernel.parentProbability ^ j *
      (1 - kernel.parentProbability) ^ (r - j) := by positivity
  have hJ := typeSum_binEntropy_le (j := j) kernel.childProbability
    kernel.childProbability_nonneg kernel.childProbability_le_one
  calc kernel.parentProbability ^ j * (1 - kernel.parentProbability) ^ (r - j) *
        ∑ x ∈ popcountFibre r j, Real.binEntropy (kernel.childProbability x)
      ≤ kernel.parentProbability ^ j * (1 - kernel.parentProbability) ^ (r - j) *
          ((r.choose j : ℝ) *
            Real.binEntropy (typeAvg kernel.childProbability j)) :=
        mul_le_mul_of_nonneg_left hJ hnn
    _ = kernel.typeWeight j * Real.binEntropy (kernel.typeProbability j) := by
        unfold typeWeight typeProbability
        ring

end BinaryRKernel

/-! ### The entropy input, as a hypothesis

`Entropy3.conditional_entropy_bound` (`A₀ = 17/80`, `λ = 7/4`, `α = 1/2`) is
`r = 3`-specific — its proof rests on hand-tuned numeric certificates
(`residual_cubic_pos` and the `θ`, `σ₀`, `σ₁` enclosures).  So the `r`-generic
chain takes the per-type inequality as a hypothesis and never opens it. -/

/-- The per-type conditional-entropy bound at arity `r` with constants
`A` (in bits) and `λ`.  At `r = 3` this is exactly
`ThreeDegenerateGraphs.conditional_entropy_bound` with `A = 17/80`, `λ = 7/4`. -/
def TypeEntropyBound (r : ℕ) (A lam : ℝ) : Prop :=
  ∀ q v d : ℝ, ∀ p : ℕ → ℝ,
    0 ≤ q → q ≤ 1 → 0 < v → v < 1 →
    (∀ j, 0 ≤ p j) → (∀ j, p j ≤ 1) →
    v = ∑ j ∈ range (r + 1), (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) * p j →
    (r : ℝ) * d = ∑ j ∈ range (r + 1),
      (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) *
        ((j : ℝ) * (1 - p j) + ((r - j : ℕ) : ℝ) * p j) →
    (∑ j ∈ range (r + 1), (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) *
        Real.binEntropy (p j)) ≤
      A * Real.log 2 + lam * Real.log 2 * d +
        (Real.binEntropy v - Real.binEntropy q) / 2

namespace BinaryRKernel

variable {r : ℕ}

/-- **The `r`-generic kernel bound, interior case.**  Analogue of
`ThreeDegenerateGraphs.BinaryTripleKernel.conditionalEntropy_bound_of_marginal_interior`. -/
theorem conditionalEntropy_bound_of_marginal_interior (hr : 0 < r)
    {A lam : ℝ} (hbound : TypeEntropyBound r A lam)
    (kernel : BinaryRKernel r)
    (hmarginal_zero : 0 < kernel.childMarginal)
    (hmarginal_one : kernel.childMarginal < 1) :
    kernel.conditionalEntropy ≤
      A + lam * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2 := by
  have hv := kernel.childMarginal_eq_types
  have hd := kernel.averageDisagreement_eq_types hr
  unfold typeWeight at hv hd
  have htypes := hbound kernel.parentProbability kernel.childMarginal
    kernel.averageDisagreement kernel.typeProbability
    kernel.parentProbability_nonneg kernel.parentProbability_le_one
    hmarginal_zero hmarginal_one
    kernel.typeProbability_nonneg kernel.typeProbability_le_one hv hd
  have hjensen := kernel.conditionalEntropy_mul_log_two_le
  unfold typeWeight at hjensen
  have hchain : kernel.conditionalEntropy * Real.log 2 ≤
      A * Real.log 2 + lam * Real.log 2 * kernel.averageDisagreement +
        (Real.binEntropy kernel.childMarginal -
          Real.binEntropy kernel.parentProbability) / 2 :=
    hjensen.trans htypes
  have hright :
      (A + lam * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2) * Real.log 2 =
        A * Real.log 2 + lam * Real.log 2 * kernel.averageDisagreement +
          (Real.binEntropy kernel.childMarginal -
            Real.binEntropy kernel.parentProbability) / 2 := by
    unfold binaryEntropy
    field_simp [log_two_pos.ne']
  refine (mul_le_mul_iff_of_pos_right log_two_pos).mp ?_
  rw [hright]
  exact hchain

/-! ### Boundary cases `v ∈ {0,1}` by smoothing

Structurally identical to the `r = 2` and `r = 3` arguments; the normal forms
are no longer needed because the smoothing identities follow directly from
`independentBinaryRMass_sum`. -/

noncomputable def smoothed (kernel : BinaryRKernel r)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing) (hmixing_one : mixing ≤ 1) :
    BinaryRKernel r where
  parentProbability := kernel.parentProbability
  parentProbability_nonneg := kernel.parentProbability_nonneg
  parentProbability_le_one := kernel.parentProbability_le_one
  childProbability x := (1 - mixing) * kernel.childProbability x + mixing / 2
  childProbability_nonneg := by
    intro x
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hmixing_one) (kernel.childProbability_nonneg x))
      (div_nonneg hmixing_zero (by norm_num))
  childProbability_le_one := by
    intro x
    have hproduct := mul_le_mul_of_nonneg_left
      (kernel.childProbability_le_one x) (sub_nonneg.mpr hmixing_one)
    nlinarith

theorem smoothed_childMarginal (kernel : BinaryRKernel r)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing) (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).childMarginal =
      (1 - mixing) * kernel.childMarginal + mixing / 2 := by
  have hpt : ∀ x : Fin r → Bool,
      independentBinaryRMass kernel.parentProbability x *
          ((1 - mixing) * kernel.childProbability x + mixing / 2) =
        (1 - mixing) *
          (independentBinaryRMass kernel.parentProbability x *
            kernel.childProbability x) +
          mixing / 2 * independentBinaryRMass kernel.parentProbability x :=
    fun x => by ring
  show (∑ x : Fin r → Bool,
      independentBinaryRMass kernel.parentProbability x *
        ((1 - mixing) * kernel.childProbability x + mixing / 2)) = _
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum,
    independentBinaryRMass_sum r kernel.parentProbability]
  rw [show (∑ x : Fin r → Bool,
      independentBinaryRMass kernel.parentProbability x *
        kernel.childProbability x) = kernel.childMarginal from rfl]
  ring

theorem smoothed_averageDisagreement (hr : 0 < r) (kernel : BinaryRKernel r)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing) (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).averageDisagreement =
      (1 - mixing) * kernel.averageDisagreement + mixing / 2 := by
  have hrne : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hr.ne'
  have hbd : ∀ (b : Bool) (z : ℝ),
      BinaryPairKernel.bitDisagreementProbability b ((1 - mixing) * z + mixing / 2) =
        (1 - mixing) * BinaryPairKernel.bitDisagreementProbability b z + mixing / 2 := by
    intro b z
    cases b <;> simp [BinaryPairKernel.bitDisagreementProbability]
    ring
  have hsum : ∀ x : Fin r → Bool,
      (∑ i, BinaryPairKernel.bitDisagreementProbability (x i)
          ((1 - mixing) * kernel.childProbability x + mixing / 2)) =
        (1 - mixing) *
            (∑ i, BinaryPairKernel.bitDisagreementProbability (x i)
              (kernel.childProbability x)) + (r : ℝ) * (mixing / 2) := by
    intro x
    rw [Finset.sum_congr rfl (fun i _ => hbd (x i) (kernel.childProbability x)),
      Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul]
  have hpt : ∀ x : Fin r → Bool,
      independentBinaryRMass kernel.parentProbability x *
          ((∑ i, BinaryPairKernel.bitDisagreementProbability (x i)
            ((1 - mixing) * kernel.childProbability x + mixing / 2)) / (r : ℝ)) =
        (1 - mixing) *
          (independentBinaryRMass kernel.parentProbability x *
            ((∑ i, BinaryPairKernel.bitDisagreementProbability (x i)
              (kernel.childProbability x)) / (r : ℝ))) +
          mixing / 2 * independentBinaryRMass kernel.parentProbability x := by
    intro x
    rw [hsum x]
    field_simp
  show (∑ x : Fin r → Bool,
      independentBinaryRMass kernel.parentProbability x *
        ((∑ i, BinaryPairKernel.bitDisagreementProbability (x i)
          ((1 - mixing) * kernel.childProbability x + mixing / 2)) / (r : ℝ))) = _
  rw [Finset.sum_congr rfl (fun x _ => hpt x), Finset.sum_add_distrib,
    ← Finset.mul_sum, ← Finset.mul_sum,
    independentBinaryRMass_sum r kernel.parentProbability]
  rw [show (∑ x : Fin r → Bool,
      independentBinaryRMass kernel.parentProbability x *
        ((∑ i, BinaryPairKernel.bitDisagreementProbability (x i)
          (kernel.childProbability x)) / (r : ℝ))) =
      kernel.averageDisagreement from rfl]
  ring

noncomputable def smoothedConditionalEntropy
    (kernel : BinaryRKernel r) (mixing : ℝ) : ℝ :=
  ∑ x : Fin r → Bool,
    independentBinaryRMass kernel.parentProbability x *
      binaryEntropy ((1 - mixing) * kernel.childProbability x + mixing / 2)

theorem smoothedConditionalEntropy_continuous (kernel : BinaryRKernel r) :
    Continuous (smoothedConditionalEntropy kernel) := by
  unfold smoothedConditionalEntropy
  fun_prop

theorem smoothed_conditionalEntropy (kernel : BinaryRKernel r)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing) (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).conditionalEntropy =
      smoothedConditionalEntropy kernel mixing := rfl

/-- **The `r`-generic kernel bound.**  Analogue of
`ThreeDegenerateGraphs.BinaryTripleKernel.conditionalEntropy_bound`; no
interiority hypothesis on the child marginal. -/
theorem conditionalEntropy_bound (hr : 0 < r)
    {A lam : ℝ} (hbound : TypeEntropyBound r A lam)
    (kernel : BinaryRKernel r) :
    kernel.conditionalEntropy ≤
      A + lam * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2 := by
  let mixing : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hmixing_pos (n : ℕ) : 0 < mixing n := by dsimp [mixing]; positivity
  have hmixing_le_one (n : ℕ) : mixing n ≤ 1 := by
    dsimp [mixing]
    refine (div_le_one (by positivity)).mpr ?_
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  let approximation : ℕ → BinaryRKernel r := fun n =>
    smoothed kernel (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hmixing_tendsto : Filter.Tendsto mixing Filter.atTop (nhds 0) := by
    simpa [mixing] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmarginal_zero (n : ℕ) : 0 < (approximation n).childMarginal := by
    have hformula := smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
    change 0 < (smoothed kernel (mixing n)
      (hmixing_pos n).le (hmixing_le_one n)).childMarginal
    rw [hformula]
    have h1 := mul_nonneg (sub_nonneg.mpr (hmixing_le_one n))
      (childMarginal_nonneg kernel)
    have h2 := div_pos (hmixing_pos n) (by norm_num : (0 : ℝ) < 2)
    linarith
  have hmarginal_one (n : ℕ) : (approximation n).childMarginal < 1 := by
    have hformula := smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
    change (smoothed kernel (mixing n)
      (hmixing_pos n).le (hmixing_le_one n)).childMarginal < 1
    rw [hformula]
    have hproduct := mul_le_mul_of_nonneg_left (childMarginal_le_one kernel)
      (sub_nonneg.mpr (hmixing_le_one n))
    have hpositive := hmixing_pos n
    nlinarith
  have hconditional_tendsto :
      Filter.Tendsto (fun n => (approximation n).conditionalEntropy)
        Filter.atTop (nhds kernel.conditionalEntropy) := by
    have hcontinuous :=
      (smoothedConditionalEntropy_continuous kernel).continuousAt.tendsto.comp
        hmixing_tendsto
    have hzero : smoothedConditionalEntropy kernel 0 = kernel.conditionalEntropy := by
      simp [smoothedConditionalEntropy, conditionalEntropy]
    rw [hzero] at hcontinuous
    refine hcontinuous.congr' ?_
    filter_upwards [] with n
    exact (smoothed_conditionalEntropy kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)).symm
  have hmarginal_tendsto :
      Filter.Tendsto (fun n => (approximation n).childMarginal)
        Filter.atTop (nhds kernel.childMarginal) := by
    have hlinear := ((tendsto_const_nhds (x := (1 : ℝ))).sub hmixing_tendsto).mul
      (tendsto_const_nhds (x := kernel.childMarginal))
    have hpath := hlinear.add (hmixing_tendsto.div_const 2)
    have hpath' :
        Filter.Tendsto (fun n => (1 - mixing n) * kernel.childMarginal + mixing n / 2)
          Filter.atTop (nhds kernel.childMarginal) := by simpa using hpath
    convert hpath' using 1
    funext n
    exact smoothed_childMarginal kernel (mixing n) (hmixing_pos n).le
      (hmixing_le_one n)
  have hdisagreement_tendsto :
      Filter.Tendsto (fun n => (approximation n).averageDisagreement)
        Filter.atTop (nhds kernel.averageDisagreement) := by
    have hlinear := ((tendsto_const_nhds (x := (1 : ℝ))).sub hmixing_tendsto).mul
      (tendsto_const_nhds (x := kernel.averageDisagreement))
    have hpath := hlinear.add (hmixing_tendsto.div_const 2)
    have hpath' :
        Filter.Tendsto
          (fun n => (1 - mixing n) * kernel.averageDisagreement + mixing n / 2)
          Filter.atTop (nhds kernel.averageDisagreement) := by simpa using hpath
    convert hpath' using 1
    funext n
    exact smoothed_averageDisagreement hr kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hchildentropy_tendsto :=
    binaryEntropy_continuous.continuousAt.tendsto.comp hmarginal_tendsto
  have hparent (n : ℕ) :
      (approximation n).parentProbability = kernel.parentProbability := rfl
  have hright_tendsto :
      Filter.Tendsto
        (fun n =>
          A + lam * (approximation n).averageDisagreement +
            (binaryEntropy (approximation n).childMarginal -
              binaryEntropy (approximation n).parentProbability) / 2)
        Filter.atTop
        (nhds
          (A + lam * kernel.averageDisagreement +
            (binaryEntropy kernel.childMarginal -
              binaryEntropy kernel.parentProbability) / 2)) := by
    simp_rw [hparent]
    have hd := (tendsto_const_nhds (x := lam)).mul hdisagreement_tendsto
    have he := (hchildentropy_tendsto.sub
      (tendsto_const_nhds (x := binaryEntropy kernel.parentProbability))).div_const 2
    have hsum := (tendsto_const_nhds (x := A)).add (hd.add he)
    simpa [add_assoc] using hsum
  refine le_of_tendsto_of_tendsto' hconditional_tendsto hright_tendsto ?_
  intro n
  exact conditionalEntropy_bound_of_marginal_interior hr hbound
    (approximation n) (hmarginal_zero n) (hmarginal_one n)

end BinaryRKernel

/-! ## §3 Sampling `r` *distinct* parents

`Kernel3`'s `withoutReplacementBinaryTripleMass` used the explicit product
`L(L−1)(L−2)` and discharged positivity by `interval_cases`/`nlinarith`; that
does not port.  The survey calls for a redesign around `Nat.descFactorial`,
which is what follows.  The probability that an ordered sample of `r` *distinct*
indices out of `L` (of which `k` carry a `1`) realises the pattern `x` is

`k^(j) · (L−k)^(r−j) / L^(r)`,  `j = popcount x`,

with `n^(m) = Nat.descFactorial n m`.  Everything below is a function of the
popcount, so §1 applies directly. -/

/-- Vandermonde in descending-factorial form:
`Σⱼ C(r,j) k^(j) (L−k)^(r−j) = L^(r)`.  This is what makes the
without-replacement law a probability distribution. -/
theorem sum_choose_descFactorial {parentCount oneCount : ℕ} (r : ℕ)
    (hones : oneCount ≤ parentCount) :
    (∑ j ∈ range (r + 1), r.choose j * oneCount.descFactorial j *
        (parentCount - oneCount).descFactorial (r - j)) =
      parentCount.descFactorial r := by
  have hvan : parentCount.choose r =
      ∑ j ∈ range (r + 1),
        oneCount.choose j * (parentCount - oneCount).choose (r - j) := by
    have hsplit := Nat.add_choose_eq oneCount (parentCount - oneCount) r
    rw [Nat.add_sub_cancel' hones] at hsplit
    rw [hsplit, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  rw [Nat.descFactorial_eq_factorial_mul_choose, hvan, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [Nat.descFactorial_eq_factorial_mul_choose,
    Nat.descFactorial_eq_factorial_mul_choose,
    show r.choose j * (Nat.factorial j * oneCount.choose j) *
        (Nat.factorial (r - j) * (parentCount - oneCount).choose (r - j)) =
      (r.choose j * Nat.factorial j * Nat.factorial (r - j)) *
        (oneCount.choose j * (parentCount - oneCount).choose (r - j)) from by ring,
    Nat.choose_mul_factorial_mul_factorial hj']

/-- The without-replacement mass of an *ordered* parent word.  `r = 3`
analogue: `ThreeDegenerateGraphs.withoutReplacementBinaryTripleMass`. -/
noncomputable def withoutReplacementBinaryRMass
    (r parentCount oneCount : ℕ) (x : Fin r → Bool) : ℝ :=
  ((oneCount.descFactorial (popcount x) *
      (parentCount - oneCount).descFactorial (r - popcount x) : ℕ) : ℝ) /
    ((parentCount.descFactorial r : ℕ) : ℝ)

theorem descFactorial_pos_cast {parentCount r : ℕ} (hr : r ≤ parentCount) :
    (0 : ℝ) < ((parentCount.descFactorial r : ℕ) : ℝ) := by
  have : parentCount.descFactorial r ≠ 0 := by
    rw [Ne, Nat.descFactorial_eq_zero_iff_lt]
    omega
  exact_mod_cast Nat.pos_of_ne_zero this

theorem withoutReplacementBinaryRMass_nonneg
    (r parentCount oneCount : ℕ) (x : Fin r → Bool) :
    0 ≤ withoutReplacementBinaryRMass r parentCount oneCount x :=
  div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)

theorem withoutReplacementBinaryRMass_sum
    {r parentCount oneCount : ℕ}
    (hparents : r ≤ parentCount) (hones : oneCount ≤ parentCount) :
    (∑ x : Fin r → Bool,
      withoutReplacementBinaryRMass r parentCount oneCount x) = 1 := by
  have hD := descFactorial_pos_cast (parentCount := parentCount) (r := r) hparents
  have hrw := sum_bool_word_popcount_real r
    (fun j => ((oneCount.descFactorial j *
        (parentCount - oneCount).descFactorial (r - j) : ℕ) : ℝ) /
      ((parentCount.descFactorial r : ℕ) : ℝ))
  rw [show (∑ x : Fin r → Bool,
      withoutReplacementBinaryRMass r parentCount oneCount x) = _ from hrw]
  have hcollect : ∀ j ∈ range (r + 1),
      (r.choose j : ℝ) *
          (((oneCount.descFactorial j *
            (parentCount - oneCount).descFactorial (r - j) : ℕ) : ℝ) /
            ((parentCount.descFactorial r : ℕ) : ℝ)) =
        ((r.choose j : ℝ) *
          ((oneCount.descFactorial j *
            (parentCount - oneCount).descFactorial (r - j) : ℕ) : ℝ)) /
          ((parentCount.descFactorial r : ℕ) : ℝ) :=
    fun j _ => by ring
  rw [Finset.sum_congr rfl hcollect, ← Finset.sum_div,
    div_eq_one_iff_eq hD.ne']
  have hnat := sum_choose_descFactorial (parentCount := parentCount)
    (oneCount := oneCount) r hones
  calc (∑ j ∈ range (r + 1), (r.choose j : ℝ) *
        ((oneCount.descFactorial j *
          (parentCount - oneCount).descFactorial (r - j) : ℕ) : ℝ))
      = ((∑ j ∈ range (r + 1), r.choose j * oneCount.descFactorial j *
            (parentCount - oneCount).descFactorial (r - j) : ℕ) : ℝ) := by
        push_cast
        exact Finset.sum_congr rfl fun j _ => by ring
    _ = ((parentCount.descFactorial r : ℕ) : ℝ) := by rw [hnat]

/-- **Domination of the without-replacement law by the i.i.d. law**, with the
explicit constant `c = L^r / L^(r)`.  This replaces `Kernel3`'s eight-way
`cases … <;> nlinarith`: the only content is `descFactorial ≤ pow`. -/
theorem withoutReplacementBinaryRMass_le
    {r parentCount oneCount : ℕ}
    (hparents : r ≤ parentCount) (hpos : 0 < parentCount)
    (hones : oneCount ≤ parentCount) (x : Fin r → Bool) :
    withoutReplacementBinaryRMass r parentCount oneCount x ≤
      ((parentCount : ℝ) ^ r / ((parentCount.descFactorial r : ℕ) : ℝ)) *
        independentBinaryRMass ((oneCount : ℝ) / (parentCount : ℝ)) x := by
  have hD := descFactorial_pos_cast (parentCount := parentCount) (r := r) hparents
  have hLpos : (0 : ℝ) < (parentCount : ℝ) := by exact_mod_cast hpos
  have hcast : ((parentCount - oneCount : ℕ) : ℝ) =
      (parentCount : ℝ) - (oneCount : ℝ) := by
    have : (oneCount : ℝ) ≤ (parentCount : ℝ) := by exact_mod_cast hones
    push_cast [Nat.cast_sub hones]
    ring
  have hj := popcount_le x
  have hiid :
      ((parentCount : ℝ) ^ r / ((parentCount.descFactorial r : ℕ) : ℝ)) *
          independentBinaryRMass ((oneCount : ℝ) / (parentCount : ℝ)) x =
        ((oneCount : ℝ) ^ popcount x *
            ((parentCount : ℝ) - oneCount) ^ (r - popcount x)) /
          ((parentCount.descFactorial r : ℕ) : ℝ) := by
    rw [independentBinaryRMass_eq]
    have hone : (1 : ℝ) - (oneCount : ℝ) / (parentCount : ℝ) =
        ((parentCount : ℝ) - oneCount) / (parentCount : ℝ) := by
      field_simp
    rw [hone, div_pow, div_pow]
    have hsplit : (parentCount : ℝ) ^ popcount x *
        (parentCount : ℝ) ^ (r - popcount x) = (parentCount : ℝ) ^ r := by
      rw [← pow_add]
      congr 1
      omega
    rw [div_mul_div_comm, hsplit]
    field_simp
  rw [hiid, withoutReplacementBinaryRMass]
  refine div_le_div_of_nonneg_right ?_ hD.le
  have h1 : ((oneCount.descFactorial (popcount x) : ℕ) : ℝ) ≤
      (oneCount : ℝ) ^ popcount x := by
    exact_mod_cast Nat.descFactorial_le_pow oneCount (popcount x)
  have h2 : (((parentCount - oneCount).descFactorial (r - popcount x) : ℕ) : ℝ) ≤
      ((parentCount : ℝ) - oneCount) ^ (r - popcount x) := by
    rw [← hcast]
    exact_mod_cast Nat.descFactorial_le_pow (parentCount - oneCount) (r - popcount x)
  have hnn1 : (0 : ℝ) ≤ ((oneCount.descFactorial (popcount x) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  have hnn2 : (0 : ℝ) ≤
      (((parentCount - oneCount).descFactorial (r - popcount x) : ℕ) : ℝ) :=
    Nat.cast_nonneg _
  push_cast
  exact mul_le_mul h1 h2 hnn2 (by positivity)

/-! ### The domination constant

`L^r / L^(r) ≤ 1 + r²/L` as soon as `L ≥ r²` — the honest explicit bound
replacing `Kernel3`'s `c − 1 ≤ 4/L for L ≥ 10`.  At `r = 3` it reads
`c − 1 ≤ 9/L for L ≥ 9`, slightly *better* than the published `4/L for L ≥ 10`
on the relevant range in the sense that the shape `r²/L` is now uniform. -/

/-- `L^(r) ≥ L^r (1 − r²/(2L))`.  Induction on `r`; the step is
`(L−r)(1 − r²/(2L)) ≥ L − (r+1)²/2`, which is `r³/(2L) ≥ −1/2`. -/
theorem descFactorial_ge_pow_mul {parentCount : ℕ} (hpos : 0 < parentCount) :
    ∀ r : ℕ, r ≤ parentCount →
      (parentCount : ℝ) ^ r * (1 - (r : ℝ) ^ 2 / (2 * parentCount)) ≤
        ((parentCount.descFactorial r : ℕ) : ℝ) := by
  have hL : (0 : ℝ) < (parentCount : ℝ) := by exact_mod_cast hpos
  intro r
  induction r with
  | zero => intro _; norm_num
  | succ r ih =>
      intro hr
      have hr' : r ≤ parentCount := by omega
      have hstep := ih hr'
      have hsub : ((parentCount - r : ℕ) : ℝ) = (parentCount : ℝ) - (r : ℝ) := by
        push_cast [Nat.cast_sub hr']
        ring
      have hsubnn : (0 : ℝ) ≤ (parentCount : ℝ) - (r : ℝ) := by
        have : (r : ℝ) ≤ (parentCount : ℝ) := by exact_mod_cast hr'
        linarith
      have hcast : ((parentCount.descFactorial (r + 1) : ℕ) : ℝ) =
          ((parentCount : ℝ) - r) * ((parentCount.descFactorial r : ℕ) : ℝ) := by
        rw [Nat.descFactorial_succ]
        push_cast
        rw [hsub]
      rw [hcast]
      have hmul := mul_le_mul_of_nonneg_left hstep hsubnn
      refine le_trans ?_ hmul
      have hpowpos : (0 : ℝ) < (parentCount : ℝ) ^ r := by positivity
      have hkey :
          (parentCount : ℝ) * (1 - ((r : ℝ) + 1) ^ 2 / (2 * parentCount)) ≤
            ((parentCount : ℝ) - r) * (1 - (r : ℝ) ^ 2 / (2 * parentCount)) := by
        rw [← sub_nonneg]
        have hdiff :
            ((parentCount : ℝ) - r) * (1 - (r : ℝ) ^ 2 / (2 * parentCount)) -
              (parentCount : ℝ) * (1 - ((r : ℝ) + 1) ^ 2 / (2 * parentCount)) =
              (r : ℝ) ^ 3 / (2 * parentCount) + 1 / 2 := by
          field_simp
          ring
        rw [hdiff]
        positivity
      push_cast
      calc (parentCount : ℝ) ^ (r + 1) *
            (1 - ((r : ℝ) + 1) ^ 2 / (2 * parentCount))
          = (parentCount : ℝ) ^ r *
              ((parentCount : ℝ) * (1 - ((r : ℝ) + 1) ^ 2 / (2 * parentCount))) := by
            ring
        _ ≤ (parentCount : ℝ) ^ r *
              (((parentCount : ℝ) - r) * (1 - (r : ℝ) ^ 2 / (2 * parentCount))) :=
            mul_le_mul_of_nonneg_left hkey hpowpos.le
        _ = ((parentCount : ℝ) - r) *
              ((parentCount : ℝ) ^ r * (1 - (r : ℝ) ^ 2 / (2 * parentCount))) := by
            ring

/-- **The domination constant.**  `c − 1 ≤ r²/L` whenever `L ≥ r²` and
`r ≥ 1`. -/
theorem domination_constant_le {parentCount r : ℕ} (hr : 1 ≤ r)
    (hL : r ^ 2 ≤ parentCount) :
    (parentCount : ℝ) ^ r / ((parentCount.descFactorial r : ℕ) : ℝ) - 1 ≤
      (r : ℝ) ^ 2 / (parentCount : ℝ) := by
  have hrL : r ≤ parentCount := le_trans (Nat.le_self_pow (by omega) r) hL
  have hpos : 0 < parentCount := by nlinarith [hr, hL, Nat.one_le_two_pow (n := 1)]
  have hLr : (0 : ℝ) < (parentCount : ℝ) := by exact_mod_cast hpos
  have hsq : ((r : ℝ)) ^ 2 ≤ (parentCount : ℝ) := by exact_mod_cast hL
  have hD := descFactorial_pos_cast (parentCount := parentCount) (r := r) hrL
  have hlower := descFactorial_ge_pow_mul hpos r hrL
  have hpowpos : (0 : ℝ) < (parentCount : ℝ) ^ r := by positivity
  -- `1 − r²/(2L) ≥ 1/2`
  have hhalf : (1 : ℝ) / 2 ≤ 1 - (r : ℝ) ^ 2 / (2 * parentCount) := by
    have hfrac : (r : ℝ) ^ 2 / (2 * parentCount) ≤ 1 / 2 := by
      rw [div_le_div_iff₀ (by linarith) (by norm_num)]
      linarith
    linarith
  have hbig : (parentCount : ℝ) ^ r / 2 ≤ ((parentCount.descFactorial r : ℕ) : ℝ) := by
    refine le_trans ?_ hlower
    nlinarith
  rw [div_sub_one hD.ne', div_le_div_iff₀ hD hLr]
  -- `(L^r − D) · L ≤ r² · D`
  have hgap : (parentCount : ℝ) ^ r - ((parentCount.descFactorial r : ℕ) : ℝ) ≤
      (parentCount : ℝ) ^ r * ((r : ℝ) ^ 2 / (2 * parentCount)) := by
    nlinarith [hlower]
  have hDge : (parentCount : ℝ) ^ r ≤ 2 * ((parentCount.descFactorial r : ℕ) : ℝ) := by
    linarith
  have h1 : ((parentCount : ℝ) ^ r - ((parentCount.descFactorial r : ℕ) : ℝ)) *
      (parentCount : ℝ) ≤
      ((parentCount : ℝ) ^ r * ((r : ℝ) ^ 2 / (2 * parentCount))) *
        (parentCount : ℝ) :=
    mul_le_mul_of_nonneg_right hgap hLr.le
  have h2 : ((parentCount : ℝ) ^ r * ((r : ℝ) ^ 2 / (2 * parentCount))) *
      (parentCount : ℝ) = (parentCount : ℝ) ^ r * (r : ℝ) ^ 2 / 2 := by
    field_simp
  have h3 : (parentCount : ℝ) ^ r * (r : ℝ) ^ 2 / 2 ≤
      (2 * ((parentCount.descFactorial r : ℕ) : ℝ)) * (r : ℝ) ^ 2 / 2 := by
    have := mul_le_mul_of_nonneg_right hDge (sq_nonneg (r : ℝ))
    linarith
  linarith

/-! ### Coupling: transferring expectations from i.i.d. to without-replacement

`expectation_le_of_dominated` / `abs_expectation_sub_le_of_dominated` are
already stated for an arbitrary `Fintype ι` in `Kernel3` (survey Regime 1,
"zero changes"); they are restated here so that `KernelR` depends only on
`CompactnessAndDegeneracy`. -/

theorem expectation_le_of_dominated {ι : Type*} [Fintype ι]
    (m₁ m₂ : ι → ℝ) (c : ℝ) (f : ι → ℝ)
    (hm₂ : ∀ i, 0 ≤ m₂ i) (hs₂ : ∑ i, m₂ i = 1)
    (hdom : ∀ i, m₁ i ≤ c * m₂ i)
    (hf : ∀ i, 0 ≤ f i) (hf' : ∀ i, f i ≤ 1) (hc : 1 ≤ c) :
    ∑ i, m₁ i * f i - ∑ i, m₂ i * f i ≤ c - 1 := by
  have hstep : ∀ i, m₁ i * f i - m₂ i * f i ≤ (c - 1) * m₂ i := by
    intro i
    have h1 : (m₁ i - m₂ i) * f i ≤ ((c - 1) * m₂ i) * f i := by
      have hle : m₁ i - m₂ i ≤ (c - 1) * m₂ i := by
        have := hdom i; linarith
      exact mul_le_mul_of_nonneg_right hle (hf i)
    have h2 : ((c - 1) * m₂ i) * f i ≤ ((c - 1) * m₂ i) * 1 :=
      mul_le_mul_of_nonneg_left (hf' i)
        (mul_nonneg (by linarith) (hm₂ i))
    nlinarith [h1, h2]
  calc ∑ i, m₁ i * f i - ∑ i, m₂ i * f i
      = ∑ i, (m₁ i * f i - m₂ i * f i) := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, (c - 1) * m₂ i := Finset.sum_le_sum fun i _ => hstep i
    _ = c - 1 := by rw [← Finset.mul_sum, hs₂, mul_one]

theorem abs_expectation_sub_le_of_dominated {ι : Type*} [Fintype ι]
    (m₁ m₂ : ι → ℝ) (c : ℝ) (f : ι → ℝ)
    (_ : ∀ i, 0 ≤ m₁ i) (hm₂ : ∀ i, 0 ≤ m₂ i)
    (hs₁ : ∑ i, m₁ i = 1) (hs₂ : ∑ i, m₂ i = 1)
    (hdom : ∀ i, m₁ i ≤ c * m₂ i)
    (hf : ∀ i, 0 ≤ f i) (hf' : ∀ i, f i ≤ 1) (hc : 1 ≤ c) :
    |∑ i, m₁ i * f i - ∑ i, m₂ i * f i| ≤ c - 1 := by
  have hup := expectation_le_of_dominated m₁ m₂ c f hm₂ hs₂ hdom hf hf' hc
  have hdown := expectation_le_of_dominated m₁ m₂ c (fun i => 1 - f i) hm₂ hs₂
    hdom (fun i => by linarith [hf' i]) (fun i => by linarith [hf i]) hc
  have e₁ : ∑ i, m₁ i * (1 - f i) = 1 - ∑ i, m₁ i * f i := by
    have h : ∑ i, m₁ i * (1 - f i) = ∑ i, m₁ i - ∑ i, m₁ i * f i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h, hs₁]
  have e₂ : ∑ i, m₂ i * (1 - f i) = 1 - ∑ i, m₂ i * f i := by
    have h : ∑ i, m₂ i * (1 - f i) = ∑ i, m₂ i - ∑ i, m₂ i * f i := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h, hs₂]
  rw [e₁, e₂] at hdown
  rw [abs_le]
  constructor <;> linarith

/-- **The without-replacement error bound**, `r`-generic: every `[0,1]`-valued
observable has the same expectation under the without-replacement and the
i.i.d. parent law up to `r²/L`.  (`r = 3`, `L ≥ 9`: `9/L`, replacing the
published `4/L for L ≥ 10`.) -/
theorem withoutReplacement_expectation_error
    {r parentCount oneCount : ℕ} (hr : 1 ≤ r) (hL : r ^ 2 ≤ parentCount)
    (hones : oneCount ≤ parentCount)
    (f : (Fin r → Bool) → ℝ) (hf : ∀ x, 0 ≤ f x) (hf' : ∀ x, f x ≤ 1) :
    |(∑ x : Fin r → Bool,
        withoutReplacementBinaryRMass r parentCount oneCount x * f x) -
      (∑ x : Fin r → Bool,
        independentBinaryRMass ((oneCount : ℝ) / (parentCount : ℝ)) x * f x)| ≤
      (r : ℝ) ^ 2 / (parentCount : ℝ) := by
  have hrL : r ≤ parentCount := le_trans (Nat.le_self_pow (by omega) r) hL
  have hpos : 0 < parentCount := lt_of_lt_of_le (by omega) hrL
  have hLr : (0 : ℝ) < (parentCount : ℝ) := by exact_mod_cast hpos
  have hD := descFactorial_pos_cast (parentCount := parentCount) (r := r) hrL
  have hqzero : (0 : ℝ) ≤ (oneCount : ℝ) / (parentCount : ℝ) := by positivity
  have hqone : (oneCount : ℝ) / (parentCount : ℝ) ≤ 1 := by
    rw [div_le_one hLr]
    exact_mod_cast hones
  have hc : (1 : ℝ) ≤
      (parentCount : ℝ) ^ r / ((parentCount.descFactorial r : ℕ) : ℝ) := by
    rw [le_div_iff₀ hD, one_mul]
    exact_mod_cast Nat.descFactorial_le_pow parentCount r
  have habs := abs_expectation_sub_le_of_dominated
    (withoutReplacementBinaryRMass r parentCount oneCount)
    (independentBinaryRMass ((oneCount : ℝ) / (parentCount : ℝ)))
    ((parentCount : ℝ) ^ r / ((parentCount.descFactorial r : ℕ) : ℝ)) f
    (withoutReplacementBinaryRMass_nonneg r parentCount oneCount)
    (fun x => independentBinaryRMass_nonneg hqzero hqone x)
    (withoutReplacementBinaryRMass_sum hrL hones)
    (independentBinaryRMass_sum r _)
    (fun x => withoutReplacementBinaryRMass_le hrL hpos hones x)
    hf hf' hc
  exact habs.trans (domination_constant_le hr hL)

/-! ## §4 The per-coordinate ledger inequality, `r`-generic -/

/-- The without-replacement correction, in bits: the `r`-generic shape of
`Kernel3.worCorrection` with `4/L` replaced by `r²/L`. -/
noncomputable def worCorrectionR (r parentCount : ℕ) (lam : ℝ) : ℝ :=
  (r : ℝ) ^ 2 / (parentCount : ℝ) + lam * ((r : ℝ) ^ 2 / (parentCount : ℝ)) +
    binaryEntropy ((r : ℝ) ^ 2 / (parentCount : ℝ)) / 2

/-- **The `r`-generic per-coordinate ledger inequality.**  `E` is the empirical
(without-replacement) average conditional entropy at one coordinate, `τ` the
empirical average disagreement, `childMean` the empirical mean of the child
layer.  All arity-specific analysis is confined to `hbound`. -/
theorem ledger_inequality {r : ℕ} (hr : 0 < r) {A lam : ℝ} (hlam : 0 ≤ lam)
    (hbound : TypeEntropyBound r A lam) (parentCount : ℕ)
    (kernel : BinaryRKernel r) (E τ childMean : ℝ)
    (hchildMean : 0 ≤ childMean) (hchildMean' : childMean ≤ 1)
    (hE : E - kernel.conditionalEntropy ≤ (r : ℝ) ^ 2 / (parentCount : ℝ))
    (hτ : kernel.averageDisagreement - τ ≤ (r : ℝ) ^ 2 / (parentCount : ℝ))
    (_ : |childMean - kernel.childMarginal| ≤ 1 / 2)
    (hchild' : binaryEntropy |childMean - kernel.childMarginal| ≤
      binaryEntropy ((r : ℝ) ^ 2 / (parentCount : ℝ))) :
    E ≤ A + lam * τ +
        (binaryEntropy childMean -
          binaryEntropy kernel.parentProbability) / 2 +
      worCorrectionR r parentCount lam := by
  have hkernel := BinaryRKernel.conditionalEntropy_bound hr hbound kernel
  have hcont := abs_binaryEntropy_sub_le_binaryEntropy_abs_sub
    childMean kernel.childMarginal hchildMean hchildMean'
    kernel.childMarginal_nonneg kernel.childMarginal_le_one
  have hcont' : binaryEntropy kernel.childMarginal - binaryEntropy childMean ≤
      binaryEntropy ((r : ℝ) ^ 2 / (parentCount : ℝ)) := by
    have := (abs_le.mp hcont).1
    linarith [hchild']
  have hlamτ : lam * kernel.averageDisagreement ≤
      lam * (τ + (r : ℝ) ^ 2 / (parentCount : ℝ)) :=
    mul_le_mul_of_nonneg_left (by linarith) hlam
  unfold worCorrectionR
  nlinarith [hkernel, hE, hcont', hlamτ]

end RGenericKernel
