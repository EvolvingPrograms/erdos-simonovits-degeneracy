import Entropy3

/-!
# The `r = 3` kernel bridge (`BinaryTripleKernel`)

Port of the `BinaryPairKernel` development of `CompactnessAndDegeneracy.lean`
(namespace `TwoDegenerateGraphs`, lines 9963–10442 for the kernel proper and
10444–10800 for the without-replacement layer) from `r = 2` to `r = 3`.

The published `r = 2` file states its entropy lemma directly for a kernel
`Bool → Bool → ℝ` over *ordered* parent pairs.  `scratchpad/Entropy3.lean`
states the `r = 3` lemma (`ThreeDegenerateGraphs.conditional_entropy_bound`)
for the four *type*-conditional numbers `pⱼ = P(Z = 1 | X₁+X₂+X₃ = j)`.
This file supplies the missing reduction:

* `binEntropy_avg_three` — Jensen for `Real.binEntropy` at three points;
* `conditional_entropy_bound_ordered` — the eight-outcome (ordered-triple)
  form of `conditional_entropy_bound`, obtained from it by averaging the three
  outcomes of each type (concavity of `h`; the marginal `v` and the average
  disagreement `d` are *linear* in the eight numbers, so they are unchanged);
* `BinaryTripleKernel` and `BinaryTripleKernel.conditionalEntropy_bound` —
  the same statement packaged exactly like the published `r = 2` one, with the
  boundary cases `v ∈ {0,1}` removed by smoothing plus continuity.

Then the without-replacement layer and the per-coordinate ledger inequality.

Everything named `*Triple*` is the analogue of the published `*Pair*`.

**Checking.** `Entropy3.olean` is not part of the `lake` library, so build it
first and put `scratchpad` on `LEAN_PATH`:

```
cd proofs
lake env lean -o scratchpad/Entropy3.olean scratchpad/Entropy3.lean
lake env sh -c 'LEAN_PATH="$LEAN_PATH:$PWD/scratchpad" lean scratchpad/Kernel3.lean'
```
-/

namespace ThreeDegenerateGraphs

open TwoDegenerateGraphs

/-! ## Jensen for the binary entropy at three points -/

/-- Concavity of `h` at three points with equal weights.  This is the only
information-theoretic content of the reduction from ordered parent triples to
the four type-conditional probabilities. -/
theorem binEntropy_avg_three (x y z : ℝ)
    (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1)
    (hz : 0 ≤ z) (hz' : z ≤ 1) :
    Real.binEntropy x + Real.binEntropy y + Real.binEntropy z ≤
      3 * Real.binEntropy ((x + y + z) / 3) := by
  have hconcave : ConcaveOn ℝ (Set.Icc (0 : ℝ) 1) Real.binEntropy :=
    Real.strictConcave_binEntropy.concaveOn
  have hmem : ∀ i ∈ (Finset.univ : Finset (Fin 3)),
      (![x, y, z] : Fin 3 → ℝ) i ∈ Set.Icc (0 : ℝ) 1 := by
    intro i _
    fin_cases i <;> exact ⟨by assumption, by assumption⟩
  have hsum := hconcave.le_map_sum
    (t := (Finset.univ : Finset (Fin 3))) (w := fun _ => (1 / 3 : ℝ))
    (p := ![x, y, z]) (by intro i _; norm_num) (by norm_num) hmem
  simp only [Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.head_cons, Matrix.cons_val_two, Matrix.tail_cons, smul_eq_mul] at hsum
  have harg : (1 / 3 : ℝ) * x + 1 / 3 * y + 1 / 3 * z = (x + y + z) / 3 := by ring
  rw [harg] at hsum
  linarith

/-! ## The eight-outcome (ordered) entropy bound

`z_{abc} = P(Z = 1 | X₁ = a, X₂ = b, X₃ = c)` for an arbitrary joint law with
`X₁,X₂,X₃` i.i.d. Bernoulli(`q`).  Nothing is assumed about exchangeability:
the reduction to the four type numbers is Jensen. -/

/-- **The kernel bridge, raw form.**  The `r = 3` conditional-entropy bound for
an arbitrary (not necessarily exchangeable) child law over ordered parent
triples.  `v` is the child marginal, `d = ⅓ Σₐ P(Xₐ ≠ Z)`. -/
theorem conditional_entropy_bound_ordered
    (q v d z₀ z₁ z₂ z₃ z₄ z₅ z₆ z₇ : ℝ)
    (hqzero : 0 ≤ q) (hqone : q ≤ 1)
    (hvzero : 0 < v) (hvone : v < 1)
    (h₀ : 0 ≤ z₀) (h₀' : z₀ ≤ 1) (h₁ : 0 ≤ z₁) (h₁' : z₁ ≤ 1)
    (h₂ : 0 ≤ z₂) (h₂' : z₂ ≤ 1) (h₃ : 0 ≤ z₃) (h₃' : z₃ ≤ 1)
    (h₄ : 0 ≤ z₄) (h₄' : z₄ ≤ 1) (h₅ : 0 ≤ z₅) (h₅' : z₅ ≤ 1)
    (h₆ : 0 ≤ z₆) (h₆' : z₆ ≤ 1) (h₇ : 0 ≤ z₇) (h₇' : z₇ ≤ 1)
    (hv : v = (1 - q) ^ 3 * z₀ +
            q * (1 - q) ^ 2 * (z₁ + z₂ + z₃) +
            q ^ 2 * (1 - q) * (z₄ + z₅ + z₆) + q ^ 3 * z₇)
    (hd : 3 * d = (1 - q) ^ 3 * (3 * z₀) +
            q * (1 - q) ^ 2 * ((1 + z₁) + (1 + z₂) + (1 + z₃)) +
            q ^ 2 * (1 - q) * ((2 - z₄) + (2 - z₅) + (2 - z₆)) +
            q ^ 3 * (3 * (1 - z₇))) :
    (1 - q) ^ 3 * Real.binEntropy z₀ +
        q * (1 - q) ^ 2 *
          (Real.binEntropy z₁ + Real.binEntropy z₂ + Real.binEntropy z₃) +
        q ^ 2 * (1 - q) *
          (Real.binEntropy z₄ + Real.binEntropy z₅ + Real.binEntropy z₆) +
        q ^ 3 * Real.binEntropy z₇ ≤
      (17 / 80 : ℝ) * Real.log 2 + (7 / 4 : ℝ) * Real.log 2 * d +
        (Real.binEntropy v - Real.binEntropy q) / 2 := by
  have hc : (0 : ℝ) ≤ 1 - q := by linarith
  set p₀ : ℝ := z₀ with hp₀def
  set p₁ : ℝ := (z₁ + z₂ + z₃) / 3 with hp₁def
  set p₂ : ℝ := (z₄ + z₅ + z₆) / 3 with hp₂def
  set p₃ : ℝ := z₇ with hp₃def
  have hp₁ : 0 ≤ p₁ := by rw [hp₁def]; linarith
  have hp₁' : p₁ ≤ 1 := by rw [hp₁def]; linarith
  have hp₂ : 0 ≤ p₂ := by rw [hp₂def]; linarith
  have hp₂' : p₂ ≤ 1 := by rw [hp₂def]; linarith
  -- the type-level hypotheses are literally the same linear identities
  have hv' : v = (1 - q) ^ 3 * p₀ + 3 * q * (1 - q) ^ 2 * p₁ +
      3 * q ^ 2 * (1 - q) * p₂ + q ^ 3 * p₃ := by
    rw [hp₀def, hp₁def, hp₂def, hp₃def]; rw [hv]; ring
  have hd' : 3 * d = (1 - q) ^ 3 * (3 * p₀) +
      3 * q * (1 - q) ^ 2 * ((1 - p₁) + 2 * p₁) +
      3 * q ^ 2 * (1 - q) * (2 * (1 - p₂) + p₂) +
      q ^ 3 * (3 * (1 - p₃)) := by
    rw [hp₀def, hp₁def, hp₂def, hp₃def]; rw [hd]; ring
  have hmain := conditional_entropy_bound q v d p₀ p₁ p₂ p₃
    hqzero hqone hvzero hvone h₀ h₀' hp₁ hp₁' hp₂ hp₂' h₇ h₇' hv' hd'
  -- Jensen closes the gap between the ordered and the type-level left sides
  have j₁ := binEntropy_avg_three z₁ z₂ z₃ h₁ h₁' h₂ h₂' h₃ h₃'
  have j₂ := binEntropy_avg_three z₄ z₅ z₆ h₄ h₄' h₅ h₅' h₆ h₆'
  have w1 : (0 : ℝ) ≤ q * (1 - q) ^ 2 := by positivity
  have w2 : (0 : ℝ) ≤ q ^ 2 * (1 - q) := by positivity
  have m1 := mul_le_mul_of_nonneg_left j₁ w1
  have m2 := mul_le_mul_of_nonneg_left j₂ w2
  rw [← hp₁def] at m1
  rw [← hp₂def] at m2
  linarith

/-! ## The kernel

Exact analogue of `TwoDegenerateGraphs.BinaryPairKernel`: a parent bias `q`
together with an arbitrary conditional child law over ordered parent triples. -/

/-- Analogue of `TwoDegenerateGraphs.independentBinaryPairMass`. -/
def independentBinaryTripleMass (q : ℝ) (left middle right : Bool) : ℝ :=
  binaryCoinMass q left * binaryCoinMass q middle * binaryCoinMass q right

theorem independentBinaryTripleMass_nonneg {q : ℝ}
    (hqzero : 0 ≤ q) (hqone : q ≤ 1) (left middle right : Bool) :
    0 ≤ independentBinaryTripleMass q left middle right :=
  mul_nonneg
    (mul_nonneg (binaryCoinMass_nonneg hqzero hqone left)
      (binaryCoinMass_nonneg hqzero hqone middle))
    (binaryCoinMass_nonneg hqzero hqone right)

theorem independentBinaryTripleMass_sum (q : ℝ) :
    (∑ left : Bool, ∑ middle : Bool, ∑ right : Bool,
      independentBinaryTripleMass q left middle right) = 1 := by
  simp [Fintype.univ_bool, independentBinaryTripleMass, binaryCoinMass]
  ring

/-- Analogue of `TwoDegenerateGraphs.BinaryPairKernel`. -/
structure BinaryTripleKernel where
  parentProbability : ℝ
  parentProbability_nonneg : 0 ≤ parentProbability
  parentProbability_le_one : parentProbability ≤ 1
  childProbability : Bool → Bool → Bool → ℝ
  childProbability_nonneg : ∀ l m r, 0 ≤ childProbability l m r
  childProbability_le_one : ∀ l m r, childProbability l m r ≤ 1

namespace BinaryTripleKernel

noncomputable def childMarginal (kernel : BinaryTripleKernel) : ℝ :=
  ∑ l : Bool, ∑ m : Bool, ∑ r : Bool,
    independentBinaryTripleMass kernel.parentProbability l m r *
      kernel.childProbability l m r

/-- `H(Z | X₁X₂X₃)` in **bits**. -/
noncomputable def conditionalEntropy (kernel : BinaryTripleKernel) : ℝ :=
  ∑ l : Bool, ∑ m : Bool, ∑ r : Bool,
    independentBinaryTripleMass kernel.parentProbability l m r *
      binaryEntropy (kernel.childProbability l m r)

/-- `d = ⅓ Σₐ P(Xₐ ≠ Z)`. -/
noncomputable def averageDisagreement (kernel : BinaryTripleKernel) : ℝ :=
  ∑ l : Bool, ∑ m : Bool, ∑ r : Bool,
    independentBinaryTripleMass kernel.parentProbability l m r *
      ((BinaryPairKernel.bitDisagreementProbability l
            (kernel.childProbability l m r) +
          BinaryPairKernel.bitDisagreementProbability m
            (kernel.childProbability l m r) +
          BinaryPairKernel.bitDisagreementProbability r
            (kernel.childProbability l m r)) / 3)

theorem childMarginal_nonneg (kernel : BinaryTripleKernel) :
    0 ≤ kernel.childMarginal := by
  unfold childMarginal
  refine Finset.sum_nonneg fun l _ => Finset.sum_nonneg fun m _ =>
    Finset.sum_nonneg fun r _ => mul_nonneg ?_ (kernel.childProbability_nonneg l m r)
  exact independentBinaryTripleMass_nonneg
    kernel.parentProbability_nonneg kernel.parentProbability_le_one l m r

theorem childMarginal_le_one (kernel : BinaryTripleKernel) :
    kernel.childMarginal ≤ 1 := by
  unfold childMarginal
  calc
    (∑ l : Bool, ∑ m : Bool, ∑ r : Bool,
        independentBinaryTripleMass kernel.parentProbability l m r *
          kernel.childProbability l m r) ≤
      ∑ l : Bool, ∑ m : Bool, ∑ r : Bool,
        independentBinaryTripleMass kernel.parentProbability l m r * 1 := by
          refine Finset.sum_le_sum fun l _ => Finset.sum_le_sum fun m _ =>
            Finset.sum_le_sum fun r _ => ?_
          exact mul_le_mul_of_nonneg_left (kernel.childProbability_le_one l m r)
            (independentBinaryTripleMass_nonneg
              kernel.parentProbability_nonneg kernel.parentProbability_le_one l m r)
    _ = 1 := by simpa using independentBinaryTripleMass_sum kernel.parentProbability

/-- The eight ordered outcomes, grouped by type. -/
theorem childMarginal_eq_eight_outcomes (kernel : BinaryTripleKernel) :
    kernel.childMarginal =
      (1 - kernel.parentProbability) ^ 3 *
          kernel.childProbability false false false +
        kernel.parentProbability * (1 - kernel.parentProbability) ^ 2 *
          (kernel.childProbability true false false +
            kernel.childProbability false true false +
            kernel.childProbability false false true) +
        kernel.parentProbability ^ 2 * (1 - kernel.parentProbability) *
          (kernel.childProbability false true true +
            kernel.childProbability true false true +
            kernel.childProbability true true false) +
        kernel.parentProbability ^ 3 *
          kernel.childProbability true true true := by
  simp [childMarginal, Fintype.univ_bool,
    independentBinaryTripleMass, binaryCoinMass]
  ring

theorem conditionalEntropy_mul_log_two (kernel : BinaryTripleKernel) :
    kernel.conditionalEntropy * Real.log 2 =
      (1 - kernel.parentProbability) ^ 3 *
          Real.binEntropy (kernel.childProbability false false false) +
        kernel.parentProbability * (1 - kernel.parentProbability) ^ 2 *
          (Real.binEntropy (kernel.childProbability true false false) +
            Real.binEntropy (kernel.childProbability false true false) +
            Real.binEntropy (kernel.childProbability false false true)) +
        kernel.parentProbability ^ 2 * (1 - kernel.parentProbability) *
          (Real.binEntropy (kernel.childProbability false true true) +
            Real.binEntropy (kernel.childProbability true false true) +
            Real.binEntropy (kernel.childProbability true true false)) +
        kernel.parentProbability ^ 3 *
          Real.binEntropy (kernel.childProbability true true true) := by
  simp [conditionalEntropy, Fintype.univ_bool,
    independentBinaryTripleMass, binaryCoinMass, binaryEntropy]
  field_simp [log_two_pos.ne']
  ring

theorem averageDisagreement_eq_eight_outcomes (kernel : BinaryTripleKernel) :
    3 * kernel.averageDisagreement =
      (1 - kernel.parentProbability) ^ 3 *
          (3 * kernel.childProbability false false false) +
        kernel.parentProbability * (1 - kernel.parentProbability) ^ 2 *
          ((1 + kernel.childProbability true false false) +
            (1 + kernel.childProbability false true false) +
            (1 + kernel.childProbability false false true)) +
        kernel.parentProbability ^ 2 * (1 - kernel.parentProbability) *
          ((2 - kernel.childProbability false true true) +
            (2 - kernel.childProbability true false true) +
            (2 - kernel.childProbability true true false)) +
        kernel.parentProbability ^ 3 *
          (3 * (1 - kernel.childProbability true true true)) := by
  simp [averageDisagreement, Fintype.univ_bool,
    independentBinaryTripleMass, binaryCoinMass,
    BinaryPairKernel.bitDisagreementProbability]
  ring

/-- **The `r = 3` kernel bound, interior case.**  Analogue of
`TwoDegenerateGraphs.BinaryPairKernel.conditionalEntropy_bound_of_marginal_interior`.
Constants in base 2: `A₀ = 17/80`, `λ = 7/4`, `α = 1/2`. -/
theorem conditionalEntropy_bound_of_marginal_interior
    (kernel : BinaryTripleKernel)
    (hmarginal_zero : 0 < kernel.childMarginal)
    (hmarginal_one : kernel.childMarginal < 1) :
    kernel.conditionalEntropy ≤
      (17 / 80 : ℝ) + (7 / 4 : ℝ) * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2 := by
  have hordered := conditional_entropy_bound_ordered
    kernel.parentProbability kernel.childMarginal kernel.averageDisagreement
    (kernel.childProbability false false false)
    (kernel.childProbability true false false)
    (kernel.childProbability false true false)
    (kernel.childProbability false false true)
    (kernel.childProbability false true true)
    (kernel.childProbability true false true)
    (kernel.childProbability true true false)
    (kernel.childProbability true true true)
    kernel.parentProbability_nonneg kernel.parentProbability_le_one
    hmarginal_zero hmarginal_one
    (kernel.childProbability_nonneg _ _ _) (kernel.childProbability_le_one _ _ _)
    (kernel.childProbability_nonneg _ _ _) (kernel.childProbability_le_one _ _ _)
    (kernel.childProbability_nonneg _ _ _) (kernel.childProbability_le_one _ _ _)
    (kernel.childProbability_nonneg _ _ _) (kernel.childProbability_le_one _ _ _)
    (kernel.childProbability_nonneg _ _ _) (kernel.childProbability_le_one _ _ _)
    (kernel.childProbability_nonneg _ _ _) (kernel.childProbability_le_one _ _ _)
    (kernel.childProbability_nonneg _ _ _) (kernel.childProbability_le_one _ _ _)
    (kernel.childProbability_nonneg _ _ _) (kernel.childProbability_le_one _ _ _)
    (childMarginal_eq_eight_outcomes kernel)
    (averageDisagreement_eq_eight_outcomes kernel)
  rw [← conditionalEntropy_mul_log_two kernel] at hordered
  have hright :
      ((17 / 80 : ℝ) + (7 / 4 : ℝ) * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2) * Real.log 2 =
        (17 / 80 : ℝ) * Real.log 2 +
          (7 / 4 : ℝ) * Real.log 2 * kernel.averageDisagreement +
          (Real.binEntropy kernel.childMarginal -
            Real.binEntropy kernel.parentProbability) / 2 := by
    unfold binaryEntropy
    field_simp [log_two_pos.ne']
  refine (mul_le_mul_iff_of_pos_right log_two_pos).mp ?_
  rw [hright]
  linarith

/-! ### Boundary cases `v ∈ {0, 1}` by smoothing

Verbatim port of the `r = 2` `smoothed` / continuity argument. -/

noncomputable def smoothed (kernel : BinaryTripleKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing)
    (hmixing_one : mixing ≤ 1) : BinaryTripleKernel where
  parentProbability := kernel.parentProbability
  parentProbability_nonneg := kernel.parentProbability_nonneg
  parentProbability_le_one := kernel.parentProbability_le_one
  childProbability l m r := (1 - mixing) * kernel.childProbability l m r + mixing / 2
  childProbability_nonneg := by
    intro l m r
    exact add_nonneg
      (mul_nonneg (sub_nonneg.mpr hmixing_one) (kernel.childProbability_nonneg l m r))
      (div_nonneg hmixing_zero (by norm_num))
  childProbability_le_one := by
    intro l m r
    have hproduct := mul_le_mul_of_nonneg_left
      (kernel.childProbability_le_one l m r) (sub_nonneg.mpr hmixing_one)
    nlinarith

theorem smoothed_childMarginal (kernel : BinaryTripleKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing) (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).childMarginal =
      (1 - mixing) * kernel.childMarginal + mixing / 2 := by
  rw [childMarginal_eq_eight_outcomes, childMarginal_eq_eight_outcomes kernel]
  simp only [smoothed]
  ring

theorem smoothed_averageDisagreement (kernel : BinaryTripleKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing) (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).averageDisagreement =
      (1 - mixing) * kernel.averageDisagreement + mixing / 2 := by
  have h := averageDisagreement_eq_eight_outcomes
    (smoothed kernel mixing hmixing_zero hmixing_one)
  have hk := averageDisagreement_eq_eight_outcomes kernel
  have hp : (smoothed kernel mixing hmixing_zero hmixing_one).parentProbability
      = kernel.parentProbability := rfl
  have hcp : ∀ l m r,
      (smoothed kernel mixing hmixing_zero hmixing_one).childProbability l m r
        = (1 - mixing) * kernel.childProbability l m r + mixing / 2 :=
    fun _ _ _ => rfl
  rw [hp] at h
  simp only [hcp] at h
  linear_combination (h - (1 - mixing) * hk) / 3

noncomputable def smoothedConditionalEntropy
    (kernel : BinaryTripleKernel) (mixing : ℝ) : ℝ :=
  ∑ l : Bool, ∑ m : Bool, ∑ r : Bool,
    independentBinaryTripleMass kernel.parentProbability l m r *
      binaryEntropy ((1 - mixing) * kernel.childProbability l m r + mixing / 2)

theorem smoothedConditionalEntropy_continuous (kernel : BinaryTripleKernel) :
    Continuous (smoothedConditionalEntropy kernel) := by
  unfold smoothedConditionalEntropy
  fun_prop

theorem smoothed_conditionalEntropy (kernel : BinaryTripleKernel)
    (mixing : ℝ) (hmixing_zero : 0 ≤ mixing) (hmixing_one : mixing ≤ 1) :
    (smoothed kernel mixing hmixing_zero hmixing_one).conditionalEntropy =
      smoothedConditionalEntropy kernel mixing := rfl

/-- **The `r = 3` kernel bound.**  Analogue of
`TwoDegenerateGraphs.BinaryPairKernel.conditionalEntropy_bound`; no interiority
hypothesis on the child marginal. -/
theorem conditionalEntropy_bound (kernel : BinaryTripleKernel) :
    kernel.conditionalEntropy ≤
      (17 / 80 : ℝ) + (7 / 4 : ℝ) * kernel.averageDisagreement +
        (binaryEntropy kernel.childMarginal -
          binaryEntropy kernel.parentProbability) / 2 := by
  let mixing : ℕ → ℝ := fun n => 1 / ((n : ℝ) + 1)
  have hmixing_pos (n : ℕ) : 0 < mixing n := by dsimp [mixing]; positivity
  have hmixing_le_one (n : ℕ) : mixing n ≤ 1 := by
    dsimp [mixing]
    refine (div_le_one (by positivity)).mpr ?_
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  let approximation : ℕ → BinaryTripleKernel := fun n =>
    smoothed kernel (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hmixing_tendsto : Filter.Tendsto mixing Filter.atTop (nhds 0) := by
    simpa [mixing] using (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ))
  have hmarginal_zero (n : ℕ) : 0 < (approximation n).childMarginal := by
    have hformula := smoothed_childMarginal kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
    change 0 < (smoothed kernel (mixing n)
      (hmixing_pos n).le (hmixing_le_one n)).childMarginal
    rw [hformula]
    have h1 := mul_nonneg (sub_nonneg.mpr (hmixing_le_one n)) (childMarginal_nonneg kernel)
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
    exact smoothed_childMarginal kernel (mixing n) (hmixing_pos n).le (hmixing_le_one n)
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
    exact smoothed_averageDisagreement kernel
      (mixing n) (hmixing_pos n).le (hmixing_le_one n)
  have hchildentropy_tendsto :=
    binaryEntropy_continuous.continuousAt.tendsto.comp hmarginal_tendsto
  have hparent (n : ℕ) :
      (approximation n).parentProbability = kernel.parentProbability := rfl
  have hright_tendsto :
      Filter.Tendsto
        (fun n =>
          (17 / 80 : ℝ) + (7 / 4 : ℝ) * (approximation n).averageDisagreement +
            (binaryEntropy (approximation n).childMarginal -
              binaryEntropy (approximation n).parentProbability) / 2)
        Filter.atTop
        (nhds
          ((17 / 80 : ℝ) + (7 / 4 : ℝ) * kernel.averageDisagreement +
            (binaryEntropy kernel.childMarginal -
              binaryEntropy kernel.parentProbability) / 2)) := by
    simp_rw [hparent]
    have hd := (tendsto_const_nhds (x := (7 / 4 : ℝ))).mul hdisagreement_tendsto
    have he := (hchildentropy_tendsto.sub
      (tendsto_const_nhds (x := binaryEntropy kernel.parentProbability))).div_const 2
    have hsum := (tendsto_const_nhds (x := (17 / 80 : ℝ))).add (hd.add he)
    simpa [add_assoc] using hsum
  refine le_of_tendsto_of_tendsto' hconditional_tendsto hright_tendsto ?_
  intro n
  exact conditionalEntropy_bound_of_marginal_interior
    (approximation n) (hmarginal_zero n) (hmarginal_one n)

end BinaryTripleKernel

/-! ## Balancedness of the 3-subset design

Each element of `Fin L` lies in exactly `C(L-1, 2)` of the 3-element subsets.
Consequently the parent index seen at a uniformly chosen (child, slot) pair is
*uniform* on `Fin L`, so the parent bias `q` that the entropy lemma is applied
with is **exactly** the empirical mean of the parent layer — no approximation
enters at this step.  (The residual approximation is the without-replacement
correction of the next section: within one child the three slots are distinct,
which is not i.i.d. sampling.) -/

open Finset in
/-- **The balancedness fact.**  A fixed index lies in exactly `C(L-1,2)` of the
3-element subsets of `Fin L`. -/
theorem card_threeSubsets_containing {L : ℕ} (a : Fin L) :
    (((univ : Finset (Fin L)).powersetCard 3).filter (fun S => a ∈ S)).card
      = (L - 1).choose 2 := by
  have hcard : ((univ : Finset (Fin L)).erase a).card = L - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ,
      Fintype.card_fin]
  have hbij :
      (((univ : Finset (Fin L)).powersetCard 3).filter (fun S => a ∈ S)).card
        = (((univ : Finset (Fin L)).erase a).powersetCard 2).card := by
    refine Finset.card_bij' (fun S _ => S.erase a) (fun T _ => insert a T)
      ?_ ?_ ?_ ?_
    · intro S hS
      simp only [Finset.mem_filter, Finset.mem_powersetCard] at hS
      obtain ⟨⟨-, hS3⟩, ha⟩ := hS
      refine Finset.mem_powersetCard.mpr ⟨?_, ?_⟩
      · intro y hy
        exact Finset.mem_erase.mpr ⟨(Finset.mem_erase.mp hy).1, Finset.mem_univ y⟩
      · rw [Finset.card_erase_of_mem ha, hS3]
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      obtain ⟨hTsub, hT2⟩ := hT
      have haT : a ∉ T := fun h => (Finset.mem_erase.mp (hTsub h)).1 rfl
      simp only [Finset.mem_filter, Finset.mem_powersetCard]
      exact ⟨⟨Finset.subset_univ _, by rw [Finset.card_insert_of_notMem haT, hT2]⟩,
        Finset.mem_insert_self a T⟩
    · intro S hS
      simp only [Finset.mem_filter] at hS
      exact Finset.insert_erase hS.2
    · intro T hT
      simp only [Finset.mem_powersetCard] at hT
      have haT : a ∉ T := fun h => (Finset.mem_erase.mp (hT.1 h)).1 rfl
      exact Finset.erase_insert haT
  rw [hbij, Finset.card_powersetCard, hcard]

open Finset in
/-- Double counting over the 3-subset design: summing any weight over all
(child, slot) pairs is `C(L-1,2)` times summing it over the parent layer. -/
theorem sum_threeSubsets_slots {L : ℕ} (f : Fin L → ℝ) :
    ∑ S ∈ (univ : Finset (Fin L)).powersetCard 3, ∑ a ∈ S, f a
      = ((L - 1).choose 2 : ℝ) * ∑ a : Fin L, f a := by
  have hswap :
      ∑ S ∈ (univ : Finset (Fin L)).powersetCard 3, ∑ a ∈ S, f a
        = ∑ a : Fin L,
            ∑ S ∈ (univ : Finset (Fin L)).powersetCard 3,
              (if a ∈ S then f a else 0) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun S _ => ?_
    rw [Finset.sum_ite_mem, Finset.univ_inter]
  rw [hswap, Finset.mul_sum]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← Finset.sum_filter, Finset.sum_const,
    card_threeSubsets_containing a, nsmul_eq_mul]

/-- `L · C(L-1,2) = 3 · C(L,3)`: the design has `C(L,3)` children, each with 3
slots, and the resulting index distribution is uniform on `Fin L`. -/
theorem card_slots_identity {L : ℕ} (hL : 1 ≤ L) :
    L * (L - 1).choose 2 = 3 * L.choose 3 := by
  obtain ⟨n, rfl⟩ : ∃ n, L = n + 1 := ⟨L - 1, by omega⟩
  simpa [Nat.mul_comm] using (Nat.add_one_mul_choose_eq n 2)

open Finset in
/-- **The parent bias seen by the children is exactly the empirical mean.**
`x` is the parent bit array at one coordinate; the left-hand side is the
probability that a uniformly chosen (3-subset, slot) pair points at a `1`. -/
theorem threeSubset_slot_marginal {L : ℕ} (hL : 3 ≤ L) (x : Fin L → Bool) :
    (∑ S ∈ (univ : Finset (Fin L)).powersetCard 3,
        ∑ a ∈ S, (if x a then (1 : ℝ) else 0))
      = (3 * (L.choose 3 : ℝ) / (L : ℝ)) *
          ((univ.filter fun a => x a).card : ℝ) := by
  have hLpos : (0 : ℝ) < (L : ℝ) := by
    have : 0 < L := by omega
    exact_mod_cast this
  have hcount :
      ∑ a : Fin L, (if x a then (1 : ℝ) else 0)
        = ((univ.filter fun a => x a).card : ℝ) := by
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul, mul_one]
  have hid : (L : ℝ) * ((L - 1).choose 2 : ℝ) = 3 * (L.choose 3 : ℝ) := by
    exact_mod_cast congrArg (Nat.cast : ℕ → ℝ) (card_slots_identity (by omega))
  rw [sum_threeSubsets_slots, hcount]
  have : ((L - 1).choose 2 : ℝ) = 3 * (L.choose 3 : ℝ) / (L : ℝ) := by
    field_simp
    linarith [hid]
  rw [this]

/-! ## Sampling three *distinct* parents

Analogue of `withoutReplacementBinaryPairMass` and
`withoutReplacementBinaryPairExpectation_error`.  Within one child the three
parent slots carry distinct indices, so the parent triple is drawn *without*
replacement from the layer; the entropy lemma is proved for i.i.d. parents.
The published `r = 2` file quantifies the discrepancy as an absolute error
`1 / L` on every `[0,1]`-valued observable; we prove the `r = 3` analogue with
`4 / L` (the exact constant is `(3L-2)/((L-1)(L-2))`). -/

/-- A generic domination bound: if `m₁ ≤ c · m₂` pointwise and both are
probability masses, then their expectations of any `[0,1]`-valued observable
differ by at most `c - 1`.  (This is the total-variation/coupling step: `c - 1`
is the union bound on a collision among the three sampled indices.) -/
theorem expectation_le_of_dominated {ι : Type*} [Fintype ι]
    (m₁ m₂ : ι → ℝ) (c : ℝ) (f : ι → ℝ)
    (hm₂ : ∀ i, 0 ≤ m₂ i) (hs₂ : ∑ i, m₂ i = 1)
    (hdom : ∀ i, m₁ i ≤ c * m₂ i)
    (hf : ∀ i, 0 ≤ f i) (hf' : ∀ i, f i ≤ 1) (hc : 1 ≤ c) :
    ∑ i, m₁ i * f i - ∑ i, m₂ i * f i ≤ c - 1 := by
  have hstep : ∀ i, m₁ i * f i - m₂ i * f i ≤ (c - 1) * m₂ i := by
    intro i
    have h1 : (m₁ i - m₂ i) * f i ≤ ((c - 1) * m₂ i) * f i := by
      have : m₁ i - m₂ i ≤ (c - 1) * m₂ i := by
        have := hdom i; linarith
      exact mul_le_mul_of_nonneg_right this (hf i)
    have h2 : ((c - 1) * m₂ i) * f i ≤ ((c - 1) * m₂ i) * 1 :=
      mul_le_mul_of_nonneg_left (hf' i)
        (mul_nonneg (by linarith) (hm₂ i))
    nlinarith [h1, h2]
  calc ∑ i, m₁ i * f i - ∑ i, m₂ i * f i
      = ∑ i, (m₁ i * f i - m₂ i * f i) := by rw [Finset.sum_sub_distrib]
    _ ≤ ∑ i, (c - 1) * m₂ i := Finset.sum_le_sum fun i _ => hstep i
    _ = c - 1 := by rw [← Finset.mul_sum, hs₂, mul_one]

/-- Two-sided form of `expectation_le_of_dominated`. -/
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

/-- The without-replacement mass of an ordered parent triple: `L = parentCount`
indices, `oneCount` of them carrying a `1`, sampled without replacement. -/
noncomputable def withoutReplacementBinaryTripleMass
    (parentCount oneCount : ℕ) (l m r : Bool) : ℝ :=
  empiricalBinaryOutcomeCount parentCount oneCount l *
      (empiricalBinaryOutcomeCount parentCount oneCount m -
        (if l = m then 1 else 0)) *
      (empiricalBinaryOutcomeCount parentCount oneCount r -
        (if l = r then 1 else 0) - (if m = r then 1 else 0)) /
    ((parentCount : ℝ) * ((parentCount : ℝ) - 1) * ((parentCount : ℝ) - 2))

section WithoutReplacement

variable {parentCount oneCount : ℕ}

private theorem descTwo_nonneg (hones : oneCount ≤ parentCount) :
    0 ≤ (oneCount : ℝ) * ((oneCount : ℝ) - 1) ∧
    0 ≤ ((parentCount : ℝ) - oneCount) * ((parentCount : ℝ) - oneCount - 1) := by
  constructor
  · rcases Nat.lt_or_ge oneCount 1 with h | h
    · interval_cases oneCount
      norm_num
    · have h1 : (1 : ℝ) ≤ (oneCount : ℝ) := by exact_mod_cast h
      exact mul_nonneg (by linarith) (by linarith)
  · rcases Nat.lt_or_ge (parentCount - oneCount) 1 with h | h
    · have heq : (parentCount : ℝ) - oneCount = 0 := by
        have : parentCount = oneCount := by omega
        simp [this]
      rw [heq]; norm_num
    · have h1 : (1 : ℝ) ≤ (parentCount : ℝ) - oneCount := by
        have hle : oneCount + 1 ≤ parentCount := by omega
        have : ((oneCount : ℝ) + 1) ≤ (parentCount : ℝ) := by exact_mod_cast hle
        linarith
      exact mul_nonneg (by linarith) (by linarith)

private theorem descThree_nonneg (hones : oneCount ≤ parentCount) :
    0 ≤ (oneCount : ℝ) * ((oneCount : ℝ) - 1) * ((oneCount : ℝ) - 2) ∧
    0 ≤ ((parentCount : ℝ) - oneCount) * ((parentCount : ℝ) - oneCount - 1) *
        ((parentCount : ℝ) - oneCount - 2) := by
  constructor
  · rcases Nat.lt_or_ge oneCount 2 with h | h
    · interval_cases oneCount <;> norm_num
    · have h2 : (2 : ℝ) ≤ (oneCount : ℝ) := by exact_mod_cast h
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)
  · rcases Nat.lt_or_ge (parentCount - oneCount) 2 with h | h
    · have hd : parentCount ≤ oneCount + 1 := by omega
      have hle : (parentCount : ℝ) - oneCount ≤ 1 := by
        have : (parentCount : ℝ) ≤ (oneCount : ℝ) + 1 := by exact_mod_cast hd
        linarith
      have hge : (0 : ℝ) ≤ (parentCount : ℝ) - oneCount := by
        have : (oneCount : ℝ) ≤ (parentCount : ℝ) := by exact_mod_cast hones
        linarith
      have hprod := mul_nonneg hge (mul_nonneg
        (show (0:ℝ) ≤ 1 - ((parentCount : ℝ) - oneCount) by linarith)
        (show (0:ℝ) ≤ 2 - ((parentCount : ℝ) - oneCount) by linarith))
      nlinarith [hprod]
    · have h2 : (2 : ℝ) ≤ (parentCount : ℝ) - oneCount := by
        have : oneCount + 2 ≤ parentCount := by omega
        have hc : ((oneCount : ℝ) + 2) ≤ (parentCount : ℝ) := by exact_mod_cast this
        linarith
      exact mul_nonneg (mul_nonneg (by linarith) (by linarith)) (by linarith)

theorem withoutReplacementBinaryTripleMass_sum
    (hparents : 3 ≤ parentCount) :
    (∑ l : Bool, ∑ m : Bool, ∑ r : Bool,
      withoutReplacementBinaryTripleMass parentCount oneCount l m r) = 1 := by
  have h3 : (3 : ℝ) ≤ (parentCount : ℝ) := by exact_mod_cast hparents
  have h0 : (parentCount : ℝ) ≠ 0 := by linarith
  have h1 : (parentCount : ℝ) - 1 ≠ 0 := by linarith
  have h2 : (parentCount : ℝ) - 2 ≠ 0 := by linarith
  simp [Fintype.univ_bool, withoutReplacementBinaryTripleMass,
    empiricalBinaryOutcomeCount]
  field_simp
  ring

/-- Domination of the without-replacement law by the i.i.d. law, with the
explicit constant `c = L³ / (L(L-1)(L-2))`. -/
theorem withoutReplacementBinaryTripleMass_le
    (hparents : 3 ≤ parentCount) (hones : oneCount ≤ parentCount)
    (l m r : Bool) :
    withoutReplacementBinaryTripleMass parentCount oneCount l m r ≤
      ((parentCount : ℝ) ^ 3 /
          ((parentCount : ℝ) * ((parentCount : ℝ) - 1) * ((parentCount : ℝ) - 2))) *
        independentBinaryTripleMass ((oneCount : ℝ) / (parentCount : ℝ)) l m r := by
  have h3 : (3 : ℝ) ≤ (parentCount : ℝ) := by exact_mod_cast hparents
  have hD : 0 < (parentCount : ℝ) * ((parentCount : ℝ) - 1) * ((parentCount : ℝ) - 2) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  have hk : (0 : ℝ) ≤ (oneCount : ℝ) := by positivity
  have hnk : (0 : ℝ) ≤ (parentCount : ℝ) - oneCount := by
    have : (oneCount : ℝ) ≤ (parentCount : ℝ) := by exact_mod_cast hones
    linarith
  obtain ⟨d2k, d2n⟩ := descTwo_nonneg (parentCount := parentCount) (oneCount := oneCount) hones
  obtain ⟨d3k, d3n⟩ := descThree_nonneg (parentCount := parentCount) (oneCount := oneCount) hones
  have hrhs :
      ((parentCount : ℝ) ^ 3 /
          ((parentCount : ℝ) * ((parentCount : ℝ) - 1) * ((parentCount : ℝ) - 2))) *
        independentBinaryTripleMass ((oneCount : ℝ) / (parentCount : ℝ)) l m r
      = (empiricalBinaryOutcomeCount parentCount oneCount l *
          empiricalBinaryOutcomeCount parentCount oneCount m *
          empiricalBinaryOutcomeCount parentCount oneCount r) /
        ((parentCount : ℝ) * ((parentCount : ℝ) - 1) * ((parentCount : ℝ) - 2)) := by
    have hne : (parentCount : ℝ) ≠ 0 := by linarith
    cases l <;> cases m <;> cases r <;>
      simp [independentBinaryTripleMass, binaryCoinMass,
        empiricalBinaryOutcomeCount] <;> field_simp
  rw [hrhs, withoutReplacementBinaryTripleMass]
  refine div_le_div_of_nonneg_right ?_ hD.le
  cases l <;> cases m <;> cases r <;>
    simp [empiricalBinaryOutcomeCount] <;> nlinarith [hk, hnk, d2k, d2n, d3k, d3n]

end WithoutReplacement

/-! ## The per-coordinate ledger inequality

Assembling the pieces into the inequality the exclusion argument consumes.
`A₀ = 17/80`, `λ = 7/4`, `α = 1/2`, all in **bits**. -/

/-- The without-replacement correction, in bits.  The `4/L` terms come from
`abs_expectation_sub_le_of_dominated`; the `binaryEntropy (4/L)` term is the
modulus of continuity of `h` and is the source of the `log L / L` shape quoted
in `THEOREM_r3.md` (`h(4/L) = (4/L)·log₂(L/4) + O(1/L)`). -/
noncomputable def worCorrection (L : ℕ) : ℝ :=
  4 / (L : ℝ) + (7 / 4 : ℝ) * (4 / (L : ℝ)) + binaryEntropy (4 / (L : ℝ)) / 2

/-- `c - 1 ≤ 4/L` for `L ≥ 10`, where `c = L³/(L(L-1)(L-2))`. -/
theorem domination_constant_le (L : ℕ) (hL : 10 ≤ L) :
    (L : ℝ) ^ 3 / ((L : ℝ) * ((L : ℝ) - 1) * ((L : ℝ) - 2)) - 1 ≤ 4 / (L : ℝ) := by
  have h10 : (10 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hpos : (0 : ℝ) < (L : ℝ) := by linarith
  have hD : 0 < (L : ℝ) * ((L : ℝ) - 1) * ((L : ℝ) - 2) :=
    mul_pos (mul_pos (by linarith) (by linarith)) (by linarith)
  rw [div_sub_one hD.ne', div_le_div_iff₀ hD hpos]
  nlinarith

/-- Modulus of continuity of the binary entropy: the published file already
proves this as `abs_binaryEntropy_sub_le_binaryEntropy_abs_sub`. -/
theorem abs_binaryEntropy_sub_le {x y : ℝ}
    (hx : 0 ≤ x) (hx' : x ≤ 1) (hy : 0 ≤ y) (hy' : y ≤ 1)
    (_ : |x - y| ≤ 1 / 2) :
    |binaryEntropy x - binaryEntropy y| ≤ binaryEntropy |x - y| :=
  abs_binaryEntropy_sub_le_binaryEntropy_abs_sub x y hx hx' hy hy'

/-- **The per-coordinate ledger inequality.**

`E` is the empirical (without-replacement) average conditional entropy at one
coordinate, `τ` the empirical average disagreement, `Φchild`/`Φparent` the
binary entropies of the empirical means of the child and parent layers.  The
hypotheses are exactly what the without-replacement layer delivers:
`kernel` is the i.i.d. idealisation with `q = ` the parent-layer empirical mean
(which `threeSubset_slot_marginal` shows is *exact*), and each empirical
functional differs from its i.i.d. counterpart by at most `4/L`. -/
theorem ledger_inequality (L : ℕ) (_ : 10 ≤ L)
    (kernel : BinaryTripleKernel) (E τ childMean : ℝ)
    (hchildMean : 0 ≤ childMean) (hchildMean' : childMean ≤ 1)
    (hE : E - kernel.conditionalEntropy ≤ 4 / (L : ℝ))
    (hτ : kernel.averageDisagreement - τ ≤ 4 / (L : ℝ))
    (hchild : |childMean - kernel.childMarginal| ≤ 1 / 2)
    (hchild' : binaryEntropy |childMean - kernel.childMarginal| ≤
      binaryEntropy (4 / (L : ℝ))) :
    E ≤ (17 / 80 : ℝ) + (7 / 4 : ℝ) * τ +
        (binaryEntropy childMean -
          binaryEntropy kernel.parentProbability) / 2 +
      worCorrection L := by
  have hbound := BinaryTripleKernel.conditionalEntropy_bound kernel
  have hcont := abs_binaryEntropy_sub_le hchildMean hchildMean'
    (kernel.childMarginal_nonneg) (kernel.childMarginal_le_one) hchild
  have hcont' : binaryEntropy kernel.childMarginal - binaryEntropy childMean ≤
      binaryEntropy (4 / (L : ℝ)) := by
    have := (abs_le.mp hcont).1
    linarith [hchild']
  unfold worCorrection
  linarith

end ThreeDegenerateGraphs
