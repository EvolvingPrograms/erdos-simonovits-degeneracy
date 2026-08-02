import LawDefs
import LemmaA
import Lemma61
import LemmaC

/-!
# Lemma B: the supremum of `G_r` sits at the symmetric point

Design-notes reference (notes not shipped in this repository): §4 (statement in §4.7).

Target:
`supG r lam = Gfun r lam (1/2) (1/2)` for `2 ≤ r`, `0 < lam ≤ 27/20`.
-/

namespace DegeneracyLaw
namespace LemmaB

open TwoDegenerateGraphs Finset

noncomputable section

/-! ## §0 Small helpers -/

lemma log_two_pos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)

/-- Rewrite the derivative value of a `HasDerivAt` statement. -/
private lemma HDA_congr {f : ℝ → ℝ} {c d x : ℝ} (h : HasDerivAt f c x) (hcd : c = d) :
    HasDerivAt f d x := hcd ▸ h

/-! ## §1 A square-root bound used by the `v`-direction estimates -/

/-- `√v + √(1-v) ≤ √2` on `[0,1]`. -/
lemma sqrt_add_sqrt_one_sub_le {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Real.sqrt v + Real.sqrt (1 - v) ≤ 2 * Real.sqrt (1 / 2) := by
  have hs : Real.sqrt v ^ 2 = v := Real.sq_sqrt hv0
  have ht : Real.sqrt (1 - v) ^ 2 = 1 - v := Real.sq_sqrt (by linarith)
  have h2 : (2 * Real.sqrt (1 / 2)) ^ 2 = 2 := by
    have : Real.sqrt (1 / 2) ^ 2 = 1 / 2 := Real.sq_sqrt (by norm_num)
    nlinarith [this]
  have hnn : 0 ≤ 2 * Real.sqrt (1 / 2) := by positivity
  have hlhs : 0 ≤ Real.sqrt v + Real.sqrt (1 - v) := by positivity
  nlinarith [sq_nonneg (Real.sqrt v - Real.sqrt (1 - v)), hs, ht, h2, hnn, hlhs]

/-! ## §2 Symmetry of `G_r` under `(q,v) ↦ (1-q, 1-v)` -/

/-- **Index reflection `j ↦ r - j`.** `G_r(q,v) = G_r(1-q, 1-v)`. -/
theorem Gfun_symm (r : ℕ) (lam q v : ℝ) :
    Gfun r lam q v = Gfun r lam (1 - q) (1 - v) := by
  unfold Gfun
  have hent : binaryEntropy q = binaryEntropy (1 - q) := by
    unfold binaryEntropy; rw [Real.binEntropy_one_sub]
  rw [hent]
  congr 1
  rw [← Finset.sum_range_reflect
    (fun j => ((r.choose j : ℝ) * (1 - q) ^ j * (1 - (1 - q)) ^ (r - j) *
      logTwo (Real.sqrt (1 - (1 - v)) * 2 ^ (-(lam * j) / r) +
              Real.sqrt (1 - v) * 2 ^ (-(lam * (r - j : ℝ)) / r)))) (r + 1)]
  refine Finset.sum_congr rfl ?_
  intro j hj
  have hjr : j ≤ r := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
  have hidx : r + 1 - 1 - j = r - j := by omega
  rw [hidx]
  have hchoose : r.choose (r - j) = r.choose j := Nat.choose_symm hjr
  have hsub : r - (r - j) = j := by omega
  have hcast : ((r - j : ℕ) : ℝ) = (r : ℝ) - j := by
    push_cast [Nat.cast_sub hjr]; ring
  have hcast2 : ((r : ℝ) - ((r - j : ℕ) : ℝ)) = (j : ℝ) := by rw [hcast]; ring
  rw [hchoose, hsub, hcast2]
  have hv : (1 : ℝ) - (1 - v) = v := by ring
  have hq : (1 : ℝ) - (1 - q) = q := by ring
  rw [hv, hq, hcast]
  ring_nf

/-! ## §3b The Bernstein operator and its derivatives (paper §4.3)

`B_r[u](q) = ∑_j C(r,j) q^j (1-q)^{r-j} u_j`. We prove the two exact
difference formulas
`(B_r u)' = r · B_{r-1}[Δu]` and `(B_r u)'' = r(r-1) · B_{r-2}[Δ²u]`,
which is the algebraic core of the transfer (4.6).
-/

/-- The Bernstein polynomial of a real sequence. -/
def bern (r : ℕ) (u : ℕ → ℝ) (q : ℝ) : ℝ :=
  ∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) * u j

/-- The forward difference `(Δu)_j = u_{j+1} - u_j`. -/
def fwdDiff (u : ℕ → ℝ) : ℕ → ℝ := fun j => u (j + 1) - u j

/-- Derivative of a single Bernstein term. -/
lemma hasDerivAt_bernTerm (r j : ℕ) (u : ℕ → ℝ) (q : ℝ) :
    HasDerivAt (fun x : ℝ => (r.choose j : ℝ) * x ^ j * (1 - x) ^ (r - j) * u j)
      ((r.choose j : ℝ) * u j *
        ((j : ℝ) * q ^ (j - 1) * (1 - q) ^ (r - j)
          - ((r - j : ℕ) : ℝ) * q ^ j * (1 - q) ^ (r - j - 1))) q := by
  have h1 : HasDerivAt (fun x : ℝ => x ^ j) ((j : ℝ) * q ^ (j - 1)) q := hasDerivAt_pow j q
  have hin : HasDerivAt (fun x : ℝ => 1 - x) (-1 : ℝ) q := by
    simpa using (hasDerivAt_id q).const_sub 1
  have h2 : HasDerivAt (fun x : ℝ => (1 - x) ^ (r - j))
      (((r - j : ℕ) : ℝ) * (1 - q) ^ (r - j - 1) * (-1)) q :=
    (hasDerivAt_pow (r - j) (1 - q)).comp q hin
  have h3 := ((h1.const_mul ((r.choose j : ℝ))).mul h2).mul_const (u j)
  exact HDA_congr h3 (by ring)

/-- Derivative of the whole Bernstein polynomial, before simplification. -/
lemma hasDerivAt_bern_raw (r : ℕ) (u : ℕ → ℝ) (q : ℝ) :
    HasDerivAt (bern r u)
      (∑ j ∈ Finset.range (r + 1), (r.choose j : ℝ) * u j *
        ((j : ℝ) * q ^ (j - 1) * (1 - q) ^ (r - j)
          - ((r - j : ℕ) : ℝ) * q ^ j * (1 - q) ^ (r - j - 1))) q := by
  have hfun : (bern r u) = ∑ j ∈ Finset.range (r + 1),
      (fun x : ℝ => (r.choose j : ℝ) * x ^ j * (1 - x) ^ (r - j) * u j) := by
    funext x
    simp [bern, Finset.sum_apply]
  rw [hfun]
  exact HasDerivAt.sum (fun j _ => hasDerivAt_bernTerm r j u q)

/-- **The Bernstein first-difference identity.** -/
lemma bern_deriv_sum (m : ℕ) (u : ℕ → ℝ) (q : ℝ) :
    (∑ j ∈ Finset.range (m + 1 + 1), ((m + 1).choose j : ℝ) * u j *
        ((j : ℝ) * q ^ (j - 1) * (1 - q) ^ (m + 1 - j)
          - ((m + 1 - j : ℕ) : ℝ) * q ^ j * (1 - q) ^ (m + 1 - j - 1)))
      = (m + 1 : ℝ) * bern m (fwdDiff u) q := by
  have hsplit : ∀ j ∈ Finset.range (m + 1 + 1),
      ((m + 1).choose j : ℝ) * u j *
        ((j : ℝ) * q ^ (j - 1) * (1 - q) ^ (m + 1 - j)
          - ((m + 1 - j : ℕ) : ℝ) * q ^ j * (1 - q) ^ (m + 1 - j - 1))
      = (((m + 1).choose j : ℝ) * u j * ((j : ℝ) * q ^ (j - 1) * (1 - q) ^ (m + 1 - j)))
        - (((m + 1).choose j : ℝ) * u j *
            (((m + 1 - j : ℕ) : ℝ) * q ^ j * (1 - q) ^ (m - j))) := by
    intro j _
    have h : m + 1 - j - 1 = m - j := by omega
    rw [h]; ring
  rw [Finset.sum_congr rfl hsplit, Finset.sum_sub_distrib]
  have hS1 : (∑ j ∈ Finset.range (m + 1 + 1),
      ((m + 1).choose j : ℝ) * u j * ((j : ℝ) * q ^ (j - 1) * (1 - q) ^ (m + 1 - j)))
      = (m + 1 : ℝ) * ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * q ^ i * (1 - q) ^ (m - i) * u (i + 1) := by
    rw [Finset.sum_range_succ']
    simp only [Nat.cast_zero, zero_mul, mul_zero, add_zero]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have he1 : i + 1 - 1 = i := by omega
    have he2 : m + 1 - (i + 1) = m - i := by omega
    have hch : ((m + 1).choose (i + 1) : ℝ) * ((i : ℝ) + 1) = ((m : ℝ) + 1) * (m.choose i : ℝ) := by
      have h := Nat.add_one_mul_choose_eq m i
      have := congrArg (fun n : ℕ => (n : ℝ)) h
      push_cast at this
      linarith [this]
    rw [he1, he2]
    push_cast
    linear_combination (u (i + 1) * q ^ i * (1 - q) ^ (m - i)) * hch
  have hS2 : (∑ j ∈ Finset.range (m + 1 + 1),
      ((m + 1).choose j : ℝ) * u j * (((m + 1 - j : ℕ) : ℝ) * q ^ j * (1 - q) ^ (m - j)))
      = (m + 1 : ℝ) * ∑ i ∈ Finset.range (m + 1),
          (m.choose i : ℝ) * q ^ i * (1 - q) ^ (m - i) * u i := by
    rw [Finset.sum_range_succ]
    have hzero : ((m + 1 - (m + 1) : ℕ) : ℝ) = 0 := by simp
    rw [hzero]
    simp only [zero_mul, mul_zero, add_zero]
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl ?_
    intro i hi
    have hi' : i ≤ m := Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)
    have hcast : ((m + 1 - i : ℕ) : ℝ) = (m : ℝ) + 1 - (i : ℝ) := by
      push_cast [Nat.cast_sub (by omega : i ≤ m + 1)]; ring
    have hch : ((m + 1).choose i : ℝ) * ((m : ℝ) + 1 - (i : ℝ))
        = ((m : ℝ) + 1) * (m.choose i : ℝ) := by
      have h := Nat.choose_mul_succ_eq m i
      have h2 := congrArg (fun n : ℕ => (n : ℝ)) h
      push_cast [Nat.cast_sub (by omega : i ≤ m + 1)] at h2
      linarith [h2]
    rw [hcast]
    linear_combination (u i * q ^ i * (1 - q) ^ (m - i)) * hch
  rw [hS1, hS2]
  unfold bern fwdDiff
  rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro i _
  ring

/-- **`(B_r u)' = r · B_{r-1}[Δu]`** (paper §4.3, first half). -/
theorem hasDerivAt_bern (m : ℕ) (u : ℕ → ℝ) (q : ℝ) :
    HasDerivAt (bern (m + 1) u) ((m + 1 : ℝ) * bern m (fwdDiff u) q) q := by
  have h := hasDerivAt_bern_raw (m + 1) u q
  rwa [bern_deriv_sum m u q] at h

/-- **`(B_r u)'' = r(r-1) · B_{r-2}[Δ²u]`** (paper §4.3, the formula the
transfer (4.6) is applied to). -/
theorem hasDerivAt_bern_second (m : ℕ) (u : ℕ → ℝ) (q : ℝ) :
    HasDerivAt (fun x : ℝ => (m + 2 : ℝ) * bern (m + 1) (fwdDiff u) x)
      ((m + 2 : ℝ) * (m + 1 : ℝ) * bern m (fwdDiff (fwdDiff u)) q) q := by
  have h := (hasDerivAt_bern m (fwdDiff u) q).const_mul ((m : ℝ) + 2)
  exact HDA_congr h (by ring)

/-- The Bernstein basis is a partition of unity: `B_r[1] = 1`. -/
lemma bern_one (r : ℕ) (q : ℝ) : bern r (fun _ => (1 : ℝ)) q = 1 := by
  unfold bern
  have h := add_pow q (1 - q) r
  simp only [mul_one]
  rw [show (q + (1 - q)) = (1 : ℝ) by ring, one_pow] at h
  refine Eq.trans ?_ h.symm
  refine Finset.sum_congr rfl ?_
  intro j _
  ring

/-- **The Bernstein transfer (4.6), sup form.** If all coefficients are `≤ M`
then `B_r[u](q) ≤ M` for `q ∈ [0,1]`. -/
lemma bern_le_of_le (r : ℕ) (u : ℕ → ℝ) (M q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : ∀ j, u j ≤ M) : bern r u q ≤ M := by
  have hcoeff : ∀ j : ℕ, (0 : ℝ) ≤ (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) := by
    intro j
    have h1 : (0 : ℝ) ≤ (r.choose j : ℝ) := by positivity
    exact mul_nonneg (mul_nonneg h1 (pow_nonneg hq0 j)) (pow_nonneg (by linarith) _)
  have hle : bern r u q ≤ bern r (fun _ => M) q := by
    unfold bern
    refine Finset.sum_le_sum ?_
    intro j _
    exact mul_le_mul_of_nonneg_left (h j) (hcoeff j)
  have hM : bern r (fun _ => M) q = M := by
    have : bern r (fun _ => M) q = M * bern r (fun _ => (1 : ℝ)) q := by
      unfold bern
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl ?_
      intro j _
      ring
    rw [this, bern_one]; ring
  linarith [hle, hM]

/-- The second difference in explicit form. -/
lemma fwdDiff_fwdDiff (u : ℕ → ℝ) (j : ℕ) :
    fwdDiff (fwdDiff u) j = u (j + 2) - 2 * u (j + 1) + u j := by
  unfold fwdDiff
  have : j + 1 + 1 = j + 2 := by omega
  rw [this]; ring

/-- **Second differences versus the second derivative.**
If `f'' ≤ M` everywhere then `f(x+2h) - 2f(x+h) + f(x) ≤ M h²` for `h > 0`.
This is the missing half of the Bernstein transfer (4.6): together with
`hasDerivAt_bern_second` and `bern_le_of_le` it turns a bound on `sup u''`
into a bound on `(B_r u)''`. -/
theorem second_difference_le {f f' f'' : ℝ → ℝ}
    (hd : ∀ x, HasDerivAt f (f' x) x) (hd' : ∀ x, HasDerivAt f' (f'' x) x)
    {M : ℝ} (hM : ∀ x, f'' x ≤ M) {h : ℝ} (hh : 0 < h) (x : ℝ) :
    f (x + 2 * h) - 2 * f (x + h) + f x ≤ M * h ^ 2 := by
  -- `g s = f (s + h) - f s`
  set g : ℝ → ℝ := fun s => f (s + h) - f s with hgdef
  set g' : ℝ → ℝ := fun s => f' (s + h) - f' s with hg'def
  have hg : ∀ s : ℝ, HasDerivAt g (g' s) s := by
    intro s
    have hsh : HasDerivAt (fun t : ℝ => f (t + h)) (f' (s + h)) s := by
      have hin : HasDerivAt (fun t : ℝ => t + h) (1 : ℝ) s := (hasDerivAt_id s).add_const h
      exact HDA_congr ((hd (s + h)).comp s hin) (by ring)
    exact hsh.sub (hd s)
  -- first mean value theorem
  obtain ⟨η, hη, heq⟩ := exists_hasDerivAt_eq_slope g g' (by linarith : x < x + h)
    (fun s _ => (hg s).continuousAt.continuousWithinAt) (fun s _ => hg s)
  -- second mean value theorem, applied to `f'` on `[η, η + h]`
  obtain ⟨ζ, hζ, heq2⟩ := exists_hasDerivAt_eq_slope f' f'' (by linarith : η < η + h)
    (fun s _ => (hd' s).continuousAt.continuousWithinAt) (fun s _ => hd' s)
  have hslope : g (x + h) - g x = h * g' η := by
    have hxh : x + h - x = h := by ring
    rw [eq_comm, div_eq_iff (by linarith : (x + h) - x ≠ 0)] at heq
    rw [hxh] at heq
    linarith [heq]
  have hslope2 : f' (η + h) - f' η = h * f'' ζ := by
    have hxh : η + h - η = h := by ring
    rw [eq_comm, div_eq_iff (by linarith : (η + h) - η ≠ 0)] at heq2
    rw [hxh] at heq2
    linarith [heq2]
  have hg'η : g' η = h * f'' ζ := by
    simp only [hg'def]
    linarith [hslope2]
  have hexpand : g (x + h) - g x = f (x + 2 * h) - 2 * f (x + h) + f x := by
    simp only [hgdef]
    have : x + h + h = x + 2 * h := by ring
    rw [this]
    ring
  rw [← hexpand, hslope, hg'η]
  have : f'' ζ ≤ M := hM ζ
  nlinarith [hh, this]

/-! ## §3c `rpow`/`exp` conversion

The exact centre value `G_r(1/2,1/2) = centerSum r lam` (paper (4.13)) is proved
once and for all in `Lemma61.lean` as `DegeneracyLaw.Gfun_center_eq`; this file
consumes it (see `supG_eq_center` below) rather than reproving it.
-/

/-- `2 ^ x = exp (x · ln 2)` for real exponents. -/
lemma two_rpow_eq_exp (x : ℝ) : (2 : ℝ) ^ x = Real.exp (x * Real.log 2) := by
  rw [Real.rpow_def_of_pos (by norm_num : (0:ℝ) < 2)]
  ring_nf

/-! ## §3d The angular objects and the three sharp derivative bounds (paper §4.2)

`T(y,θ) = cos θ e^{-ay} + sin θ e^{-a(1-y)}`, `ψ = log₂ T`. We prove exactly the
three bounds (4.3a), (4.4), (4.5):
`0 ≤ ψ_yy ≤ a²/ln2`, `ψ_θθ ≤ -1/ln2`, `0 < ψ_yθ ≤ a/(ln2 · sin 2θ)`.
-/

/-- `T(y,θ) = cos θ · e^{-a y} + sin θ · e^{-a(1-y)}` (paper §4.0). -/
def Tang (a y θ : ℝ) : ℝ :=
  Real.cos θ * Real.exp (-(a * y)) + Real.sin θ * Real.exp (-(a * (1 - y)))

/-- `∂_θ T`. -/
def Tth (a y θ : ℝ) : ℝ :=
  -Real.sin θ * Real.exp (-(a * y)) + Real.cos θ * Real.exp (-(a * (1 - y)))

/-- `∂_y T`. -/
def Ty (a y θ : ℝ) : ℝ :=
  -a * (Real.cos θ * Real.exp (-(a * y))) + a * (Real.sin θ * Real.exp (-(a * (1 - y))))

/-- `ψ = log₂ T` (paper §4.0). -/
def psi (a y θ : ℝ) : ℝ := logTwo (Tang a y θ)

lemma exp_mul_exp_eq (a y : ℝ) :
    Real.exp (-(a * y)) * Real.exp (-(a * (1 - y))) = Real.exp (-a) := by
  rw [← Real.exp_add]; congr 1; ring

lemma hasDerivAt_expE (a y : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-(a * x))) (Real.exp (-(a * y)) * -a) y := by
  have hin : HasDerivAt (fun x : ℝ => -(a * x)) (-a) y := by
    have h : HasDerivAt (fun x : ℝ => -a * x) (-a * 1) y := (hasDerivAt_id y).const_mul (-a)
    have e : (fun x : ℝ => -a * x) = fun x : ℝ => -(a * x) := by funext x; ring
    rw [e] at h
    exact HDA_congr h (by ring)
  exact (Real.hasDerivAt_exp _).comp y hin

lemma hasDerivAt_expF (a y : ℝ) :
    HasDerivAt (fun x : ℝ => Real.exp (-(a * (1 - x)))) (Real.exp (-(a * (1 - y))) * a) y := by
  have hin : HasDerivAt (fun x : ℝ => -(a * (1 - x))) a y := by
    have h1 : HasDerivAt (fun x : ℝ => 1 - x) (-1 : ℝ) y := by
      simpa using (hasDerivAt_id y).const_sub 1
    have h := h1.const_mul (-a)
    have e : (fun x : ℝ => -a * (1 - x)) = fun x : ℝ => -(a * (1 - x)) := by funext x; ring
    rw [e] at h
    exact HDA_congr h (by ring)
  exact (Real.hasDerivAt_exp _).comp y hin

lemma Tang_pos {a y θ : ℝ} (hc : 0 < Real.cos θ) (hs : 0 < Real.sin θ) :
    0 < Tang a y θ := by
  unfold Tang
  have h1 : 0 < Real.cos θ * Real.exp (-(a * y)) := by positivity
  have h2 : 0 < Real.sin θ * Real.exp (-(a * (1 - y))) := by positivity
  linarith

/-! ### `θ`-derivatives -/

lemma hasDerivAt_Tang_theta (a y θ : ℝ) :
    HasDerivAt (fun x : ℝ => Tang a y x) (Tth a y θ) θ := by
  have h1 : HasDerivAt (fun x : ℝ => Real.cos x * Real.exp (-(a * y)))
      (-Real.sin θ * Real.exp (-(a * y))) θ := (Real.hasDerivAt_cos θ).mul_const _
  have h2 : HasDerivAt (fun x : ℝ => Real.sin x * Real.exp (-(a * (1 - y))))
      (Real.cos θ * Real.exp (-(a * (1 - y)))) θ := (Real.hasDerivAt_sin θ).mul_const _
  exact h1.add h2

lemma hasDerivAt_Tth_theta (a y θ : ℝ) :
    HasDerivAt (fun x : ℝ => Tth a y x) (-Tang a y θ) θ := by
  have h1 : HasDerivAt (fun x : ℝ => -Real.sin x * Real.exp (-(a * y)))
      (-Real.cos θ * Real.exp (-(a * y))) θ := by
    have := ((Real.hasDerivAt_sin θ).neg).mul_const (Real.exp (-(a * y)))
    exact HDA_congr this (by ring)
  have h2 : HasDerivAt (fun x : ℝ => Real.cos x * Real.exp (-(a * (1 - y))))
      (-Real.sin θ * Real.exp (-(a * (1 - y)))) θ := (Real.hasDerivAt_cos θ).mul_const _
  have := h1.add h2
  refine HDA_congr this ?_
  unfold Tang
  ring

/-- `ψ_θ = T_θ / (T ln 2)`. -/
lemma hasDerivAt_psi_theta (a y θ : ℝ) (hT : 0 < Tang a y θ) :
    HasDerivAt (fun x : ℝ => psi a y x) (Tth a y θ / (Tang a y θ * Real.log 2)) θ := by
  have hlog := (hasDerivAt_Tang_theta a y θ).log (ne_of_gt hT)
  have := hlog.div_const (Real.log 2)
  refine HDA_congr this ?_
  field_simp

/-- **(4.4)** `ψ_θθ = -(T² + T_θ²)/(T² ln2)`. -/
lemma hasDerivAt_psi_theta2 (a y θ : ℝ) (hT : 0 < Tang a y θ) :
    HasDerivAt (fun x : ℝ => Tth a y x / (Tang a y x * Real.log 2))
      (-((Tang a y θ) ^ 2 + (Tth a y θ) ^ 2) / ((Tang a y θ) ^ 2 * Real.log 2)) θ := by
  have hlog2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have hden : HasDerivAt (fun x : ℝ => Tang a y x * Real.log 2)
      (Tth a y θ * Real.log 2) θ := (hasDerivAt_Tang_theta a y θ).mul_const _
  have hne : Tang a y θ * Real.log 2 ≠ 0 := by positivity
  have h := (hasDerivAt_Tth_theta a y θ).div hden hne
  refine HDA_congr h ?_
  have hT' : Tang a y θ ≠ 0 := ne_of_gt hT
  field_simp
  ring

/-- **(4.4)** the uniform concavity bound `ψ_θθ ≤ -1/ln 2`. -/
theorem psi_theta2_le (a y θ : ℝ) (hT : 0 < Tang a y θ) :
    -((Tang a y θ) ^ 2 + (Tth a y θ) ^ 2) / ((Tang a y θ) ^ 2 * Real.log 2)
      ≤ -(1 / Real.log 2) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have hT2 : (0 : ℝ) < (Tang a y θ) ^ 2 := by positivity
  rw [div_le_iff₀ (by positivity), neg_mul]
  have hsq : (0 : ℝ) ≤ (Tth a y θ) ^ 2 := sq_nonneg _
  have : 1 / Real.log 2 * ((Tang a y θ) ^ 2 * Real.log 2) = (Tang a y θ) ^ 2 := by
    field_simp
  nlinarith [this, hsq]

/-! ### `y`-derivatives -/

lemma hasDerivAt_Tang_y (a y θ : ℝ) :
    HasDerivAt (fun x : ℝ => Tang a x θ) (Ty a y θ) y := by
  have he1 := hasDerivAt_expE a y
  have he2 := hasDerivAt_expF a y
  have h := (he1.const_mul (Real.cos θ)).add (he2.const_mul (Real.sin θ))
  refine HDA_congr h ?_
  unfold Ty
  ring

lemma hasDerivAt_Ty_y (a y θ : ℝ) :
    HasDerivAt (fun x : ℝ => Ty a x θ) (a ^ 2 * Tang a y θ) y := by
  have he1 := hasDerivAt_expE a y
  have he2 := hasDerivAt_expF a y
  have h := ((he1.const_mul (Real.cos θ)).const_mul (-a)).add
    ((he2.const_mul (Real.sin θ)).const_mul a)
  refine HDA_congr h ?_
  unfold Tang
  ring

/-- `ψ_y = T_y / (T ln 2)`. -/
lemma hasDerivAt_psi_y (a y θ : ℝ) (hT : 0 < Tang a y θ) :
    HasDerivAt (fun x : ℝ => psi a x θ) (Ty a y θ / (Tang a y θ * Real.log 2)) y := by
  have hlog := (hasDerivAt_Tang_y a y θ).log (ne_of_gt hT)
  have := hlog.div_const (Real.log 2)
  refine HDA_congr this ?_
  field_simp

/-- **(4.3a)** `ψ_yy = (a²T² - T_y²)/(T² ln2)`. -/
lemma hasDerivAt_psi_y2 (a y θ : ℝ) (hT : 0 < Tang a y θ) :
    HasDerivAt (fun x : ℝ => Ty a x θ / (Tang a x θ * Real.log 2))
      ((a ^ 2 * (Tang a y θ) ^ 2 - (Ty a y θ) ^ 2) / ((Tang a y θ) ^ 2 * Real.log 2)) y := by
  have hlog2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have hden : HasDerivAt (fun x : ℝ => Tang a x θ * Real.log 2)
      (Ty a y θ * Real.log 2) y := (hasDerivAt_Tang_y a y θ).mul_const _
  have hne : Tang a y θ * Real.log 2 ≠ 0 := by positivity
  have h := (hasDerivAt_Ty_y a y θ).div hden hne
  refine HDA_congr h ?_
  have hT' : Tang a y θ ≠ 0 := ne_of_gt hT
  field_simp
  try ring

/-- **(4.3a)** the convexity bound `ψ_yy ≤ a²/ln 2`. -/
theorem psi_y2_le (a y θ : ℝ) (hT : 0 < Tang a y θ) :
    (a ^ 2 * (Tang a y θ) ^ 2 - (Ty a y θ) ^ 2) / ((Tang a y θ) ^ 2 * Real.log 2)
      ≤ a ^ 2 / Real.log 2 := by
  have hlog2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have hT2 : (0 : ℝ) < (Tang a y θ) ^ 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) hlog2]
  nlinarith [sq_nonneg (Ty a y θ), hT2, hlog2]

/-! ### The mixed derivative -/

/-- **(4.5)** `ψ_yθ = 2a e^{-a}/(T² ln2) > 0`. -/
lemma hasDerivAt_psi_ytheta (a y θ : ℝ) (hT : 0 < Tang a y θ) :
    HasDerivAt (fun x : ℝ => Tth a x θ / (Tang a x θ * Real.log 2))
      (2 * a * Real.exp (-a) / ((Tang a y θ) ^ 2 * Real.log 2)) y := by
  have hlog2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have he1 := hasDerivAt_expE a y
  have he2 := hasDerivAt_expF a y
  have hnum : HasDerivAt (fun x : ℝ => Tth a x θ)
      (a * (Real.sin θ * Real.exp (-(a * y)) + Real.cos θ * Real.exp (-(a * (1 - y))))) y := by
    have h := (he1.const_mul (-Real.sin θ)).add (he2.const_mul (Real.cos θ))
    refine HDA_congr h ?_
    ring
  have hden : HasDerivAt (fun x : ℝ => Tang a x θ * Real.log 2)
      (Ty a y θ * Real.log 2) y := (hasDerivAt_Tang_y a y θ).mul_const _
  have hne : Tang a y θ * Real.log 2 ≠ 0 := by positivity
  have h := hnum.div hden hne
  refine HDA_congr h ?_
  have hT' : Tang a y θ ≠ 0 := ne_of_gt hT
  have hEF := exp_mul_exp_eq a y
  have hpyth : Real.sin θ ^ 2 + Real.cos θ ^ 2 = 1 := Real.sin_sq_add_cos_sq θ
  -- the exact numerator identity `∂_yT_θ · T - T_θ · T_y = 2a e^{-a}`
  have hkey : a * (Real.sin θ * Real.exp (-(a * y)) + Real.cos θ * Real.exp (-(a * (1 - y))))
        * Tang a y θ - Tth a y θ * Ty a y θ
      = 2 * a * Real.exp (-a) := by
    unfold Tang Tth Ty
    linear_combination
      (2 * a * Real.exp (-(a * y)) * Real.exp (-(a * (1 - y)))) * hpyth + (2 * a) * hEF
  rw [div_eq_div_iff (by positivity) (by positivity)]
  linear_combination ((Tang a y θ) ^ 2 * Real.log 2 ^ 2) * hkey

/-- AM–GM: `T² ≥ 2 e^{-a} sin 2θ`. -/
lemma Tang_sq_ge (a y θ : ℝ) :
    2 * Real.exp (-a) * Real.sin (2 * θ) ≤ (Tang a y θ) ^ 2 := by
  have hEF := exp_mul_exp_eq a y
  have hdouble : Real.sin (2 * θ) = 2 * Real.sin θ * Real.cos θ := Real.sin_two_mul θ
  have hE : (0 : ℝ) < Real.exp (-(a * y)) := Real.exp_pos _
  have hF : (0 : ℝ) < Real.exp (-(a * (1 - y))) := Real.exp_pos _
  have hEF' : Real.cos θ * Real.exp (-(a * y)) * (Real.sin θ * Real.exp (-(a * (1 - y))))
      = Real.sin θ * Real.cos θ * Real.exp (-a) := by
    linear_combination (Real.sin θ * Real.cos θ) * hEF
  unfold Tang
  rw [hdouble]
  nlinarith [sq_nonneg (Real.cos θ * Real.exp (-(a * y)) -
    Real.sin θ * Real.exp (-(a * (1 - y)))), hEF']

/-- **(4.5)** the sharp cross bound `ψ_yθ ≤ a/(ln 2 · sin 2θ)`. -/
theorem psi_ytheta_le (a y θ : ℝ) (ha : 0 < a) (hc : 0 < Real.cos θ) (hs : 0 < Real.sin θ)
    (hsin2 : 0 < Real.sin (2 * θ)) :
    2 * a * Real.exp (-a) / ((Tang a y θ) ^ 2 * Real.log 2)
      ≤ a / (Real.log 2 * Real.sin (2 * θ)) := by
  have hlog2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have hT : 0 < Tang a y θ := Tang_pos hc hs
  have hT2 : (0 : ℝ) < (Tang a y θ) ^ 2 := by positivity
  have hge := Tang_sq_ge a y θ
  have hexp : (0 : ℝ) < Real.exp (-a) := Real.exp_pos _
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hscaled := mul_le_mul_of_nonneg_left hge
    (by positivity : (0 : ℝ) ≤ a * Real.log 2)
  nlinarith [hscaled]

/-! ## §4 The angular strip (paper §4.4) -/

/-- The angular coordinate `θ` with `v = sin²θ`, `θ ∈ [0, π/2]`. -/
def thetaOf (v : ℝ) : ℝ := Real.arcsin (Real.sqrt v)

/-- `ρ_crit(a) = ½ arccos √(a²/(2-a²))` (paper §4.4). -/
def rhoCrit (a : ℝ) : ℝ := Real.arccos (Real.sqrt (a ^ 2 / (2 - a ^ 2))) / 2

/-- The shrunken half-width `ρ = 0.99 ρ_crit` (paper §4.4). -/
def rho (a : ℝ) : ℝ := (99 / 100) * rhoCrit a

/-- The strip `S = [0,1] × [π/4 - ρ, π/4 + ρ]` in `v`-coordinates. -/
def inStrip (lam v : ℝ) : Prop :=
  |thetaOf v - Real.pi / 4| ≤ rho (lam * Real.log 2)

/-- The `κ = √(a²/(2-a²))` of Prop. 4.1. -/
def kappaOf (a : ℝ) : ℝ := Real.sqrt (a ^ 2 / (2 - a ^ 2))

lemma kappaOf_nonneg (a : ℝ) : 0 ≤ kappaOf a := Real.sqrt_nonneg _

lemma kappaOf_lt_one {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : kappaOf a < 1 := by
  unfold kappaOf
  have hden : (0 : ℝ) < 2 - a ^ 2 := by nlinarith
  rw [show (1 : ℝ) = Real.sqrt 1 by simp]
  apply Real.sqrt_lt_sqrt (by positivity)
  rw [div_lt_one (by nlinarith)]
  nlinarith

lemma rhoCrit_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < rhoCrit a := by
  unfold rhoCrit
  have h := Real.arccos_pos.2 (kappaOf_lt_one ha0 ha1)
  unfold kappaOf at h
  linarith

lemma rho_pos {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) : 0 < rho a := by
  unfold rho
  have := rhoCrit_pos ha0 ha1
  linarith

lemma two_rho_lt_pi_div_two {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    2 * rho a < Real.pi / 2 := by
  unfold rho rhoCrit
  have h1 : Real.arccos (Real.sqrt (a ^ 2 / (2 - a ^ 2))) ≤ Real.pi / 2 :=
    Real.arccos_le_pi_div_two.2 (Real.sqrt_nonneg _)
  have h2 : (0 : ℝ) < Real.arccos (Real.sqrt (a ^ 2 / (2 - a ^ 2))) :=
    Real.arccos_pos.2 (kappaOf_lt_one ha0 ha1)
  linarith

/-- **Prop. 4.1, the strip inequality (strict half).** `cos 2ρ > κ`, the payoff
of the 1% retreat `ρ = 0.99 ρ_crit`. -/
theorem kappa_lt_cos_two_rho {a : ℝ} (ha0 : 0 < a) (ha1 : a < 1) :
    kappaOf a < Real.cos (2 * rho a) := by
  have hk1 : kappaOf a < 1 := kappaOf_lt_one ha0 ha1
  have hk0 : 0 ≤ kappaOf a := kappaOf_nonneg a
  have hA : (0 : ℝ) < Real.arccos (kappaOf a) := Real.arccos_pos.2 hk1
  have hApi : Real.arccos (kappaOf a) ≤ Real.pi := Real.arccos_le_pi _
  have hlt : 2 * rho a < Real.arccos (kappaOf a) := by
    unfold rho rhoCrit kappaOf
    unfold kappaOf at hA
    linarith
  have hnn : (0 : ℝ) ≤ 2 * rho a := by
    have := rho_pos ha0 ha1; linarith
  have := Real.cos_lt_cos_of_nonneg_of_le_pi hnn hApi hlt
  rwa [Real.cos_arccos (by linarith) (by linarith)] at this

/-- **Prop. 4.1, the strip inequality.** On the strip, `sin 2θ ≥ cos 2ρ`. -/
theorem sin_two_theta_ge {a θ : ℝ} (ha0 : 0 < a) (ha1 : a < 1)
    (hθ : |θ - Real.pi / 4| ≤ rho a) :
    Real.cos (2 * rho a) ≤ Real.sin (2 * θ) := by
  have hd : |2 * θ - Real.pi / 2| ≤ 2 * rho a := by
    have h : 2 * θ - Real.pi / 2 = 2 * (θ - Real.pi / 4) := by ring
    rw [h, abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith [hθ]
  have hsin : Real.sin (2 * θ) = Real.cos (2 * θ - Real.pi / 2) := by
    rw [Real.cos_sub_pi_div_two]
  rw [hsin, ← Real.cos_abs (2 * θ - Real.pi / 2)]
  have hnn : (0 : ℝ) ≤ |2 * θ - Real.pi / 2| := abs_nonneg _
  have hpi : 2 * rho a ≤ Real.pi := by
    have := two_rho_lt_pi_div_two ha0 ha1
    have hpi0 : (0 : ℝ) < Real.pi := Real.pi_pos
    linarith
  exact Real.cos_le_cos_of_nonneg_of_le_pi hnn hpi hd

/-- **Even + concave ⇒ the centre dominates.** -/
theorem le_of_concaveOn_symm {φ : ℝ → ℝ}
    (hφ : ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) φ) (hsym : φ (-1) = φ 1) :
    φ 1 ≤ φ 0 := by
  have h1 : (1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  have h2 : (-1 : ℝ) ∈ Set.Icc (-1 : ℝ) 1 := by constructor <;> norm_num
  have h := hφ.2 h1 h2 (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  simp only [smul_eq_mul] at h
  rw [show (1:ℝ)/2 * 1 + 1/2 * (-1) = 0 by ring] at h
  linarith [h, hsym]

/-! ### The `θ`-form of `G_r` -/

/-- `G_r` in angular coordinates: `v = sin²θ`. -/
theorem Gfun_theta (r : ℕ) (lam q θ : ℝ) (hr : 0 < r)
    (hc : 0 ≤ Real.cos θ) (hs : 0 ≤ Real.sin θ) :
    Gfun r lam q (Real.sin θ ^ 2)
      = binaryEntropy q / 2 + ∑ j ∈ Finset.range (r + 1),
          (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) *
            psi (lam * Real.log 2) ((j : ℝ) / r) θ := by
  have hR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  unfold Gfun psi Tang
  congr 1
  refine Finset.sum_congr rfl ?_
  intro j _
  have h1 : Real.sqrt (1 - Real.sin θ ^ 2) = Real.cos θ := by
    rw [show (1 : ℝ) - Real.sin θ ^ 2 = Real.cos θ ^ 2 by
      nlinarith [Real.sin_sq_add_cos_sq θ]]
    exact Real.sqrt_sq hc
  have h2 : Real.sqrt (Real.sin θ ^ 2) = Real.sin θ := Real.sqrt_sq hs
  have h3 : (2 : ℝ) ^ (-(lam * j) / r)
      = Real.exp (-(lam * Real.log 2 * ((j : ℝ) / r))) := by
    rw [two_rpow_eq_exp]; congr 1; field_simp; try ring
  have h4 : (2 : ℝ) ^ (-(lam * ((r : ℝ) - j)) / r)
      = Real.exp (-(lam * Real.log 2 * (1 - (j : ℝ) / r))) := by
    rw [two_rpow_eq_exp]; congr 1; field_simp; try ring
  rw [h1, h2, h3, h4]

/-! ### §4a Inside the strip

Paper Prop. 4.1 + (4.10). The 2-dimensional statement is reduced here to a
1-dimensional one by restricting `G_r` to the segment joining the centre
`(1/2, π/4)` to `(q, θ_v)`, extended to `t ∈ [-1,1]`; the involution
`(q,θ) ↦ (1-q, π/2-θ)` of `Gfun_symm` is exactly `t ↦ -t`, so the restriction
`segG` is an even function, and `le_of_concaveOn_symm` finishes.

What remains is `segG_concave`, the directional second-derivative bound
`d²/dt² ≤ 0`, i.e. `dq²G_qq + 2 dq dθ G_qθ + dθ² G_θθ ≤ 0`. All three
ingredients are proved above:
* `G_qq ≤ (a²-2)/ln2` from `psi_y2_le` + `second_difference_le` +
  `hasDerivAt_bern_second` + `bern_le_of_le` and `h'' ≤ -4/ln2`;
* `G_θθ ≤ -1/ln2` from `psi_theta2_le` + `bern_le_of_le`;
* `|G_qθ| ≤ a/(ln2·sin2θ)` from `psi_ytheta_le` + `hasDerivAt_bern`;
and the strip inequality `sin 2θ ≥ cos 2ρ > κ = a/√(2-a²)`
(`sin_two_theta_ge`, `kappa_lt_cos_two_rho`) makes the quadratic form
`(|dq|√(2-a²) - |dθ|)² ≥ 0` dominate it. Missing is only the bookkeeping that
assembles the termwise `HasDerivAt`s of `t ↦ G_r(q(t), θ(t))` into those three
sums. -/

/-- `G_r` restricted to the segment through the centre in direction
`(q - 1/2, θ_v - π/4)`, extended to `t ∈ [-1,1]`. -/
def segG (r : ℕ) (lam q v : ℝ) : ℝ → ℝ := fun t =>
  Gfun r lam (1 / 2 + t * (q - 1 / 2))
    (Real.sin (Real.pi / 4 + t * (thetaOf v - Real.pi / 4)) ^ 2)

lemma sin_thetaOf_sq {v : ℝ} (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    Real.sin (thetaOf v) ^ 2 = v := by
  unfold thetaOf
  rw [Real.sin_arcsin (by nlinarith [Real.sqrt_nonneg v]) ?_]
  · exact Real.sq_sqrt hv0
  · rw [show (1 : ℝ) = Real.sqrt 1 by simp]
    exact Real.sqrt_le_sqrt hv1

/-- `segG` at `t = 1` is the point under consideration. -/
lemma segG_one (r : ℕ) (lam q v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    segG r lam q v 1 = Gfun r lam q v := by
  unfold segG
  rw [show (1 : ℝ) / 2 + 1 * (q - 1 / 2) = q by ring,
    show Real.pi / 4 + 1 * (thetaOf v - Real.pi / 4) = thetaOf v by ring,
    sin_thetaOf_sq hv0 hv1]

/-- `segG` at `t = 0` is the centre. -/
lemma segG_zero (r : ℕ) (lam q v : ℝ) :
    segG r lam q v 0 = Gfun r lam (1 / 2) (1 / 2) := by
  unfold segG
  rw [show (1 : ℝ) / 2 + 0 * (q - 1 / 2) = 1 / 2 by ring,
    show Real.pi / 4 + 0 * (thetaOf v - Real.pi / 4) = Real.pi / 4 by ring]
  congr 1
  rw [Real.sin_pi_div_four]
  rw [div_pow, Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2)]
  norm_num

/-- **`segG` is even** — this is exactly `Gfun_symm`, the involution
`(q,θ) ↦ (1-q, π/2-θ)`. -/
lemma segG_neg_one (r : ℕ) (lam q v : ℝ) (hv0 : 0 ≤ v) (hv1 : v ≤ 1) :
    segG r lam q v (-1) = segG r lam q v 1 := by
  rw [segG_one r lam q v hv0 hv1]
  unfold segG
  rw [show (1 : ℝ) / 2 + (-1) * (q - 1 / 2) = 1 - q by ring,
    show Real.pi / 4 + (-1) * (thetaOf v - Real.pi / 4)
      = Real.pi / 2 - thetaOf v by ring, Real.sin_pi_div_two_sub]
  have hcos : Real.cos (thetaOf v) ^ 2 = 1 - v := by
    have h := Real.sin_sq_add_cos_sq (thetaOf v)
    have h2 := sin_thetaOf_sq hv0 hv1
    linarith [h, h2]
  rw [hcos, ← Gfun_symm]

/-! ## Bernstein basis and the two-parameter chain rule -/

private lemma HDA_congr' {f : ℝ → ℝ} {c d x : ℝ} (h : HasDerivAt f c x) (hcd : c = d) :
    HasDerivAt f d x := hcd ▸ h

private lemma hasDerivAt_bernBasis (r j : ℕ) (x : ℝ) :
    HasDerivAt (fun y : ℝ => (r.choose j : ℝ) * y ^ j * (1 - y) ^ (r - j))
      ((r.choose j : ℝ) *
        ((j : ℝ) * x ^ (j - 1) * (1 - x) ^ (r - j)
          - ((r - j : ℕ) : ℝ) * x ^ j * (1 - x) ^ (r - j - 1))) x := by
  have h := hasDerivAt_bernTerm r j (fun _ => (1 : ℝ)) x
  simpa using h

/-- The two-parameter chain rule for the Bernstein operator along a line. -/
private lemma hasDerivAt_bernFam (m : ℕ) (F : ℕ → ℝ → ℝ) (Fd : ℕ → ℝ)
    (x0 dx θ0 dθ t : ℝ)
    (hF : ∀ j, HasDerivAt (F j) (Fd j) (θ0 + t * dθ)) :
    HasDerivAt (fun s : ℝ => bern (m + 1) (fun j => F j (θ0 + s * dθ)) (x0 + s * dx))
      (dx * ((m + 1 : ℝ) * bern m (fwdDiff (fun j => F j (θ0 + t * dθ))) (x0 + t * dx))
        + dθ * bern (m + 1) Fd (x0 + t * dx)) t := by
  set xt := x0 + t * dx with hxt
  set θt := θ0 + t * dθ with hθt
  have hlin : HasDerivAt (fun s : ℝ => x0 + s * dx) dx t := by
    simpa using ((hasDerivAt_id t).mul_const dx).const_add x0
  have hlin2 : HasDerivAt (fun s : ℝ => θ0 + s * dθ) dθ t := by
    simpa using ((hasDerivAt_id t).mul_const dθ).const_add θ0
  have hfun : (fun s : ℝ => bern (m + 1) (fun j => F j (θ0 + s * dθ)) (x0 + s * dx))
      = ∑ j ∈ Finset.range (m + 1 + 1),
        (fun s : ℝ => (((m + 1).choose j : ℝ) * (x0 + s * dx) ^ j
            * (1 - (x0 + s * dx)) ^ (m + 1 - j)) * F j (θ0 + s * dθ)) := by
    funext s
    simp [bern, Finset.sum_apply, mul_assoc]
  rw [hfun]
  have hterm : ∀ j ∈ Finset.range (m + 1 + 1),
      HasDerivAt (fun s : ℝ => (((m + 1).choose j : ℝ) * (x0 + s * dx) ^ j
            * (1 - (x0 + s * dx)) ^ (m + 1 - j)) * F j (θ0 + s * dθ))
        ((dx * (((m + 1).choose j : ℝ) *
            ((j : ℝ) * xt ^ (j - 1) * (1 - xt) ^ (m + 1 - j)
              - ((m + 1 - j : ℕ) : ℝ) * xt ^ j * (1 - xt) ^ (m + 1 - j - 1)))) * F j θt
          + (((m + 1).choose j : ℝ) * xt ^ j * (1 - xt) ^ (m + 1 - j)) * (dθ * Fd j)) t := by
    intro j _
    have hA : HasDerivAt (fun s : ℝ => ((m + 1).choose j : ℝ) * (x0 + s * dx) ^ j
        * (1 - (x0 + s * dx)) ^ (m + 1 - j))
        (dx * (((m + 1).choose j : ℝ) *
            ((j : ℝ) * xt ^ (j - 1) * (1 - xt) ^ (m + 1 - j)
              - ((m + 1 - j : ℕ) : ℝ) * xt ^ j * (1 - xt) ^ (m + 1 - j - 1)))) t := by
      have h := (hasDerivAt_bernBasis (m + 1) j xt).comp t hlin
      exact HDA_congr' h (by ring)
    have hB : HasDerivAt (fun s : ℝ => F j (θ0 + s * dθ)) (dθ * Fd j) t := by
      have h := (hF j).comp t hlin2
      exact HDA_congr' h (by ring)
    exact hA.mul hB
  have hsum := HasDerivAt.sum hterm
  refine HDA_congr' hsum ?_
  have e1 : (∑ j ∈ Finset.range (m + 1 + 1),
      ((dx * (((m + 1).choose j : ℝ) *
            ((j : ℝ) * xt ^ (j - 1) * (1 - xt) ^ (m + 1 - j)
              - ((m + 1 - j : ℕ) : ℝ) * xt ^ j * (1 - xt) ^ (m + 1 - j - 1)))) * F j θt
          + (((m + 1).choose j : ℝ) * xt ^ j * (1 - xt) ^ (m + 1 - j)) * (dθ * Fd j)))
      = dx * (∑ j ∈ Finset.range (m + 1 + 1), ((m + 1).choose j : ℝ) * F j θt *
            ((j : ℝ) * xt ^ (j - 1) * (1 - xt) ^ (m + 1 - j)
              - ((m + 1 - j : ℕ) : ℝ) * xt ^ j * (1 - xt) ^ (m + 1 - j - 1)))
        + dθ * bern (m + 1) Fd xt := by
    rw [Finset.sum_add_distrib]
    congr 1
    · rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
    · unfold bern
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [e1, bern_deriv_sum m (fun j => F j θt) xt]

/-! ## Nonnegativity of the Bernstein operator -/

private lemma bern_nonneg (r : ℕ) (u : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : ∀ j, 0 ≤ u j) : 0 ≤ bern r u q := by
  unfold bern
  refine Finset.sum_nonneg ?_
  intro j _
  have h1 : (0 : ℝ) ≤ (r.choose j : ℝ) := by positivity
  have hcoeff : (0 : ℝ) ≤ (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) :=
    mul_nonneg (mul_nonneg h1 (pow_nonneg hq0 j)) (pow_nonneg (by linarith) _)
  exact mul_nonneg hcoeff (h j)

/-! ## A two-sided mean-value difference bound -/

private lemma diff_bound {g g' : ℝ → ℝ} (hd : ∀ y, HasDerivAt g (g' y) y)
    {A B : ℝ} (hlo : ∀ y, A ≤ g' y) (hhi : ∀ y, g' y ≤ B) {u w : ℝ} (huw : u < w) :
    A * (w - u) ≤ g w - g u ∧ g w - g u ≤ B * (w - u) := by
  obtain ⟨ξ, _, heq⟩ := exists_hasDerivAt_eq_slope g g' huw
    (fun s _ => (hd s).continuousAt.continuousWithinAt) (fun s _ => hd s)
  rw [eq_comm, div_eq_iff (by linarith : w - u ≠ 0)] at heq
  have h1 := hlo ξ
  have h2 := hhi ξ
  constructor <;> nlinarith [huw]

/-! ## The three second-derivative bounds -/

/-- (A) second differences of `ψ` in `y`. -/
private lemma boundA (m : ℕ) (aa θ x h : ℝ) (c : ℕ → ℝ) (hh : 0 < h)
    (hstep : ∀ j, c (j + 1) = c j + h)
    (hc : 0 < Real.cos θ) (hsn : 0 < Real.sin θ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    bern m (fwdDiff (fwdDiff (fun j => psi aa (c j) θ))) x ≤ (aa ^ 2 / Real.log 2) * h ^ 2 := by
  refine bern_le_of_le _ _ _ _ hx0 hx1 ?_
  intro j
  rw [fwdDiff_fwdDiff]
  have hd : ∀ y : ℝ, HasDerivAt (fun z : ℝ => psi aa z θ)
      (Ty aa y θ / (Tang aa y θ * Real.log 2)) y :=
    fun y => hasDerivAt_psi_y aa y θ (Tang_pos hc hsn)
  have hd' : ∀ y : ℝ, HasDerivAt (fun z : ℝ => Ty aa z θ / (Tang aa z θ * Real.log 2))
      ((aa ^ 2 * (Tang aa y θ) ^ 2 - (Ty aa y θ) ^ 2) / ((Tang aa y θ) ^ 2 * Real.log 2)) y :=
    fun y => hasDerivAt_psi_y2 aa y θ (Tang_pos hc hsn)
  have hM : ∀ y : ℝ, (aa ^ 2 * (Tang aa y θ) ^ 2 - (Ty aa y θ) ^ 2)
      / ((Tang aa y θ) ^ 2 * Real.log 2) ≤ aa ^ 2 / Real.log 2 :=
    fun y => psi_y2_le aa y θ (Tang_pos hc hsn)
  have key := second_difference_le hd hd' hM hh (c j)
  have e1 : c (j + 1) = c j + h := hstep j
  have e2 : c (j + 2) = c j + 2 * h := by
    have : c (j + 2) = c (j + 1 + 1) := by norm_num
    rw [this, hstep (j + 1), e1]; ring
  simp only [e1, e2]
  exact key

/-- (B) first differences of `ψ_θ` in `y`. -/
private lemma boundB (n : ℕ) (aa θ x h : ℝ) (c : ℕ → ℝ) (haa : 0 < aa) (hh : 0 < h)
    (hstep : ∀ j, c (j + 1) = c j + h)
    (hc : 0 < Real.cos θ) (hsn : 0 < Real.sin θ) (hsin2 : 0 < Real.sin (2 * θ))
    (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    0 ≤ bern n (fwdDiff (fun j => Tth aa (c j) θ / (Tang aa (c j) θ * Real.log 2))) x
      ∧ bern n (fwdDiff (fun j => Tth aa (c j) θ / (Tang aa (c j) θ * Real.log 2))) x
        ≤ (aa / (Real.log 2 * Real.sin (2 * θ))) * h := by
  have hlog2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have hd : ∀ y : ℝ, HasDerivAt (fun z : ℝ => Tth aa z θ / (Tang aa z θ * Real.log 2))
      (2 * aa * Real.exp (-aa) / ((Tang aa y θ) ^ 2 * Real.log 2)) y :=
    fun y => hasDerivAt_psi_ytheta aa y θ (Tang_pos hc hsn)
  have hlo : ∀ y : ℝ, (0 : ℝ) ≤ 2 * aa * Real.exp (-aa) / ((Tang aa y θ) ^ 2 * Real.log 2) := by
    intro y
    have hT : 0 < Tang aa y θ := Tang_pos hc hsn
    positivity
  have hhi : ∀ y : ℝ, 2 * aa * Real.exp (-aa) / ((Tang aa y θ) ^ 2 * Real.log 2)
      ≤ aa / (Real.log 2 * Real.sin (2 * θ)) :=
    fun y => psi_ytheta_le aa y θ haa hc hsn hsin2
  have hkey : ∀ j : ℕ,
      0 ≤ fwdDiff (fun j => Tth aa (c j) θ / (Tang aa (c j) θ * Real.log 2)) j
      ∧ fwdDiff (fun j => Tth aa (c j) θ / (Tang aa (c j) θ * Real.log 2)) j
        ≤ (aa / (Real.log 2 * Real.sin (2 * θ))) * h := by
    intro j
    have hlt : c j < c j + h := by linarith
    obtain ⟨h1, h2⟩ := diff_bound hd hlo hhi hlt
    have he : c j + h - c j = h := by ring
    rw [he] at h1 h2
    unfold fwdDiff
    simp only [hstep]
    exact ⟨by linarith, h2⟩
  exact ⟨bern_nonneg _ _ _ hx0 hx1 (fun j => (hkey j).1),
    bern_le_of_le _ _ _ _ hx0 hx1 (fun j => (hkey j).2)⟩

/-- (C) the pure `θ` second derivative. -/
private lemma boundC (r : ℕ) (aa θ x : ℝ) (c : ℕ → ℝ)
    (hc : 0 < Real.cos θ) (hsn : 0 < Real.sin θ) (hx0 : 0 ≤ x) (hx1 : x ≤ 1) :
    bern r (fun j => -((Tang aa (c j) θ) ^ 2 + (Tth aa (c j) θ) ^ 2) /
        ((Tang aa (c j) θ) ^ 2 * Real.log 2)) x ≤ -(1 / Real.log 2) :=
  bern_le_of_le _ _ _ _ hx0 hx1 (fun _ => psi_theta2_le _ _ _ (Tang_pos hc hsn))

/-! ## The entropy summand along the segment -/

private lemma hasDerivAt_entSeg (dq x0 t : ℝ) (h0 : x0 + t * dq ≠ 0) (h1 : x0 + t * dq ≠ 1) :
    HasDerivAt (fun s : ℝ => binaryEntropy (x0 + s * dq) / 2)
      (dq * (Real.log (1 - (x0 + t * dq)) - Real.log (x0 + t * dq)) / (2 * Real.log 2)) t := by
  have hlog2 : (0 : ℝ) < Real.log 2 := log_two_pos
  have hlin : HasDerivAt (fun s : ℝ => x0 + s * dq) dq t := by
    simpa using ((hasDerivAt_id t).mul_const dq).const_add x0
  have hb := (Real.hasDerivAt_binEntropy h0 h1).comp t hlin
  have hfun : (fun s : ℝ => binaryEntropy (x0 + s * dq) / 2)
      = fun s : ℝ => Real.binEntropy (x0 + s * dq) / Real.log 2 / 2 := by
    funext s; rfl
  rw [hfun]
  have h := (hb.div_const (Real.log 2)).div_const 2
  refine HDA_congr' h ?_
  field_simp

private lemma hasDerivAt_entSeg2 (dq x0 t : ℝ) (h0 : x0 + t * dq ≠ 0) (h1 : x0 + t * dq ≠ 1) :
    HasDerivAt
      (fun s : ℝ => dq * (Real.log (1 - (x0 + s * dq)) - Real.log (x0 + s * dq)) / (2 * Real.log 2))
      (dq ^ 2 * (-(1 / ((x0 + t * dq) * (1 - (x0 + t * dq))))) / (2 * Real.log 2)) t := by
  have hlog2 : (0 : ℝ) < Real.log 2 := log_two_pos
  set X := x0 + t * dq with hX
  have hne1 : (1 : ℝ) - X ≠ 0 := by
    intro hcon; exact h1 (by linarith)
  have hlin : HasDerivAt (fun s : ℝ => x0 + s * dq) dq t := by
    simpa using ((hasDerivAt_id t).mul_const dq).const_add x0
  have hlin' : HasDerivAt (fun s : ℝ => 1 - (x0 + s * dq)) (-dq) t := by
    simpa using hlin.const_sub 1
  have hA : HasDerivAt (fun s : ℝ => Real.log (1 - (x0 + s * dq))) (-dq / (1 - X)) t := by
    have := hlin'.log hne1
    exact HDA_congr' this (by ring)
  have hB : HasDerivAt (fun s : ℝ => Real.log (x0 + s * dq)) (dq / X) t := by
    have := hlin.log h0
    exact HDA_congr' this (by ring)
  have h := ((hA.sub hB).const_mul dq).div_const (2 * Real.log 2)
  refine HDA_congr' h ?_
  have hXne : X ≠ 0 := h0
  field_simp
  ring

/-! ## The `θ`-form of the segment and its continuity -/

private lemma segG_eq_aux (r : ℕ) (lam q v t : ℝ) (hr : 0 < r)
    (hc : 0 ≤ Real.cos (Real.pi / 4 + t * (thetaOf v - Real.pi / 4)))
    (hsn : 0 ≤ Real.sin (Real.pi / 4 + t * (thetaOf v - Real.pi / 4))) :
    segG r lam q v t
      = binaryEntropy (1 / 2 + t * (q - 1 / 2)) / 2
        + bern r (fun j => psi (lam * Real.log 2) ((j : ℝ) / (r : ℝ))
            (Real.pi / 4 + t * (thetaOf v - Real.pi / 4))) (1 / 2 + t * (q - 1 / 2)) := by
  unfold segG
  rw [Gfun_theta r lam _ _ hr hc hsn]
  rfl

private lemma continuousOn_segAux (r : ℕ) (aa dq dth : ℝ) (c : ℕ → ℝ) (S : Set ℝ)
    (hpos : ∀ t ∈ S, 0 < Real.cos (Real.pi / 4 + t * dth)
      ∧ 0 < Real.sin (Real.pi / 4 + t * dth)) :
    ContinuousOn (fun t : ℝ => binaryEntropy (1 / 2 + t * dq) / 2
      + bern r (fun j => psi aa (c j) (Real.pi / 4 + t * dth))
        (1 / 2 + t * dq)) S := by
  refine ContinuousOn.add ?_ ?_
  · have : Continuous (fun t : ℝ => binaryEntropy (1 / 2 + t * dq) / 2) := by
      unfold binaryEntropy
      fun_prop
    exact this.continuousOn
  · unfold bern
    refine continuousOn_finsetSum _ ?_
    intro j _
    refine ContinuousOn.mul (by fun_prop) ?_
    unfold psi logTwo
    refine ContinuousOn.div_const ?_ _
    refine ContinuousOn.log ?_ ?_
    · unfold Tang; fun_prop
    · intro t ht
      exact ne_of_gt (Tang_pos (hpos t ht).1 (hpos t ht).2)

/-! ## The sign of the second derivative -/

private lemma final_sign (aa K L dq dth X S A B C M M1 : ℝ)
    (hL : 0 < L) (hM : 0 < M) (hM1 : 0 ≤ M1) (hM1M : M1 ≤ M)
    (hX0 : 0 < X) (hX1 : X < 1) (hS : 0 < S)
    (hK2 : K ^ 2 = 2 - aa ^ 2) (_hKpos : 0 < K) (hKS : aa ≤ K * S)
    (hA : A ≤ aa ^ 2 / L * (1 / M) ^ 2)
    (hB0 : 0 ≤ B) (hB1 : B ≤ aa / (L * S) * (1 / M))
    (hC : C ≤ -(1 / L)) :
    dq ^ 2 * (-(1 / (X * (1 - X)))) / (2 * L) + dq ^ 2 * (M * M1) * A
      + 2 * (dq * dth * (M * B)) + dth ^ 2 * C ≤ 0 := by
  have hxx : 0 < X * (1 - X) := mul_pos hX0 (by linarith)
  have hxx4 : X * (1 - X) ≤ 1 / 4 := by nlinarith [sq_nonneg (X - 1 / 2)]
  have hinv : (4 : ℝ) ≤ 1 / (X * (1 - X)) := by rw [le_div_iff₀ hxx]; linarith
  have hE : dq ^ 2 * (-(1 / (X * (1 - X)))) / (2 * L) ≤ -(2 * dq ^ 2 / L) := by
    have h1 : dq ^ 2 * (-(1 / (X * (1 - X)))) ≤ dq ^ 2 * (-4) := by nlinarith [sq_nonneg dq]
    have h2 : dq ^ 2 * (-4) / (2 * L) = -(2 * dq ^ 2 / L) := by field_simp; ring
    have h3 : dq ^ 2 * (-(1 / (X * (1 - X)))) / (2 * L) ≤ dq ^ 2 * (-4) / (2 * L) := by
      rw [← sub_nonneg, ← sub_div]
      exact div_nonneg (by linarith) (by linarith)
    linarith
  have haaL : (0 : ℝ) ≤ aa ^ 2 / L := div_nonneg (sq_nonneg aa) hL.le
  have hT2 : dq ^ 2 * (M * M1) * A ≤ dq ^ 2 * (aa ^ 2 / L) := by
    have hco : (0 : ℝ) ≤ dq ^ 2 * (M * M1) := by positivity
    have h1 := mul_le_mul_of_nonneg_left hA hco
    refine le_trans h1 ?_
    have hval : dq ^ 2 * (M * M1) * (aa ^ 2 / L * (1 / M) ^ 2)
        = dq ^ 2 * (aa ^ 2 / L) * (M1 / M) := by
      field_simp
    rw [hval]
    have hfrac : M1 / M ≤ 1 := by rw [div_le_one hM]; linarith
    have hf0 : (0 : ℝ) ≤ M1 / M := div_nonneg hM1 hM.le
    have hnn : (0 : ℝ) ≤ dq ^ 2 * (aa ^ 2 / L) := mul_nonneg (sq_nonneg dq) haaL
    nlinarith [hnn, hfrac, hf0]
  have hBhi : M * B ≤ aa / (L * S) := by
    have h1 := mul_le_mul_of_nonneg_left hB1 hM.le
    have h2 : M * (aa / (L * S) * (1 / M)) = aa / (L * S) := by field_simp
    linarith
  have hBlo : (0 : ℝ) ≤ M * B := mul_nonneg hM.le hB0
  have haS : aa / (L * S) ≤ K / L := by
    rw [div_le_div_iff₀ (mul_pos hL hS) hL]
    nlinarith [mul_le_mul_of_nonneg_right hKS hL.le]
  have hcross : 2 * (dq * dth * (M * B)) ≤ 2 * (|dq| * |dth| * (K / L)) := by
    have hdd : dq * dth ≤ |dq| * |dth| := by
      have h := le_abs_self (dq * dth); rwa [abs_mul] at h
    have h1 : dq * dth * (M * B) ≤ |dq| * |dth| * (M * B) := by nlinarith [hBlo]
    have h2 : |dq| * |dth| * (M * B) ≤ |dq| * |dth| * (K / L) := by
      have h3 := le_trans hBhi haS
      nlinarith [mul_nonneg (abs_nonneg dq) (abs_nonneg dth)]
    linarith
  have hT4 : dth ^ 2 * C ≤ -(dth ^ 2 / L) := by
    have h1 := mul_le_mul_of_nonneg_left hC (sq_nonneg dth)
    have h2 : dth ^ 2 * (-(1 / L)) = -(dth ^ 2 / L) := by field_simp
    linarith
  have hmain : dq ^ 2 * (aa ^ 2 / L) + 2 * (|dq| * |dth| * (K / L))
      + (-(dth ^ 2 / L)) + (-(2 * dq ^ 2 / L)) ≤ 0 := by
    have hP2 : |dq| ^ 2 = dq ^ 2 := sq_abs dq
    have hQ2 : |dth| ^ 2 = dth ^ 2 := sq_abs dth
    rw [← hP2, ← hQ2]
    have ha2 : aa ^ 2 = 2 - K ^ 2 := by linarith
    rw [ha2]
    have hid : |dq| ^ 2 * ((2 - K ^ 2) / L) + 2 * (|dq| * |dth| * (K / L))
        + (-(|dth| ^ 2 / L)) + (-(2 * |dq| ^ 2 / L))
        = -((|dq| * K - |dth|) ^ 2 / L) := by
      field_simp
      ring
    rw [hid]
    have hnn : (0 : ℝ) ≤ (|dq| * K - |dth|) ^ 2 / L := div_nonneg (sq_nonneg _) hL.le
    linarith
  linarith [hE, hT2, hcross, hT4, hmain]

/-! ## The main theorem -/

/-- **The analytic core of Prop. 4.1**: the restriction of `G_r` to a
segment through the centre staying inside the strip is concave. See the section
comment for the three ingredient bounds. -/
theorem segG_concave (r : ℕ) (lam q v : ℝ) (hr : 2 ≤ r)
    (hpa0 : 0 < lam * Real.log 2) (hpa1 : lam * Real.log 2 < 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hs : inStrip lam v) :
    ConcaveOn ℝ (Set.Icc (-1 : ℝ) 1) (segG r lam q v) := by
  have hL : (0 : ℝ) < Real.log 2 := log_two_pos
  have hpi := Real.pi_pos
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨hv0, hv1⟩ := hv
  unfold inStrip at hs
  obtain ⟨m, rfl⟩ : ∃ m, r = m + 2 := ⟨r - 2, by omega⟩
  set a : ℝ := lam * Real.log 2 with ha
  set dq : ℝ := q - 1 / 2 with hdqd
  set dth : ℝ := thetaOf v - Real.pi / 4 with hdthd
  clear_value a dq dth
  have ha0 : 0 < a := hpa0
  have ha1 : a < 1 := hpa1
  have hdqabs : |dq| ≤ 1 / 2 := by rw [abs_le]; constructor <;> linarith
  have hrhopos : 0 < rho a := rho_pos ha0 ha1
  have hrho4 : rho a < Real.pi / 4 := by
    have := two_rho_lt_pi_div_two ha0 ha1; linarith
  -- angular facts
  have hth : ∀ t : ℝ, |t| ≤ 1 → |(Real.pi / 4 + t * dth) - Real.pi / 4| ≤ rho a := by
    intro t ht
    have he : (Real.pi / 4 + t * dth) - Real.pi / 4 = t * dth := by ring
    rw [he, abs_mul]
    have h1 : |t| * |dth| ≤ 1 * |dth| :=
      mul_le_mul_of_nonneg_right ht (abs_nonneg _)
    have h2 : |dth| ≤ rho a := hs
    linarith
  have hcos : ∀ t : ℝ, |t| ≤ 1 → 0 < Real.cos (Real.pi / 4 + t * dth) := by
    intro t ht
    have h := hth t ht
    rw [abs_le] at h
    have h1 : (Real.pi / 4 + t * dth) - Real.pi / 4 = t * dth := by ring
    rw [h1] at h
    refine Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hsin : ∀ t : ℝ, |t| ≤ 1 → 0 < Real.sin (Real.pi / 4 + t * dth) := by
    intro t ht
    have h := hth t ht
    rw [abs_le] at h
    have h1 : (Real.pi / 4 + t * dth) - Real.pi / 4 = t * dth := by ring
    rw [h1] at h
    refine Real.sin_pos_of_pos_of_lt_pi (by linarith) (by linarith)
  -- the strip inequality
  set K : ℝ := Real.sqrt (2 - a ^ 2) with hKd
  have hden : (0 : ℝ) < 2 - a ^ 2 := by nlinarith
  have hKpos : 0 < K := Real.sqrt_pos.2 hden
  have hK2 : K ^ 2 = 2 - a ^ 2 := Real.sq_sqrt hden.le
  clear_value K
  have hkap : kappaOf a = a / K := by
    have hnn : (0 : ℝ) < a / K := by positivity
    have hk : (0 : ℝ) ≤ kappaOf a := kappaOf_nonneg a
    have hsq : (kappaOf a) ^ 2 = (a / K) ^ 2 := by
      unfold kappaOf
      rw [Real.sq_sqrt (div_nonneg (sq_nonneg a) hden.le), div_pow, hK2]
    have hfac : (kappaOf a - a / K) * (kappaOf a + a / K) = 0 := by linear_combination hsq
    rcases mul_eq_zero.1 hfac with h | h
    · linarith
    · linarith
  have hSpos : ∀ t : ℝ, |t| ≤ 1 → 0 < Real.sin (2 * (Real.pi / 4 + t * dth)) := by
    intro t ht
    have hge := sin_two_theta_ge ha0 ha1 (hth t ht)
    have hklt := kappa_lt_cos_two_rho ha0 ha1
    have hk0 := kappaOf_nonneg a
    linarith
  have hKS : ∀ t : ℝ, |t| ≤ 1 → a ≤ K * Real.sin (2 * (Real.pi / 4 + t * dth)) := by
    intro t ht
    have hge := sin_two_theta_ge ha0 ha1 (hth t ht)
    have hklt := kappa_lt_cos_two_rho ha0 ha1
    rw [hkap] at hklt
    have hlt : a / K < Real.sin (2 * (Real.pi / 4 + t * dth)) := by linarith
    rw [div_lt_iff₀ hKpos] at hlt
    nlinarith [hlt]
  -- the index scaling
  obtain ⟨cc, hcc⟩ : ∃ cc : ℕ → ℝ, ∀ j : ℕ, cc j = (j : ℝ) / ((m : ℝ) + 2) :=
    ⟨_, fun _ => rfl⟩
  have hstep : ∀ j : ℕ, cc (j + 1) = cc j + 1 / ((m : ℝ) + 2) := by
    intro j; rw [hcc, hcc]; push_cast; ring
  have hMpos : (0 : ℝ) < (m : ℝ) + 2 := by positivity
  have hhpos : (0 : ℝ) < 1 / ((m : ℝ) + 2) := by positivity
  -- the θ-form
  have hseg : ∀ t : ℝ, |t| ≤ 1 → segG (m + 2) lam q v t
      = binaryEntropy (1 / 2 + t * dq) / 2
        + bern (m + 2) (fun j => psi a (cc j) (Real.pi / 4 + t * dth)) (1 / 2 + t * dq) := by
    intro t ht
    have hc' : 0 ≤ Real.cos (Real.pi / 4 + t * (thetaOf v - Real.pi / 4)) := by
      rw [← hdthd]; exact (hcos t ht).le
    have hs' : 0 ≤ Real.sin (Real.pi / 4 + t * (thetaOf v - Real.pi / 4)) := by
      rw [← hdthd]; exact (hsin t ht).le
    rw [segG_eq_aux (m + 2) lam q v t (by omega) hc' hs']
    rw [← hdqd, ← hdthd, ← ha]
    simp only [hcc]
    push_cast
    rfl
  -- x-range
  have hxle : ∀ t : ℝ, |t| ≤ 1 → 0 ≤ 1 / 2 + t * dq ∧ 1 / 2 + t * dq ≤ 1 := by
    intro t ht
    have h1 : |t * dq| ≤ 1 / 2 := by
      rw [abs_mul]
      have := mul_le_mul_of_nonneg_right ht (abs_nonneg dq)
      linarith
    rw [abs_le] at h1
    exact ⟨by linarith, by linarith⟩
  have hxlt : ∀ t : ℝ, |t| < 1 → 0 < 1 / 2 + t * dq ∧ 1 / 2 + t * dq < 1 := by
    intro t ht
    have h1 : |t * dq| < 1 / 2 := by
      rw [abs_mul]
      rcases eq_or_lt_of_le (abs_nonneg dq) with hz | hz
      · rw [← hz]; norm_num
      · have := mul_lt_mul_of_pos_right ht hz
        linarith
    rw [abs_lt] at h1
    exact ⟨by linarith, by linarith⟩
  refine concaveOn_of_hasDerivWithinAt2_nonpos (convex_Icc (-1 : ℝ) 1)
    (f' := fun t : ℝ =>
      dq * (Real.log (1 - (1 / 2 + t * dq)) - Real.log (1 / 2 + t * dq)) / (2 * Real.log 2)
      + (dq * (((m : ℝ) + 2) * bern (m + 1)
            (fwdDiff (fun j => psi a (cc j) (Real.pi / 4 + t * dth))) (1 / 2 + t * dq))
        + dth * bern (m + 2)
            (fun j => Tth a (cc j) (Real.pi / 4 + t * dth)
              / (Tang a (cc j) (Real.pi / 4 + t * dth) * Real.log 2)) (1 / 2 + t * dq)))
    (f'' := fun t : ℝ =>
      dq ^ 2 * (-(1 / ((1 / 2 + t * dq) * (1 - (1 / 2 + t * dq))))) / (2 * Real.log 2)
      + dq ^ 2 * (((m : ℝ) + 2) * ((m : ℝ) + 1)) * bern m
          (fwdDiff (fwdDiff (fun j => psi a (cc j) (Real.pi / 4 + t * dth)))) (1 / 2 + t * dq)
      + 2 * (dq * dth * (((m : ℝ) + 2) * bern (m + 1)
          (fwdDiff (fun j => Tth a (cc j) (Real.pi / 4 + t * dth)
            / (Tang a (cc j) (Real.pi / 4 + t * dth) * Real.log 2))) (1 / 2 + t * dq)))
      + dth ^ 2 * bern (m + 2)
          (fun j => -((Tang a (cc j) (Real.pi / 4 + t * dth)) ^ 2
              + (Tth a (cc j) (Real.pi / 4 + t * dth)) ^ 2)
            / ((Tang a (cc j) (Real.pi / 4 + t * dth)) ^ 2 * Real.log 2)) (1 / 2 + t * dq))
    ?_ ?_ ?_ ?_
  -- (i) continuity
  · refine ContinuousOn.congr
      (continuousOn_segAux (m + 2) a dq dth cc (Set.Icc (-1 : ℝ) 1) ?_) ?_
    · intro y hy
      have h : |y| ≤ 1 := abs_le.2 ⟨hy.1, hy.2⟩
      exact ⟨hcos y h, hsin y h⟩
    · intro y hy
      exact hseg y (abs_le.2 ⟨hy.1, hy.2⟩)
  -- (ii) the first derivative
  · intro t ht
    rw [interior_Icc] at ht
    have htle : |t| ≤ 1 := abs_le.2 ⟨ht.1.le, ht.2.le⟩
    have htlt : |t| < 1 := abs_lt.2 ⟨ht.1, ht.2⟩
    obtain ⟨hx0, hx1⟩ := hxlt t htlt
    have hclt := hcos t htle
    have hslt := hsin t htle
    have hd1 := hasDerivAt_entSeg dq (1 / 2) t (ne_of_gt hx0) (ne_of_lt hx1)
    have hF : ∀ j : ℕ, HasDerivAt (fun θ : ℝ => psi a (cc j) θ)
        (Tth a (cc j) (Real.pi / 4 + t * dth)
          / (Tang a (cc j) (Real.pi / 4 + t * dth) * Real.log 2)) (Real.pi / 4 + t * dth) :=
      fun j => hasDerivAt_psi_theta a (cc j) _ (Tang_pos hclt hslt)
    have hraw := hasDerivAt_bernFam (m + 1) (fun j θ => psi a (cc j) θ)
      (fun j => Tth a (cc j) (Real.pi / 4 + t * dth)
        / (Tang a (cc j) (Real.pi / 4 + t * dth) * Real.log 2))
      (1 / 2) dq (Real.pi / 4) dth t hF
    have hd2' : HasDerivAt
        (fun s : ℝ => bern (m + 2) (fun j => psi a (cc j) (Real.pi / 4 + s * dth))
          (1 / 2 + s * dq))
        (dq * ((((m + 1 : ℕ) : ℝ) + 1) * bern (m + 1)
              (fwdDiff (fun j => psi a (cc j) (Real.pi / 4 + t * dth))) (1 / 2 + t * dq))
          + dth * bern (m + 2)
              (fun j => Tth a (cc j) (Real.pi / 4 + t * dth)
                / (Tang a (cc j) (Real.pi / 4 + t * dth) * Real.log 2)) (1 / 2 + t * dq)) t :=
      hraw
    have hd2 : HasDerivAt
        (fun s : ℝ => bern (m + 2) (fun j => psi a (cc j) (Real.pi / 4 + s * dth))
          (1 / 2 + s * dq))
        (dq * (((m : ℝ) + 2) * bern (m + 1)
              (fwdDiff (fun j => psi a (cc j) (Real.pi / 4 + t * dth))) (1 / 2 + t * dq))
          + dth * bern (m + 2)
              (fun j => Tth a (cc j) (Real.pi / 4 + t * dth)
                / (Tang a (cc j) (Real.pi / 4 + t * dth) * Real.log 2)) (1 / 2 + t * dq)) t :=
      HDA_congr' hd2' (by push_cast; ring)

    have hsum := hd1.add hd2
    refine HasDerivWithinAt.congr hsum.hasDerivWithinAt ?_ (hseg t htle)
    intro y hy
    rw [interior_Icc] at hy
    exact hseg y (abs_le.2 ⟨hy.1.le, hy.2.le⟩)
  -- (iii) the second derivative
  · intro t ht
    rw [interior_Icc] at ht
    have htle : |t| ≤ 1 := abs_le.2 ⟨ht.1.le, ht.2.le⟩
    have htlt : |t| < 1 := abs_lt.2 ⟨ht.1, ht.2⟩
    obtain ⟨hx0, hx1⟩ := hxlt t htlt
    have hclt := hcos t htle
    have hslt := hsin t htle
    have hd1 := hasDerivAt_entSeg2 dq (1 / 2) t (ne_of_gt hx0) (ne_of_lt hx1)
    have hFa : ∀ j : ℕ, HasDerivAt (fun θ : ℝ => psi a (cc (j + 1)) θ - psi a (cc j) θ)
        (Tth a (cc (j + 1)) (Real.pi / 4 + t * dth)
            / (Tang a (cc (j + 1)) (Real.pi / 4 + t * dth) * Real.log 2)
          - Tth a (cc j) (Real.pi / 4 + t * dth)
            / (Tang a (cc j) (Real.pi / 4 + t * dth) * Real.log 2)) (Real.pi / 4 + t * dth) :=
      fun j => (hasDerivAt_psi_theta a (cc (j + 1)) _ (Tang_pos hclt hslt)).sub
        (hasDerivAt_psi_theta a (cc j) _ (Tang_pos hclt hslt))
    have hrawa := hasDerivAt_bernFam m (fun j θ => psi a (cc (j + 1)) θ - psi a (cc j) θ)
      (fun j => Tth a (cc (j + 1)) (Real.pi / 4 + t * dth)
            / (Tang a (cc (j + 1)) (Real.pi / 4 + t * dth) * Real.log 2)
          - Tth a (cc j) (Real.pi / 4 + t * dth)
            / (Tang a (cc j) (Real.pi / 4 + t * dth) * Real.log 2))
      (1 / 2) dq (Real.pi / 4) dth t hFa
    have hd2 : HasDerivAt
        (fun s : ℝ => dq * (((m : ℝ) + 2) * bern (m + 1)
          (fwdDiff (fun j => psi a (cc j) (Real.pi / 4 + s * dth))) (1 / 2 + s * dq)))
        (dq * (((m : ℝ) + 2) *
          (dq * (((m : ℝ) + 1) * bern m
              (fwdDiff (fwdDiff (fun j => psi a (cc j) (Real.pi / 4 + t * dth))))
              (1 / 2 + t * dq))
            + dth * bern (m + 1)
              (fwdDiff (fun j => Tth a (cc j) (Real.pi / 4 + t * dth)
                / (Tang a (cc j) (Real.pi / 4 + t * dth) * Real.log 2)))
              (1 / 2 + t * dq)))) t :=
      (hrawa.const_mul ((m : ℝ) + 2)).const_mul dq
    have hFb : ∀ j : ℕ,
        HasDerivAt (fun θ : ℝ => Tth a (cc j) θ / (Tang a (cc j) θ * Real.log 2))
        (-((Tang a (cc j) (Real.pi / 4 + t * dth)) ^ 2
              + (Tth a (cc j) (Real.pi / 4 + t * dth)) ^ 2)
            / ((Tang a (cc j) (Real.pi / 4 + t * dth)) ^ 2 * Real.log 2))
        (Real.pi / 4 + t * dth) :=
      fun j => hasDerivAt_psi_theta2 a (cc j) _ (Tang_pos hclt hslt)
    have hrawb := hasDerivAt_bernFam (m + 1)
      (fun j θ => Tth a (cc j) θ / (Tang a (cc j) θ * Real.log 2))
      (fun j => -((Tang a (cc j) (Real.pi / 4 + t * dth)) ^ 2
            + (Tth a (cc j) (Real.pi / 4 + t * dth)) ^ 2)
          / ((Tang a (cc j) (Real.pi / 4 + t * dth)) ^ 2 * Real.log 2))
      (1 / 2) dq (Real.pi / 4) dth t hFb
    have hd3' : HasDerivAt
        (fun s : ℝ => dth * bern (m + 2)
          (fun j => Tth a (cc j) (Real.pi / 4 + s * dth)
            / (Tang a (cc j) (Real.pi / 4 + s * dth) * Real.log 2)) (1 / 2 + s * dq))
        (dth * (dq * ((((m + 1 : ℕ) : ℝ) + 1) * bern (m + 1)
              (fwdDiff (fun j => Tth a (cc j) (Real.pi / 4 + t * dth)
                / (Tang a (cc j) (Real.pi / 4 + t * dth) * Real.log 2))) (1 / 2 + t * dq))
          + dth * bern (m + 2)
              (fun j => -((Tang a (cc j) (Real.pi / 4 + t * dth)) ^ 2
                    + (Tth a (cc j) (Real.pi / 4 + t * dth)) ^ 2)
                  / ((Tang a (cc j) (Real.pi / 4 + t * dth)) ^ 2 * Real.log 2))
              (1 / 2 + t * dq))) t :=
      hrawb.const_mul dth
    have hd3 : HasDerivAt
        (fun s : ℝ => dth * bern (m + 2)
          (fun j => Tth a (cc j) (Real.pi / 4 + s * dth)
            / (Tang a (cc j) (Real.pi / 4 + s * dth) * Real.log 2)) (1 / 2 + s * dq))
        (dth * (dq * (((m : ℝ) + 2) * bern (m + 1)
              (fwdDiff (fun j => Tth a (cc j) (Real.pi / 4 + t * dth)
                / (Tang a (cc j) (Real.pi / 4 + t * dth) * Real.log 2))) (1 / 2 + t * dq))
          + dth * bern (m + 2)
              (fun j => -((Tang a (cc j) (Real.pi / 4 + t * dth)) ^ 2
                    + (Tth a (cc j) (Real.pi / 4 + t * dth)) ^ 2)
                  / ((Tang a (cc j) (Real.pi / 4 + t * dth)) ^ 2 * Real.log 2))
              (1 / 2 + t * dq))) t :=
      HDA_congr' hd3' (by push_cast; ring)
    have hsum := hd1.add (hd2.add hd3)
    refine HasDerivAt.hasDerivWithinAt ?_
    exact HDA_congr' hsum (by ring)
  -- (iv) the sign
  · intro t ht
    rw [interior_Icc] at ht
    have htle : |t| ≤ 1 := abs_le.2 ⟨ht.1.le, ht.2.le⟩
    have htlt : |t| < 1 := abs_lt.2 ⟨ht.1, ht.2⟩
    obtain ⟨hx0, hx1⟩ := hxlt t htlt
    have hclt := hcos t htle
    have hslt := hsin t htle
    have hBb := boundB (m + 1) a (Real.pi / 4 + t * dth) (1 / 2 + t * dq)
      (1 / ((m : ℝ) + 2)) cc ha0 hhpos hstep hclt hslt (hSpos t htle) hx0.le hx1.le
    exact final_sign a K (Real.log 2) dq dth (1 / 2 + t * dq)
      (Real.sin (2 * (Real.pi / 4 + t * dth))) _ _ _ ((m : ℝ) + 2) ((m : ℝ) + 1)
      hL hMpos (by positivity) (by linarith) hx0 hx1 (hSpos t htle) hK2 hKpos (hKS t htle)
      (boundA m a (Real.pi / 4 + t * dth) (1 / 2 + t * dq) (1 / ((m : ℝ) + 2)) cc
        hhpos hstep hclt hslt hx0.le hx1.le)
      hBb.1 hBb.2
      (boundC (m + 2) a (Real.pi / 4 + t * dth) (1 / 2 + t * dq) cc hclt hslt hx0.le hx1.le)

/-- **Prop. 4.1 + (4.10)**: inside the strip the centre dominates. -/
theorem Gfun_le_center_strip (r : ℕ) (lam q v : ℝ) (hr : 2 ≤ r)
    (hpa0 : 0 < lam * Real.log 2) (hpa1 : lam * Real.log 2 < 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hs : inStrip lam v) :
    Gfun r lam q v ≤ Gfun r lam (1 / 2) (1 / 2) := by
  obtain ⟨hv0, hv1⟩ := hv
  have hconc := segG_concave r lam q v hr hpa0 hpa1 hq ⟨hv0, hv1⟩ hs
  have hsym := segG_neg_one r lam q v hv0 hv1
  have h := le_of_concaveOn_symm hconc hsym
  rwa [segG_one r lam q v hv0 hv1, segG_zero] at h

/-! ### §4b Building blocks for Prop. 4.2 -/

/-- **Paper (4.11), the polar identity.** `cos θ·A + sin θ·B = √(A²+B²) cos(θ-θ*)`
with `θ* = arctan(B/A)`; here `A = e^{-ay}`, `B = e^{-a(1-y)}`, so
`θ*(y) = arctan(e^{a(2y-1)})`. -/
theorem Tang_eq_polar (a y θ : ℝ) :
    Tang a y θ
      = Real.sqrt (Real.exp (-(a * y)) ^ 2 + Real.exp (-(a * (1 - y))) ^ 2) *
        Real.cos (θ - Real.arctan (Real.exp (-(a * (1 - y))) / Real.exp (-(a * y)))) := by
  set A := Real.exp (-(a * y)) with hA
  set B := Real.exp (-(a * (1 - y))) with hB
  have hApos : 0 < A := Real.exp_pos _
  have hBpos : 0 < B := Real.exp_pos _
  have hR2 : (0 : ℝ) < A ^ 2 + B ^ 2 := by positivity
  set R := Real.sqrt (A ^ 2 + B ^ 2) with hRdef
  have hRpos : 0 < R := Real.sqrt_pos.2 hR2
  have hRsq : R ^ 2 = A ^ 2 + B ^ 2 := Real.sq_sqrt hR2.le
  -- `√(1 + (B/A)²) = R / A`
  have hs : Real.sqrt (1 + (B / A) ^ 2) = R / A := by
    have he : (1 : ℝ) + (B / A) ^ 2 = (A ^ 2 + B ^ 2) / A ^ 2 := by
      field_simp
    rw [he, Real.sqrt_div' _ (by positivity), Real.sqrt_sq hApos.le]
  rw [Real.cos_sub, Real.cos_arctan, Real.sin_arctan, hs]
  unfold Tang
  field_simp
  ring

/-- `θ*(q) = arctan(e^{a(2q-1)})` moves at most at rate `a`:
`|θ*(q) - π/4| ≤ a|q - 1/2|` (the second bullet of Prop. 4.2). -/
theorem arctan_exp_sub_pi_div_four (t : ℝ) :
    |Real.arctan (Real.exp t) - Real.pi / 4| ≤ |t| / 2 := by
  have hd : ∀ x ∈ (Set.univ : Set ℝ),
      HasDerivWithinAt (fun s : ℝ => Real.arctan (Real.exp s))
        (Real.exp x * (1 / (1 + Real.exp x ^ 2))) Set.univ x := by
    intro x _
    have h := (Real.hasDerivAt_arctan (Real.exp x)).comp x (Real.hasDerivAt_exp x)
    exact (HDA_congr h (by ring)).hasDerivWithinAt
  have hbound : ∀ x ∈ (Set.univ : Set ℝ),
      ‖Real.exp x * (1 / (1 + Real.exp x ^ 2))‖ ≤ (1 : ℝ) / 2 := by
    intro x _
    have hx : (0 : ℝ) < Real.exp x := Real.exp_pos x
    have hden : (0 : ℝ) < 1 + Real.exp x ^ 2 := by positivity
    rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    rw [mul_one_div, div_le_div_iff₀ hden (by norm_num)]
    nlinarith [sq_nonneg (Real.exp x - 1)]
  have h := Convex.norm_image_sub_le_of_norm_hasDerivWithin_le hd hbound convex_univ
    (Set.mem_univ (0 : ℝ)) (Set.mem_univ t)
  rw [Real.exp_zero, Real.arctan_one] at h
  rw [Real.norm_eq_abs, Real.norm_eq_abs] at h
  calc |Real.arctan (Real.exp t) - Real.pi / 4| ≤ 1 / 2 * |t - 0| := h
    _ = |t| / 2 := by rw [sub_zero]; ring

/-- `-log cos x ≥ x²/2` on `[0, π/2)`: the convexity input that makes
`Δ_min(a) > 0` (and gives it an explicit quadratic lower bound). -/
theorem neg_log_cos_ge {x : ℝ} (hx0 : 0 ≤ x) (hx : x < Real.pi / 2) :
    x ^ 2 / 2 ≤ -Real.log (Real.cos x) := by
  set f : ℝ → ℝ := fun s => -Real.log (Real.cos s) - s ^ 2 / 2 with hfdef
  have hcos : ∀ s ∈ Set.Icc (0 : ℝ) x, 0 < Real.cos s := by
    intro s hs
    exact Real.cos_pos_of_mem_Ioo ⟨by linarith [hs.1, Real.pi_pos], by
      linarith [hs.2]⟩
  have hderiv : ∀ s ∈ Set.Icc (0 : ℝ) x,
      HasDerivAt f (Real.tan s - s) s := by
    intro s hs
    have hc := hcos s hs
    have h1 : HasDerivAt (fun t : ℝ => Real.log (Real.cos t))
        (-Real.sin s / Real.cos s) s := by
      have := (Real.hasDerivAt_cos s).log (ne_of_gt hc)
      exact HDA_congr this (by ring)
    have h2 : HasDerivAt (fun t : ℝ => t ^ 2 / 2) s s := by
      have h := (hasDerivAt_pow 2 s).div_const 2
      exact HDA_congr h (by norm_num)
    have := h1.neg.sub h2
    refine HDA_congr this ?_
    rw [Real.tan_eq_sin_div_cos]
    ring
  have hmono : MonotoneOn f (Set.Icc 0 x) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc 0 x)
      (fun s hs => (hderiv s hs).continuousAt.continuousWithinAt)
      (fun s hs => (hderiv s (interior_subset hs)).differentiableAt.differentiableWithinAt) ?_
    intro s hs
    rw [interior_Icc] at hs
    have hmem : s ∈ Set.Icc (0 : ℝ) x := ⟨hs.1.le, hs.2.le⟩
    rw [(hderiv s hmem).deriv]
    rcases eq_or_lt_of_le hs.1.le with h | h
    · rw [← h]; simp
    · have := Real.lt_tan h (by linarith [hs.2])
      linarith
  have h0 : f 0 = 0 := by simp [hfdef]
  have := hmono (Set.left_mem_Icc.2 hx0) (Set.right_mem_Icc.2 hx0) hx0
  rw [h0] at this
  simp only [hfdef] at this
  linarith

/-! ### §4c Outside the strip

Paper Prop. 4.2 + (4.12) + (4.14): the exact identity
`g₀(q,θ) = F_a(q)/2 + log₂ cos(θ - θ*(q))`, Lemma A's quadratic margin
(`LemmaA.Ffun_le_center`) for the first summand, `|θ*(q) - π/4| ≤ a|q - 1/2|`
for the second, the convexity excess `G_r ≤ g₀ + a²/(8r ln 2)`, and
`μ_r ≤ a⁴/(64 r² ln 2)`; at `λ ≤ 1.35` the numeric comparison
`a⁴/(64 r² ln 2) < Δ_min(a)` holds already at `r = 2`. -/
private lemma HDA {f : ℝ → ℝ} {c d x : ℝ} (h : HasDerivAt f c x) (hcd : c = d) :
    HasDerivAt f d x := hcd ▸ h

/-! ### Bernstein: elementary algebra -/

lemma bern_zero_deg (u : ℕ → ℝ) (q : ℝ) : bern 0 u q = u 0 := by
  unfold bern; simp

lemma bern_at_zero (r : ℕ) (u : ℕ → ℝ) : bern r u 0 = u 0 := by
  unfold bern
  have h := Finset.sum_eq_single (M := ℝ) (s := Finset.range (r + 1))
    (f := fun j => (r.choose j : ℝ) * (0 : ℝ) ^ j * (1 - (0 : ℝ)) ^ (r - j) * u j) 0
    (by intro j _ hj; simp [zero_pow hj])
    (by intro h; exact absurd (Finset.mem_range.2 (Nat.succ_pos r)) h)
  simpa using h

lemma bern_const (r : ℕ) (c q : ℝ) : bern r (fun _ => c) q = c := by
  have h : bern r (fun _ => c) q = c * bern r (fun _ => (1 : ℝ)) q := by
    unfold bern; rw [Finset.mul_sum]; exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [h, bern_one]; ring

lemma bern_add (r : ℕ) (u v : ℕ → ℝ) (q : ℝ) :
    bern r (fun j => u j + v j) q = bern r u q + bern r v q := by
  unfold bern; rw [← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun j _ => by ring)

lemma bern_smul (r : ℕ) (c : ℝ) (u : ℕ → ℝ) (q : ℝ) :
    bern r (fun j => c * u j) q = c * bern r u q := by
  unfold bern; rw [Finset.mul_sum]
  exact Finset.sum_congr rfl (fun j _ => by ring)

lemma bern_mono (r : ℕ) (u v : ℕ → ℝ) (q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (h : ∀ j, u j ≤ v j) : bern r u q ≤ bern r v q := by
  unfold bern
  refine Finset.sum_le_sum ?_
  intro j _
  have hc : (0 : ℝ) ≤ (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) := by
    have h1 : (0 : ℝ) ≤ (r.choose j : ℝ) := by positivity
    exact mul_nonneg (mul_nonneg h1 (pow_nonneg hq0 j)) (pow_nonneg (by linarith) _)
  exact mul_le_mul_of_nonneg_left (h j) hc

/-! ### Bernstein moments -/

/-- First moment: `B_r[j](q) = r q`. -/
lemma bern_M1 (r : ℕ) (q : ℝ) : bern r (fun j => (j : ℝ)) q = r * q := by
  cases r with
  | zero => rw [bern_zero_deg]; simp
  | succ m =>
    have hfd : fwdDiff (fun j : ℕ => (j : ℝ)) = fun _ => (1 : ℝ) := by
      funext j; unfold fwdDiff; push_cast; ring
    have hd : ∀ x : ℝ, HasDerivAt (bern (m + 1) (fun j : ℕ => (j : ℝ))) ((m : ℝ) + 1) x := by
      intro x
      have h := hasDerivAt_bern m (fun j : ℕ => (j : ℝ)) x
      rw [hfd, bern_one] at h
      exact HDA h (by ring)
    have hg : ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => bern (m + 1) (fun j : ℕ => (j : ℝ)) y - ((m : ℝ) + 1) * y)
          0 x := by
      intro x
      have h2 : HasDerivAt (fun y : ℝ => ((m : ℝ) + 1) * y) ((m : ℝ) + 1) x := by
        simpa using (hasDerivAt_id x).const_mul ((m : ℝ) + 1)
      exact HDA ((hd x).sub h2) (by ring)
    have hconst := is_const_of_deriv_eq_zero
      (f := fun y : ℝ => bern (m + 1) (fun j : ℕ => (j : ℝ)) y - ((m : ℝ) + 1) * y)
      (fun x => (hg x).differentiableAt) (fun x => (hg x).deriv) q 0
    simp only [mul_zero, sub_zero] at hconst
    rw [bern_at_zero] at hconst
    simp only [Nat.cast_zero] at hconst
    push_cast
    linarith

/-- Second factorial moment: `B_r[j(j-1)](q) = r(r-1) q²`. -/
lemma bern_M2 (r : ℕ) (q : ℝ) :
    bern r (fun j => (j : ℝ) * ((j : ℝ) - 1)) q = (r : ℝ) * ((r : ℝ) - 1) * q ^ 2 := by
  cases r with
  | zero => rw [bern_zero_deg]; simp
  | succ m =>
    have hfd : fwdDiff (fun j : ℕ => (j : ℝ) * ((j : ℝ) - 1)) = fun j : ℕ => 2 * (j : ℝ) := by
      funext j; unfold fwdDiff; push_cast; ring
    have hd : ∀ x : ℝ,
        HasDerivAt (bern (m + 1) (fun j : ℕ => (j : ℝ) * ((j : ℝ) - 1)))
          (((m : ℝ) + 1) * (2 * ((m : ℝ) * x))) x := by
      intro x
      have h := hasDerivAt_bern m (fun j : ℕ => (j : ℝ) * ((j : ℝ) - 1)) x
      rw [hfd] at h
      rw [bern_smul m 2 (fun j : ℕ => (j : ℝ)) x, bern_M1 m x] at h
      exact HDA h (by ring)
    have hg : ∀ x : ℝ,
        HasDerivAt (fun y : ℝ => bern (m + 1) (fun j : ℕ => (j : ℝ) * ((j : ℝ) - 1)) y
            - ((m : ℝ) + 1) * (m : ℝ) * y ^ 2) 0 x := by
      intro x
      have h2 : HasDerivAt (fun y : ℝ => ((m : ℝ) + 1) * (m : ℝ) * y ^ 2)
          (((m : ℝ) + 1) * (m : ℝ) * (2 * x)) x := by
        have := (hasDerivAt_pow 2 x).const_mul (((m : ℝ) + 1) * (m : ℝ))
        exact HDA this (by push_cast; ring)
      exact HDA ((hd x).sub h2) (by ring)
    have hconst := is_const_of_deriv_eq_zero
      (f := fun y : ℝ => bern (m + 1) (fun j : ℕ => (j : ℝ) * ((j : ℝ) - 1)) y
          - ((m : ℝ) + 1) * (m : ℝ) * y ^ 2)
      (fun x => (hg x).differentiableAt) (fun x => (hg x).deriv) q 0
    rw [bern_at_zero] at hconst
    simp only [Nat.cast_zero, zero_mul, zero_sub, ne_eq, OfNat.ofNat_ne_zero,
      not_false_eq_true, zero_pow, mul_zero, sub_zero] at hconst
    push_cast
    linarith

/-- `B_r[j/r](q) = q` for `r ≥ 1`. -/
lemma bern_mean (r : ℕ) (hr : 1 ≤ r) (q : ℝ) : bern r (fun j => (j : ℝ) / r) q = q := by
  have hR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h : (fun j : ℕ => (j : ℝ) / r) = fun j : ℕ => (1 / (r : ℝ)) * (j : ℝ) := by
    funext j; field_simp
  rw [h, bern_smul, bern_M1]
  field_simp

/-- The Bernstein variance `B_r[(j/r - q)²](q) = q(1-q)/r`. -/
lemma bern_var (r : ℕ) (hr : 1 ≤ r) (q : ℝ) :
    bern r (fun j => ((j : ℝ) / r - q) ^ 2) q = q * (1 - q) / r := by
  have hR : (r : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  have h : (fun j : ℕ => ((j : ℝ) / r - q) ^ 2)
      = fun j : ℕ => ((1 / (r : ℝ) ^ 2) * ((j : ℝ) * ((j : ℝ) - 1))
          + (1 / (r : ℝ) ^ 2 - 2 * q / r) * (j : ℝ)) + q ^ 2 := by
    funext j; field_simp; ring
  rw [h, bern_add, bern_add, bern_smul, bern_smul, bern_const, bern_M1, bern_M2]
  field_simp
  ring

lemma bern_quad (r : ℕ) (A B C q : ℝ) (w : ℕ → ℝ) :
    bern r (fun j => A + B * w j + C * w j ^ 2) q
      = A + B * bern r w q + C * bern r (fun j => w j ^ 2) q := by
  have h1 : bern r (fun j => A + B * w j + C * w j ^ 2) q
      = bern r (fun _ => A) q + bern r (fun j => B * w j) q
        + bern r (fun j => C * w j ^ 2) q := by
    unfold bern
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [h1, bern_const, bern_smul, bern_smul]

lemma bern_centered (r : ℕ) (hr : 1 ≤ r) (q : ℝ) :
    bern r (fun j => (j : ℝ) / r - q) q = 0 := by
  have h : bern r (fun j => (j : ℝ) / r - q) q
      = bern r (fun j => (j : ℝ) / r) q - bern r (fun _ => q) q := by
    unfold bern; rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl (fun j _ => by ring)
  rw [h, bern_mean r hr, bern_const]; ring

/-! ### Positivity of `T` on the closed quadrant -/

lemma Tang_pos' {a θ : ℝ} (hc : 0 ≤ Real.cos θ) (hsn : 0 ≤ Real.sin θ)
    (hne : 0 < Real.cos θ + Real.sin θ) (y : ℝ) : 0 < Tang a y θ := by
  unfold Tang
  have hE : (0 : ℝ) < Real.exp (-(a * y)) := Real.exp_pos _
  have hF : (0 : ℝ) < Real.exp (-(a * (1 - y))) := Real.exp_pos _
  rcases lt_or_eq_of_le hc with h | h
  · have h1 : 0 < Real.cos θ * Real.exp (-(a * y)) := by positivity
    have h2 : 0 ≤ Real.sin θ * Real.exp (-(a * (1 - y))) := by positivity
    linarith
  · have hs' : 0 < Real.sin θ := by linarith
    have h2 : 0 < Real.sin θ * Real.exp (-(a * (1 - y))) := by positivity
    nlinarith

/-! ### The one-sided Taylor bound in `y` -/

lemma psi_taylor (a θ q : ℝ) (hT : ∀ y : ℝ, 0 < Tang a y θ) (y : ℝ) :
    psi a y θ ≤ psi a q θ + (Ty a q θ / (Tang a q θ * Real.log 2)) * (y - q)
      + (a ^ 2 / (2 * Real.log 2)) * (y - q) ^ 2 := by
  have hL : (0 : ℝ) < Real.log 2 := log_two_pos
  set c : ℝ := Ty a q θ / (Tang a q θ * Real.log 2) with hc
  set f : ℝ → ℝ := fun x => psi a q θ + c * (x - q)
      + (a ^ 2 / (2 * Real.log 2)) * (x - q) ^ 2 - psi a x θ with hfdef
  set f1 : ℝ → ℝ := fun x => c + (a ^ 2 / Real.log 2) * (x - q)
      - Ty a x θ / (Tang a x θ * Real.log 2) with hf1def
  set f2 : ℝ → ℝ := fun x => a ^ 2 / Real.log 2
      - (a ^ 2 * (Tang a x θ) ^ 2 - (Ty a x θ) ^ 2) / ((Tang a x θ) ^ 2 * Real.log 2)
    with hf2def
  have hlin : ∀ x : ℝ, HasDerivAt (fun z : ℝ => z - q) (1 : ℝ) x := fun x =>
    (hasDerivAt_id x).sub_const q
  have hf : ∀ x : ℝ, HasDerivAt f (f1 x) x := by
    intro x
    have h1 : HasDerivAt (fun z : ℝ => c * (z - q)) c x := by
      have := (hlin x).const_mul c
      exact HDA this (by ring)
    have h2 : HasDerivAt (fun z : ℝ => (a ^ 2 / (2 * Real.log 2)) * (z - q) ^ 2)
        ((a ^ 2 / Real.log 2) * (x - q)) x := by
      have hp : HasDerivAt (fun z : ℝ => (z - q) ^ 2) (2 * (x - q)) x := by
        have := (hasDerivAt_pow 2 (x - q)).comp x (hlin x)
        exact HDA this (by push_cast; ring)
      have := hp.const_mul (a ^ 2 / (2 * Real.log 2))
      refine HDA this ?_
      field_simp
      try ring
    have h3 := hasDerivAt_psi_y a x θ (hT x)
    have := (((hasDerivAt_const x (psi a q θ)).add h1).add h2).sub h3
    exact HDA this (by simp [hf1def])
  have hf1 : ∀ x : ℝ, HasDerivAt f1 (f2 x) x := by
    intro x
    have h1 : HasDerivAt (fun z : ℝ => (a ^ 2 / Real.log 2) * (z - q))
        (a ^ 2 / Real.log 2) x := by
      have := (hlin x).const_mul (a ^ 2 / Real.log 2)
      exact HDA this (by ring)
    have h2 := hasDerivAt_psi_y2 a x θ (hT x)
    have := ((hasDerivAt_const x c).add h1).sub h2
    exact HDA this (by simp [hf2def])
  have hf2nn : ∀ x : ℝ, 0 ≤ f2 x := by
    intro x
    have := psi_y2_le a x θ (hT x)
    simp only [hf2def]
    linarith
  have hmono : Monotone f1 := by
    refine monotone_of_deriv_nonneg (fun x => (hf1 x).differentiableAt) ?_
    intro x
    rw [(hf1 x).deriv]
    exact hf2nn x
  have hf1q : f1 q = 0 := by simp [hf1def, hc]
  have hfq : f q = 0 := by simp [hfdef]
  have hgoal : 0 ≤ f y := by
    rcases lt_trichotomy y q with hlt | heq | hgt
    · obtain ⟨ξ, hξ, heq2⟩ := exists_hasDerivAt_eq_slope f f1 hlt
        (fun s _ => (hf s).continuousAt.continuousWithinAt) (fun s _ => hf s)
      have hξle : f1 ξ ≤ 0 := by
        have := hmono (le_of_lt hξ.2)
        rw [hf1q] at this; exact this
      have hden : (0 : ℝ) < q - y := by linarith
      rw [eq_comm, div_eq_iff (ne_of_gt hden)] at heq2
      rw [hfq] at heq2
      nlinarith
    · rw [heq, hfq]
    · obtain ⟨ξ, hξ, heq2⟩ := exists_hasDerivAt_eq_slope f f1 hgt
        (fun s _ => (hf s).continuousAt.continuousWithinAt) (fun s _ => hf s)
      have hξge : 0 ≤ f1 ξ := by
        have := hmono (le_of_lt hξ.1)
        rw [hf1q] at this; exact this
      have hden : (0 : ℝ) < y - q := by linarith
      rw [eq_comm, div_eq_iff (ne_of_gt hden)] at heq2
      rw [hfq] at heq2
      nlinarith
  simp only [hfdef] at hgoal
  linarith

/-- **The convexity excess (4.12).** -/
lemma bern_psi_le (r : ℕ) (hr : 1 ≤ r) (a θ q : ℝ) (hq0 : 0 ≤ q) (hq1 : q ≤ 1)
    (hT : ∀ y : ℝ, 0 < Tang a y θ) :
    bern r (fun j => psi a ((j : ℝ) / r) θ) q
      ≤ psi a q θ + (a ^ 2 / (2 * Real.log 2)) * (q * (1 - q) / r) := by
  have hle := bern_mono r (fun j => psi a ((j : ℝ) / r) θ)
    (fun j => psi a q θ + (Ty a q θ / (Tang a q θ * Real.log 2)) * ((j : ℝ) / r - q)
      + (a ^ 2 / (2 * Real.log 2)) * ((j : ℝ) / r - q) ^ 2) q hq0 hq1
    (fun j => psi_taylor a θ q hT _)
  rw [bern_quad r (psi a q θ) (Ty a q θ / (Tang a q θ * Real.log 2))
    (a ^ 2 / (2 * Real.log 2)) q (fun j => (j : ℝ) / r - q),
    bern_centered r hr, bern_var r hr] at hle
  linarith

/-! ### The numeric certificate -/

lemma cos_47_ge : (887 / 1000 : ℝ) ≤ Real.cos (47 / 100) := by
  have hx : |(47 / 100 : ℝ)| ≤ 1 := by
    rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 47/100)]; norm_num
  have h := Real.cos_bound hx
  rw [abs_of_nonneg (by norm_num : (0:ℝ) ≤ 47/100)] at h
  rw [abs_le] at h
  have h1 := h.1
  norm_num at h1 ⊢
  linarith

lemma kappaOf_le' {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 93575 / 100000) :
    Real.sqrt (a ^ 2 / (2 - a ^ 2)) ≤ 883 / 1000 := by
  have hden : (0 : ℝ) < 2 - a ^ 2 := by nlinarith
  rw [show (883 / 1000 : ℝ) = Real.sqrt ((883 / 1000) ^ 2) from
    (Real.sqrt_sq (by norm_num)).symm]
  apply Real.sqrt_le_sqrt
  rw [div_le_iff₀ hden]
  nlinarith

lemma rho_lower {a : ℝ} (ha0 : 0 < a) (ha : a ≤ 93575 / 100000) :
    (23265 / 100000 : ℝ) ≤ rho a := by
  unfold rho rhoCrit
  have hk := kappaOf_le' ha0 ha
  have hcos : (883 / 1000 : ℝ) ≤ Real.cos (47 / 100) := by linarith [cos_47_ge]
  have h1 : Real.arccos (Real.cos (47 / 100)) ≤ Real.arccos (Real.sqrt (a ^ 2 / (2 - a ^ 2))) :=
    Real.arccos_le_arccos (le_trans hk hcos)
  have h2 : Real.arccos (Real.cos (47 / 100)) = 47 / 100 :=
    Real.arccos_cos (by norm_num) (by linarith [Real.pi_gt_three])
  rw [h2] at h1
  linarith

lemma numeric_cert {a D rr E : ℝ} (ha0 : 0 < a) (ha : a ≤ 93575 / 100000)
    (hD0 : 0 ≤ D) (hD : D ≤ 1 / 2) (hrho : (23265 / 100000 : ℝ) ≤ rr)
    (hE0 : 0 ≤ E) (hE : rr - a * D ≤ E) :
    a ^ 4 / 256 ≤ (1 - a ^ 2) * D ^ 2 + E ^ 2 / 2 := by
  have hsq0 : (0 : ℝ) ≤ a ^ 2 := sq_nonneg a
  have hsq : a ^ 2 ≤ 8757 / 10000 := by nlinarith
  have ha4 : a ^ 4 / 256 ≤ 2996 / 1000000 := by nlinarith [hsq, hsq0]
  have ha2 : (1243 / 10000 : ℝ) ≤ 1 - a ^ 2 := by nlinarith
  by_cases hcase : (2486 / 10000 : ℝ) ≤ D
  · have hDsq : (2486 / 10000 : ℝ) ^ 2 ≤ D ^ 2 := by nlinarith
    nlinarith [sq_nonneg E]
  · have hcase' : D < 2486 / 10000 := lt_of_not_ge hcase
    have hlin : (0 : ℝ) ≤ 23265 / 100000 - 93575 / 100000 * D := by nlinarith
    have hEge : 23265 / 100000 - 93575 / 100000 * D ≤ E := by nlinarith
    have hEsq : (23265 / 100000 - 93575 / 100000 * D) ^ 2 ≤ E ^ 2 := by nlinarith
    have hquad : (2996 : ℝ) / 1000000
        ≤ 1243 / 10000 * D ^ 2 + (23265 / 100000 - 93575 / 100000 * D) ^ 2 / 2 := by
      nlinarith [sq_nonneg (D - 193637 / 1000000)]
    nlinarith

/-! ### The polar split (4.11) -/

lemma logTwo_mul {x y : ℝ} (hx : 0 < x) (hy : 0 < y) :
    logTwo (x * y) = logTwo x + logTwo y := by
  unfold logTwo
  rw [Real.log_mul (ne_of_gt hx) (ne_of_gt hy)]
  ring

lemma psi_split (a q θ : ℝ)
    (hcos : 0 < Real.cos (θ - Real.arctan (Real.exp (a * (2 * q - 1))))) :
    binaryEntropy q / 2 + psi a q θ
      = Ffun a q / 2 + logTwo (Real.cos (θ - Real.arctan (Real.exp (a * (2 * q - 1))))) := by
  have hstar : Real.exp (-(a * (1 - q))) / Real.exp (-(a * q)) = Real.exp (a * (2 * q - 1)) := by
    rw [← Real.exp_sub]; congr 1; ring
  have hE : Real.exp (-(a * q)) ^ 2 + Real.exp (-(a * (1 - q))) ^ 2
      = Real.exp (-(2 * a * q)) + Real.exp (-(2 * a * (1 - q))) := by
    rw [show Real.exp (-(a * q)) ^ 2 = Real.exp (-(a * q) + -(a * q)) by rw [Real.exp_add]; ring,
      show Real.exp (-(a * (1 - q))) ^ 2 = Real.exp (-(a * (1 - q)) + -(a * (1 - q))) by
        rw [Real.exp_add]; ring]
    congr 2 <;> ring
  set S : ℝ := Real.exp (-(2 * a * q)) + Real.exp (-(2 * a * (1 - q))) with hS
  have hSpos : 0 < S := by rw [hS]; positivity
  have hpolar := Tang_eq_polar a q θ
  rw [hstar, hE] at hpolar
  have hsqrt : 0 < Real.sqrt S := Real.sqrt_pos.2 hSpos
  have hp : psi a q θ = logTwo (Real.sqrt S)
      + logTwo (Real.cos (θ - Real.arctan (Real.exp (a * (2 * q - 1))))) := by
    unfold psi
    rw [hpolar, logTwo_mul hsqrt hcos]
  have hls : logTwo (Real.sqrt S) = logTwo S / 2 := by
    unfold logTwo; rw [Real.log_sqrt hSpos.le]; ring
  rw [hp, hls]
  unfold Ffun
  rw [← hS]
  ring

/-! ### Assembly -/

/-- **The quantified upper bound of §4.5–4.6(i)**, with no constraint on `λ`
beyond subcriticality `a = λ ln 2 ∈ (0,1)`.

There is a "rotation centre" `ts = arctan e^{a(2q-1)}` with
`|ts - π/4| ≤ a|q - ½|` such that

`G_r(q,v) ≤ 1 - λ/2 - ((1-a²)(q-½)² + (θ-ts)²/2)/ln2 + a²/(8r ln2)`,

where `θ = thetaOf v`.  This is Lemma A's margin (`Ffun_le_center`) plus the
polar split (`psi_split`, `Tang_eq_polar`) plus the Bernstein excess (4.12)
(`bern_psi_le`).  Both `Gfun_le_center_offstrip` (fixed `λ ≤ 1.35`) and the
quantified `DegeneracyLawQuant.Gfun_le_offstrip_quant` are corollaries; they
differ only in how the quadratic margin is compared with the centre defect. -/
theorem Gfun_le_center_margin (r : ℕ) (lam q v : ℝ) (hr : 2 ≤ r)
    (hpa0 : 0 < lam * Real.log 2) (hpa1 : lam * Real.log 2 < 1)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    ∃ ts : ℝ, |ts - Real.pi / 4| ≤ (lam * Real.log 2) * |q - 1 / 2| ∧
      Gfun r lam q v ≤ 1 - lam / 2
        - ((1 - (lam * Real.log 2) ^ 2) * (q - 1 / 2) ^ 2
            + (thetaOf v - ts) ^ 2 / 2) / Real.log 2
        + ((lam * Real.log 2) ^ 2 / (8 * (r : ℝ))) / Real.log 2 := by
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨hv0, hv1⟩ := hv
  have hL : (0 : ℝ) < Real.log 2 := log_two_pos
  have hLne : Real.log 2 ≠ 0 := ne_of_gt hL
  have hR2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hRpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hRne : (r : ℝ) ≠ 0 := ne_of_gt hRpos
  set a : ℝ := lam * Real.log 2 with hadef
  set θ : ℝ := thetaOf v with hθdef
  have ha0 : 0 < a := hpa0
  have ha1 : a < 1 := hpa1
  have hlamval : lam = a / Real.log 2 := by rw [hadef]; field_simp
  clear_value a θ
  -- angular coordinate
  have hθ0 : 0 ≤ θ := by rw [hθdef]; exact Real.arcsin_nonneg.2 (Real.sqrt_nonneg v)
  have hθ2 : θ ≤ Real.pi / 2 := by rw [hθdef]; exact Real.arcsin_le_pi_div_two _
  have hpi : (0 : ℝ) < Real.pi := Real.pi_pos
  have hsn : 0 ≤ Real.sin θ :=
    Real.sin_nonneg_of_nonneg_of_le_pi hθ0 (by linarith)
  have hcs : 0 ≤ Real.cos θ := Real.cos_nonneg_of_mem_Icc ⟨by linarith, hθ2⟩
  have hne : 0 < Real.cos θ + Real.sin θ := by
    nlinarith [Real.sin_sq_add_cos_sq θ, mul_nonneg hcs hsn]
  have hT : ∀ y : ℝ, 0 < Tang a y θ := Tang_pos' hcs hsn hne
  have hvsin : Real.sin θ ^ 2 = v := by rw [hθdef]; exact sin_thetaOf_sq hv0 hv1
  -- Step 3: the convexity excess
  have hGth := Gfun_theta r lam q θ (by omega) hcs hsn
  rw [hvsin, ← hadef] at hGth
  have hbernform : ∑ j ∈ Finset.range (r + 1),
      (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) * psi a ((j : ℝ) / r) θ
      = bern r (fun j => psi a ((j : ℝ) / r) θ) q := rfl
  rw [hbernform] at hGth
  have hexcess := bern_psi_le r (by omega) a θ q hq0 hq1 hT
  have hA : Gfun r lam q v ≤ binaryEntropy q / 2 + psi a q θ
      + (a ^ 2 / (2 * Real.log 2)) * (q * (1 - q) / r) := by
    rw [hGth]; linarith
  have hqq : q * (1 - q) ≤ 1 / 4 := by nlinarith [sq_nonneg (q - 1 / 2)]
  have hB : (a ^ 2 / (2 * Real.log 2)) * (q * (1 - q) / (r : ℝ))
      ≤ a ^ 2 / (8 * (r : ℝ) * Real.log 2) := by
    have heq : a ^ 2 / (8 * (r : ℝ) * Real.log 2)
        - (a ^ 2 / (2 * Real.log 2)) * (q * (1 - q) / (r : ℝ))
        = (a ^ 2 * (1 / 4 - q * (1 - q))) / (2 * (r : ℝ) * Real.log 2) := by
      field_simp; ring
    have hnn : (0 : ℝ) ≤ (a ^ 2 * (1 / 4 - q * (1 - q))) / (2 * (r : ℝ) * Real.log 2) := by
      apply div_nonneg _ (by positivity)
      nlinarith [sq_nonneg a]
    linarith
  -- Step 4: the polar split
  set ts : ℝ := Real.arctan (Real.exp (a * (2 * q - 1))) with htsdef
  have hts0 : 0 < ts := by
    rw [htsdef]
    exact Real.arctan_pos.2 (Real.exp_pos _)
  have hts2 : ts < Real.pi / 2 := by rw [htsdef]; exact Real.arctan_lt_pi_div_two _
  have hcospos : 0 < Real.cos (θ - ts) :=
    Real.cos_pos_of_mem_Ioo ⟨by linarith, by linarith⟩
  have hC := psi_split a q θ hcospos
  rw [← htsdef] at hC
  have hstarbd : |ts - Real.pi / 4| ≤ a * |q - 1 / 2| := by
    have h := arctan_exp_sub_pi_div_four (a * (2 * q - 1))
    rw [← htsdef] at h
    have hval : |a * (2 * q - 1)| / 2 = a * |q - 1 / 2| := by
      rw [abs_mul, abs_of_pos ha0,
        show (2 * q - 1) = 2 * (q - 1 / 2) by ring, abs_mul,
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
      ring
    linarith [h, hval.le, hval.ge]
  clear_value ts
  refine ⟨ts, hstarbd, ?_⟩
  -- Step 5a: Lemma A's margin
  have hFc : Ffun a (1 / 2) = 2 - lam := by
    unfold Ffun
    have hbin : binaryEntropy (1 / 2 : ℝ) = 1 := by
      unfold binaryEntropy
      rw [show (1 : ℝ) / 2 = 2⁻¹ by norm_num, Real.binEntropy_two_inv]
      field_simp
    have harg : Real.exp (-(2 * a * (1 / 2))) + Real.exp (-(2 * a * (1 - 1 / 2)))
        = 2 * Real.exp (-a) := by
      rw [show -(2 * a * (1 / 2 : ℝ)) = -a by ring,
        show -(2 * a * (1 - 1 / 2 : ℝ)) = -a by ring]
      ring
    rw [hbin, harg]
    unfold logTwo
    rw [Real.log_mul (by norm_num) (ne_of_gt (Real.exp_pos _)), Real.log_exp, hlamval]
    field_simp
    ring
  have hD1 : Ffun a q ≤ (2 - lam) - (2 * (1 - a ^ 2) / Real.log 2) * (q - 1 / 2) ^ 2 := by
    have h := Ffun_le_center a ha0 ha1 q ⟨hq0, hq1⟩
    rw [hFc] at h
    exact h
  -- Step 5b: the log-cos bound
  have habs : |θ - ts| < Real.pi / 2 := by
    rw [abs_lt]; constructor <;> linarith
  have hnl := neg_log_cos_ge (abs_nonneg (θ - ts)) habs
  rw [Real.cos_abs, sq_abs] at hnl
  have hE1 : logTwo (Real.cos (θ - ts)) ≤ -((θ - ts) ^ 2 / (2 * Real.log 2)) := by
    unfold logTwo
    rw [div_le_iff₀ hL]
    have hx : -((θ - ts) ^ 2 / (2 * Real.log 2)) * Real.log 2 = -((θ - ts) ^ 2 / 2) := by
      field_simp
    rw [hx]; linarith
  have heq : ((2 - lam) - (2 * (1 - a ^ 2) / Real.log 2) * (q - 1 / 2) ^ 2) / 2
      + -((θ - ts) ^ 2 / (2 * Real.log 2)) + a ^ 2 / (8 * (r : ℝ) * Real.log 2)
      = 1 - lam / 2 - ((1 - a ^ 2) * (q - 1 / 2) ^ 2 + (θ - ts) ^ 2 / 2) / Real.log 2
        + (a ^ 2 / (8 * (r : ℝ))) / Real.log 2 := by
    field_simp; ring
  linarith [hA, hB, hC, hD1, hE1, heq]

theorem Gfun_le_center_offstrip (r : ℕ) (lam q v : ℝ) (hr : 2 ≤ r)
    (hlam0 : 0 < lam) (hlam : lam ≤ 27 / 20)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1)
    (hs : ¬ inStrip lam v) :
    Gfun r lam q v ≤ Gfun r lam (1 / 2) (1 / 2) := by
  have hq' := hq
  have hv' := hv
  obtain ⟨hq0, hq1⟩ := hq
  obtain ⟨hv0, hv1⟩ := hv
  unfold inStrip at hs
  have hL : (0 : ℝ) < Real.log 2 := log_two_pos
  have hLlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hR2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hRpos : (0 : ℝ) < (r : ℝ) := by linarith
  have ha0 : 0 < lam * Real.log 2 := mul_pos hlam0 hL
  have ha : lam * Real.log 2 ≤ 93575 / 100000 := by nlinarith
  have ha1 : lam * Real.log 2 < 1 := by linarith
  obtain ⟨ts, hstarbd, hup⟩ := Gfun_le_center_margin r lam q v hr ha0 ha1 hq' hv'
  set a : ℝ := lam * Real.log 2 with hadef
  set θ : ℝ := thetaOf v with hθdef
  clear_value a θ
  have ha4nn : (0 : ℝ) ≤ a ^ 4 := by positivity
  -- Step 5c: the angular margin
  have hoff : rho a < |θ - Real.pi / 4| := not_le.1 hs
  have htri : |θ - Real.pi / 4| ≤ |θ - ts| + |ts - Real.pi / 4| :=
    abs_sub_le θ ts (Real.pi / 4)
  have hDbd : |q - 1 / 2| ≤ 1 / 2 := by
    rw [abs_le]; constructor <;> linarith
  have hcert : a ^ 4 / 256
      ≤ (1 - a ^ 2) * (q - 1 / 2) ^ 2 + (θ - ts) ^ 2 / 2 := by
    have h := numeric_cert (a := a) (D := |q - 1 / 2|) (rr := rho a) (E := |θ - ts|)
      ha0 ha (abs_nonneg _) hDbd (rho_lower ha0 ha) (abs_nonneg _)
      (by linarith)
    rw [sq_abs, sq_abs] at h
    exact h
  -- Step 6: the centre value from below
  have hcen : 1 - lam / 2
      + (a ^ 2 / (8 * (r : ℝ)) - a ^ 4 / (64 * (r : ℝ) ^ 2) + a ^ 4 / (96 * (r : ℝ) ^ 3))
        / Real.log 2
      ≤ Gfun r lam (1 / 2) (1 / 2) := by
    rw [Gfun_center_eq r lam (by omega)]
    unfold centerSum
    rw [← hadef]
    have h := centerSum_lower r lam (by omega)
    rw [← hadef] at h
    linarith
  -- Step 7: the numeric comparison
  have hrbnd : a ^ 4 / (64 * (r : ℝ) ^ 2) - a ^ 4 / (96 * (r : ℝ) ^ 3) ≤ a ^ 4 / 256 := by
    have hsq4 : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith
    have hr4 : (256 : ℝ) ≤ 64 * (r : ℝ) ^ 2 := by linarith
    have h1 : a ^ 4 / (64 * (r : ℝ) ^ 2) ≤ a ^ 4 / 256 := by
      rw [div_le_div_iff₀ (by positivity) (by norm_num : (0:ℝ) < 256)]
      exact mul_le_mul_of_nonneg_left hr4 ha4nn
    have h2 : (0 : ℝ) ≤ a ^ 4 / (96 * (r : ℝ) ^ 3) := by positivity
    linarith
  have hstep : -((1 - a ^ 2) * (q - 1 / 2) ^ 2 + (θ - ts) ^ 2 / 2) / Real.log 2
      + (a ^ 2 / (8 * (r : ℝ))) / Real.log 2
      ≤ (a ^ 2 / (8 * (r : ℝ)) - a ^ 4 / (64 * (r : ℝ) ^ 2) + a ^ 4 / (96 * (r : ℝ) ^ 3))
        / Real.log 2 := by
    rw [← sub_nonneg]
    have heq : (a ^ 2 / (8 * (r : ℝ)) - a ^ 4 / (64 * (r : ℝ) ^ 2)
          + a ^ 4 / (96 * (r : ℝ) ^ 3)) / Real.log 2
        - (-((1 - a ^ 2) * (q - 1 / 2) ^ 2 + (θ - ts) ^ 2 / 2) / Real.log 2
          + (a ^ 2 / (8 * (r : ℝ))) / Real.log 2)
        = (((1 - a ^ 2) * (q - 1 / 2) ^ 2 + (θ - ts) ^ 2 / 2)
            - (a ^ 4 / (64 * (r : ℝ) ^ 2) - a ^ 4 / (96 * (r : ℝ) ^ 3))) / Real.log 2 := by
      field_simp; ring
    rw [heq]
    apply div_nonneg _ hL.le
    linarith
  have hfin : 1 - lam / 2
      - ((1 - a ^ 2) * (q - 1 / 2) ^ 2 + (θ - ts) ^ 2 / 2) / Real.log 2
      + (a ^ 2 / (8 * (r : ℝ))) / Real.log 2
      = 1 - lam / 2
      + (-((1 - a ^ 2) * (q - 1 / 2) ^ 2 + (θ - ts) ^ 2 / 2) / Real.log 2
        + (a ^ 2 / (8 * (r : ℝ))) / Real.log 2) := by ring
  linarith [hup, hcen, hstep, hfin.le, hfin.ge]

/-- **The pointwise form of Lemma B**: the centre dominates on the whole box. -/
theorem Gfun_le_center (r : ℕ) (lam q v : ℝ) (hr : 2 ≤ r)
    (hlam0 : 0 < lam) (hlam : lam ≤ 27 / 20)
    (hq : q ∈ Set.Icc (0 : ℝ) 1) (hv : v ∈ Set.Icc (0 : ℝ) 1) :
    Gfun r lam q v ≤ Gfun r lam (1 / 2) (1 / 2) := by
  have hL : (0 : ℝ) < Real.log 2 := log_two_pos
  have hpa0 : 0 < lam * Real.log 2 := mul_pos hlam0 hL
  have hpa1 : lam * Real.log 2 < 1 := by
    have h9 := Real.log_two_lt_d9
    nlinarith [mul_nonneg (by linarith : (0:ℝ) ≤ 27 / 20 - lam) hL.le]
  by_cases hs : inStrip lam v
  · exact Gfun_le_center_strip r lam q v hr hpa0 hpa1 hq hv hs
  · exact Gfun_le_center_offstrip r lam q v hr hlam0 hlam hq hv hs

/-! ## §5 From the pointwise bound to the supremum -/

/-- The `sSup` step: a pointwise upper bound attained at an interior point of the
box identifies `supG`. -/
theorem supG_eq_center_of_le (r : ℕ) (lam : ℝ)
    (hle : ∀ q ∈ Set.Icc (0 : ℝ) 1, ∀ v ∈ Set.Icc (0 : ℝ) 1,
      Gfun r lam q v ≤ Gfun r lam (1 / 2) (1 / 2)) :
    supG r lam = Gfun r lam (1 / 2) (1 / 2) := by
  have hmemq : (1 / 2 : ℝ) ∈ Set.Icc (0 : ℝ) 1 := by constructor <;> norm_num
  have hmem : Gfun r lam (1 / 2) (1 / 2) ∈
      Set.image2 (Gfun r lam) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1) :=
    Set.mem_image2_of_mem hmemq hmemq
  have hub : ∀ x ∈ Set.image2 (Gfun r lam) (Set.Icc (0 : ℝ) 1) (Set.Icc (0 : ℝ) 1),
      x ≤ Gfun r lam (1 / 2) (1 / 2) := by
    rintro x ⟨q, hq, v, hv, rfl⟩
    exact hle q hq v hv
  unfold supG
  refine le_antisymm (csSup_le ⟨_, hmem⟩ hub) (le_csSup ⟨_, hub⟩ hmem)

/-- **Lemma B** (paper §4.7) at the Theorem-2 operating point `λ ≤ 1.35`,
where the threshold `r₀(λ)` equals `2`, so there are no finite exceptions. -/
theorem supG_eq_center (r : ℕ) (lam : ℝ) (hr : 2 ≤ r) (hlam0 : 0 < lam)
    (hlam : lam ≤ 27 / 20) :
    supG r lam = Gfun r lam (1 / 2) (1 / 2) :=
  supG_eq_center_of_le r lam fun q hq v hv =>
    Gfun_le_center r lam q v hr hlam0 hlam hq hv

end

end LemmaB
end DegeneracyLaw
