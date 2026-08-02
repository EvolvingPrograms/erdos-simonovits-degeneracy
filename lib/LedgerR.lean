import LawDefs

/-!
# The uniform ledger: arithmetic layer (paper §8, §9.2)

This file is the *arithmetic* layer of the uniform ledger of the design notes §8.  Every
statement takes the window `width r lam` as a **hypothesis**; nothing here proves
that the window is open.  That is Lemma C's job, and this file deliberately does
not import it (it re-proves its own copy of the entropy-defect bound, §2 below).

Contents.

* §1  Definitions mirroring §8: `betaMid`, `deltaR`, `sR`, `epsMaxR`, `epsR`.
* §2  A self-contained two-sided bound on `1 - h(1/2 - x)` (paper §5.2/§5.3).
      This intentionally duplicates `LemmaC.entGap`.
* §3  Lemma 8.3 **as corrected**: `epsMax_lower` gives `w / (2 K₁ r²)`, and the
      halving to `w / (4 K₁ r²)` happens exactly once, in `epsR_lower_half`.
* §4  `K1_bound`: the general form of hypothesis (W3).
* §5  The concrete corollary at `λ = 27/20`, `w = 0.00604`.

Reference: the design notes §§5.2–5.3, 8.0–8.4, 9.2.
-/

namespace DegeneracyLedger

open DegeneracyLaw TwoDegenerateGraphs Finset

noncomputable section

/-! ## §1 Definitions (paper §8.0–§8.4) -/

/-- The midpoint choice `β_r := ½(A_r + C_r)` of paper (8.1). -/
def betaMid (r : ℕ) (lam : ℝ) : ℝ := (Aside r lam + Cside r (tauOf r lam)) / 2

/-- The entropy slack `δ_r := (β_r - A_r)/4` of paper (8.2). -/
def deltaR (r : ℕ) (lam betaR : ℝ) : ℝ := (betaR - Aside r lam) / 4

/-- The number of layers `s(r) := ⌈2/width_r⌉ + 1` of paper (8.5). -/
def sR (r : ℕ) (lam : ℝ) : ℕ := ⌈2 / width r lam⌉₊ + 1

/-- `ε^max_r = (C_r - β_r) / (r (1 - β_r))`, paper §8.4. -/
def epsMaxR (r : ℕ) (lam betaR : ℝ) : ℝ :=
  (Cside r (tauOf r lam) - betaR) / ((r : ℝ) * (1 - betaR))

/-- `ε_r := (1 - η_r) ε^max_r`, paper §8.4. -/
def epsR (r : ℕ) (lam betaR eta : ℝ) : ℝ := (1 - eta) * epsMaxR r lam betaR

/-- At the midpoint, `C_r - β_r = width_r / 2` (paper (8.1)). -/
theorem betaMid_spec (r : ℕ) (lam : ℝ) :
    Cside r (tauOf r lam) - betaMid r lam = width r lam / 2 := by
  simp only [betaMid, width]; ring

/-- At the midpoint, `β_r - A_r = width_r / 2` (paper (8.1)). -/
theorem betaMid_spec' (r : ℕ) (lam : ℝ) :
    betaMid r lam - Aside r lam = width r lam / 2 := by
  simp only [betaMid, width]; ring

/-- `δ_r ≥ w/(8r²)` (paper (8.2)). -/
theorem deltaR_lower (r : ℕ) (lam betaR w : ℝ)
    (hbeta : betaR - Aside r lam = width r lam / 2)
    (hwidth : w / (r : ℝ) ^ 2 ≤ width r lam) :
    w / (8 * (r : ℝ) ^ 2) ≤ deltaR r lam betaR := by
  simp only [deltaR, hbeta]
  have h8 : w / (8 * (r : ℝ) ^ 2) = w / (r : ℝ) ^ 2 / 8 := by ring
  rw [h8]
  linarith [hwidth]

/-! ## §2 The entropy defect (own copy; paper §5.2–§5.3)

`entGap u = log 2 - binEntropy ((1-u)/2) = ∑_{k≥1} u^{2k}/(2k(2k-1))`, in nats.
-/

/-- `log 2 - binEntropy ((1-u)/2)`: the entropy deficit in nats. -/
def entGap (u : ℝ) : ℝ := Real.log 2 - Real.binEntropy ((1 - u) / 2)

theorem entGap_eq {u : ℝ} (h : |u| < 1) :
    entGap u = (1 - u) / 2 * Real.log (1 - u) + (1 + u) / 2 * Real.log (1 + u) := by
  have hu := abs_lt.1 h
  have h1 : (0 : ℝ) < 1 - u := by linarith [hu.2]
  have h2 : (0 : ℝ) < 1 + u := by linarith [hu.1]
  have e1 : Real.log ((1 - u) / 2) = Real.log (1 - u) - Real.log 2 := by
    rw [Real.log_div h1.ne' (by norm_num)]
  have e2 : Real.log (1 - (1 - u) / 2) = Real.log (1 + u) - Real.log 2 := by
    rw [show (1 : ℝ) - (1 - u) / 2 = (1 + u) / 2 by ring, Real.log_div h2.ne' (by norm_num)]
  simp only [entGap, Real.binEntropy, Real.log_inv, e1, e2]
  ring

/-- The all-positive power series of the entropy deficit (paper (5.2)). -/
theorem hasSum_entGap {u : ℝ} (h : |u| < 1) :
    HasSum (fun k : ℕ => u ^ (2 * k + 2) / ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)))
      (entGap u) := by
  have hu := abs_lt.1 h
  have h1 : (0 : ℝ) < 1 - u := by linarith [hu.2]
  have h2 : (0 : ℝ) < 1 + u := by linarith [hu.1]
  have hsq : |u ^ 2| < 1 := by
    rw [abs_pow]
    exact pow_lt_one₀ (abs_nonneg u) h (by norm_num)
  have hodd := (Real.hasSum_log_sub_log_of_abs_lt_one h).mul_left (u / 2)
  have heven := (Real.hasSum_pow_div_log_of_abs_lt_one hsq).mul_left (-(1 / 2) : ℝ)
  have hsum := hodd.add heven
  have hval : (u / 2) * (Real.log (1 + u) - Real.log (1 - u))
      + (-(1 / 2) : ℝ) * (-Real.log (1 - u ^ 2)) = entGap u := by
    rw [entGap_eq h, show (1 : ℝ) - u ^ 2 = (1 - u) * (1 + u) by ring,
      Real.log_mul h1.ne' h2.ne']
    ring
  rw [hval] at hsum
  have hfun : (fun k : ℕ => u ^ (2 * k + 2) / ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)))
      = fun k : ℕ => (u / 2) * ((2 : ℝ) * (1 / (2 * (k : ℝ) + 1)) * u ^ (2 * k + 1))
          + (-(1 / 2) : ℝ) * ((u ^ 2) ^ (k + 1) / ((k : ℝ) + 1)) := by
    funext k
    have hk1 : (2 * (k : ℝ) + 1) ≠ 0 := by positivity
    have hk2 : ((k : ℝ) + 1) ≠ 0 := by positivity
    have hp : (u ^ 2) ^ (k + 1) = u ^ (2 * k + 2) := by
      rw [← pow_mul]; ring_nf
    rw [hp]
    have hq : u ^ (2 * k + 2) = u ^ (2 * k + 1) * u := by rw [← pow_succ]
    rw [hq]
    field_simp
    ring
  rw [hfun]
  exact hsum

/-- Lower bound: the leading term (all terms of (5.2) are positive). -/
theorem entGap_lower {u : ℝ} (h : |u| < 1) : u ^ 2 / 2 ≤ entGap u := by
  have hs := hasSum_entGap h
  have := le_hasSum hs 0 (fun j _ => by
    have : (0 : ℝ) ≤ u ^ (2 * j + 2) := by
      rw [show 2 * j + 2 = 2 * (j + 1) by ring, pow_mul]
      positivity
    positivity)
  simpa using this

/-- Upper bound with the explicit geometric tail (paper (5.3)). -/
theorem entGap_upper {u : ℝ} (h : |u| < 1) :
    entGap u ≤ u ^ 2 / 2 + u ^ 4 / 12 + u ^ 6 / (30 * (1 - u ^ 2)) := by
  have hs := hasSum_entGap h
  have hu2 : u ^ 2 < 1 := by
    have : |u| ^ 2 < 1 := pow_lt_one₀ (abs_nonneg u) h (by norm_num)
    rwa [← abs_pow, abs_of_nonneg (sq_nonneg u)] at this
  have hu2' : (0 : ℝ) ≤ u ^ 2 := sq_nonneg u
  set f : ℕ → ℝ := fun k => u ^ (2 * k + 2) / ((2 * (k : ℝ) + 1) * (2 * (k : ℝ) + 2)) with hf
  have hsplit := hs.summable.sum_add_tsum_nat_add 2
  rw [hs.tsum_eq] at hsplit
  have hgeo : HasSum (fun k : ℕ => u ^ 6 / 30 * (u ^ 2) ^ k) (u ^ 6 / 30 * (1 - u ^ 2)⁻¹) :=
    (hasSum_geometric_of_lt_one hu2' hu2).mul_left _
  have hle : ∀ k : ℕ, f (k + 2) ≤ u ^ 6 / 30 * (u ^ 2) ^ k := by
    intro k
    have hpow : u ^ (2 * (k + 2) + 2) = u ^ 6 * (u ^ 2) ^ k := by
      rw [← pow_mul, ← pow_add]; ring_nf
    have hpos : (0 : ℝ) ≤ u ^ 6 * (u ^ 2) ^ k := by positivity
    have hd : (30 : ℝ) ≤ (2 * ((k : ℕ) + 2 : ℕ) + 1) * (2 * ((k : ℕ) + 2 : ℕ) + 2) := by
      push_cast
      nlinarith [Nat.cast_nonneg (α := ℝ) k]
    simp only [hf]
    rw [hpow]
    rw [div_le_iff₀ (by push_cast; positivity)]
    nlinarith [hpos, hd]
  have htail : ∑' k : ℕ, f (k + 2) ≤ u ^ 6 / 30 * (1 - u ^ 2)⁻¹ := by
    refine le_trans (Summable.tsum_le_tsum hle ((summable_nat_add_iff 2).2 hs.summable)
      hgeo.summable) ?_
    exact le_of_eq hgeo.tsum_eq
  have hfin : ∑ k ∈ range 2, f k = u ^ 2 / 2 + u ^ 4 / 12 := by
    simp [hf, Finset.sum_range_succ]
    ring
  have hE : entGap u = ∑ k ∈ range 2, f k + ∑' k : ℕ, f (k + 2) := hsplit.symm
  rw [hE, hfin]
  have hrw : u ^ 6 / (30 * (1 - u ^ 2)) = u ^ 6 / 30 * (1 - u ^ 2)⁻¹ := by
    rw [div_mul_eq_div_div]; ring
  rw [hrw]
  linarith [htail]

/-- The two-sided entropy-defect bound in **bits**, for `|x| ≤ 1/4`
(paper §5.2/§5.3).  This is the file's own copy of `LemmaC.binaryEntropy_gap_bounds`. -/
theorem binEntropy_defect_bounds {x : ℝ} (hx : |x| ≤ 1 / 4) :
    2 / Real.log 2 * x ^ 2 ≤ 1 - binaryEntropy (1 / 2 - x) ∧
      1 - binaryEntropy (1 / 2 - x) ≤ 2 / Real.log 2 * x ^ 2 + 3 / Real.log 2 * x ^ 4 := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have habs : |2 * x| < 1 := by
    rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 2)]
    linarith [hx]
  have hhalf : (1 : ℝ) / 2 - x = (1 - 2 * x) / 2 := by ring
  have hgap : 1 - binaryEntropy (1 / 2 - x) = entGap (2 * x) / Real.log 2 := by
    rw [hhalf]
    simp only [binaryEntropy, entGap]
    field_simp
  have hx2 : x ^ 2 ≤ 1 / 16 := by
    have := abs_le.1 hx
    nlinarith [this.1, this.2]
  have hu2 : (2 * x) ^ 2 ≤ 1 / 4 := by nlinarith [hx2]
  constructor
  · rw [hgap, le_div_iff₀ hlog]
    have hl := entGap_lower habs
    have hx' : (2 * x) ^ 2 / 2 = 2 * x ^ 2 := by ring
    rw [hx'] at hl
    calc 2 / Real.log 2 * x ^ 2 * Real.log 2 = 2 * x ^ 2 := by field_simp
      _ ≤ entGap (2 * x) := hl
  · rw [hgap, div_le_iff₀ hlog]
    have hub := entGap_upper habs
    have hden : (0 : ℝ) < 1 - (2 * x) ^ 2 := by nlinarith [hu2]
    have htail : (2 * x) ^ 6 / (30 * (1 - (2 * x) ^ 2)) ≤ 4 * x ^ 4 / 3 := by
      rw [div_le_div_iff₀ (by nlinarith [hden]) (by norm_num)]
      nlinarith [hx2, hden, sq_nonneg x, pow_nonneg (sq_nonneg x) 2,
        mul_nonneg (pow_nonneg (sq_nonneg x) 2) (sq_nonneg x)]
    have hmain : entGap (2 * x) ≤ 2 * x ^ 2 + 4 * x ^ 4 / 3 + 4 * x ^ 4 / 3 := by
      have e1 : (2 * x) ^ 2 / 2 = 2 * x ^ 2 := by ring
      have e2 : (2 * x) ^ 4 / 12 = 4 * x ^ 4 / 3 := by ring
      rw [e1, e2] at hub
      linarith [hub, htail]
    calc entGap (2 * x) ≤ 2 * x ^ 2 + 4 * x ^ 4 / 3 + 4 * x ^ 4 / 3 := hmain
      _ ≤ (2 / Real.log 2 * x ^ 2 + 3 / Real.log 2 * x ^ 4) * Real.log 2 := by
          field_simp
          nlinarith [pow_nonneg (sq_nonneg x) 2, sq_nonneg x]

/-! ## §3 Lemma 8.3, corrected (paper §8.4)

The paper's own erratum: `ε^max_r ≥ w/(2K₁r²)`, and the factor `(1-η_r) = ½`
of Theorem 2 is applied **once**, giving `ε_r ≥ w/(4K₁r²)`.
-/

/-- **Lemma 8.3 (corrected).**  Given the window lower bound `width_r ≥ w/r²`,
the midpoint condition `C_r - β_r = width_r/2`, and (W3) `r(1-β_r) ≤ K₁`,
the admissible exponent satisfies `ε^max_r ≥ w/(2K₁r²)`.

Note the single halving: the `1/2` comes from `C_r - β_r = width_r/2`, and
nothing else divides by two here. -/
theorem epsMax_lower (r : ℕ) (lam betaR w K1 : ℝ) (hr : 2 ≤ r)
    (hw : 0 ≤ w) (hK1 : 0 < K1) (hbpos : betaR < 1)
    (hwidth : w / (r : ℝ) ^ 2 ≤ width r lam)
    (hbeta : Cside r (tauOf r lam) - betaR = width r lam / 2)
    (hK : (r : ℝ) * (1 - betaR) ≤ K1) :
    w / (2 * K1 * (r : ℝ) ^ 2) ≤ epsMaxR r lam betaR := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hden : (0 : ℝ) < (r : ℝ) * (1 - betaR) := by
    have : (0 : ℝ) < 1 - betaR := by linarith
    positivity
  have hnum : w / (2 * (r : ℝ) ^ 2) ≤ Cside r (tauOf r lam) - betaR := by
    rw [hbeta]
    have : w / (r : ℝ) ^ 2 / 2 ≤ width r lam / 2 := by linarith
    calc w / (2 * (r : ℝ) ^ 2) = w / (r : ℝ) ^ 2 / 2 := by
          rw [div_div]; ring_nf
      _ ≤ width r lam / 2 := this
  have hK1ne : K1 ≠ 0 := ne_of_gt hK1
  have hrne : ((r : ℝ)) ^ 2 ≠ 0 := by positivity
  rw [epsMaxR, le_div_iff₀ hden]
  calc w / (2 * K1 * (r : ℝ) ^ 2) * ((r : ℝ) * (1 - betaR))
      ≤ w / (2 * K1 * (r : ℝ) ^ 2) * K1 :=
        mul_le_mul_of_nonneg_left hK (div_nonneg hw (by positivity))
    _ = w / (2 * (r : ℝ) ^ 2) := by field_simp; try ring
    _ ≤ _ := hnum

/-- Theorem 2's instance: `η_r = 1/2`, so `ε_r ≥ w/(4K₁r²)`.  The halving is
applied exactly once here, on top of `epsMax_lower`. -/
theorem epsR_lower_half (r : ℕ) (lam betaR w K1 : ℝ) (hr : 2 ≤ r)
    (hw : 0 ≤ w) (hK1 : 0 < K1) (hbpos : betaR < 1)
    (hwidth : w / (r : ℝ) ^ 2 ≤ width r lam)
    (hbeta : Cside r (tauOf r lam) - betaR = width r lam / 2)
    (hK : (r : ℝ) * (1 - betaR) ≤ K1) :
    w / (4 * K1 * (r : ℝ) ^ 2) ≤ epsR r lam betaR (1 / 2) := by
  have h := epsMax_lower r lam betaR w K1 hr hw hK1 hbpos hwidth hbeta hK
  simp only [epsR]
  have hK1ne : K1 ≠ 0 := ne_of_gt hK1
  have hrne : ((r : ℝ)) ^ 2 ≠ 0 := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    positivity
  have : w / (4 * K1 * (r : ℝ) ^ 2) = (1 - 1 / 2) * (w / (2 * K1 * (r : ℝ) ^ 2)) := by
    field_simp; try ring
  rw [this]
  exact mul_le_mul_of_nonneg_left h (by norm_num)

/-! ## §4 Hypothesis (W3): the `K₁` bound (paper §8.4) -/

/-- The `1 - β_r` decomposition of paper §8.4:
`1 - β_r = (1 - C_r) + width_r/2`. -/
theorem one_sub_beta_eq (r : ℕ) (lam betaR : ℝ)
    (hbeta : Cside r (tauOf r lam) - betaR = width r lam / 2) :
    1 - betaR = (1 - Cside r (tauOf r lam)) + width r lam / 2 := by
  linarith [hbeta]

/-- `1 - C_r(τ) = r (1 - h(τ))`. -/
theorem one_sub_Cside (r : ℕ) (tau : ℝ) :
    1 - Cside r tau = (r : ℝ) * (1 - binaryEntropy tau) := by
  simp only [Cside]; ring

/-- **The entropy-defect half of (W3).**  With `τ_r = 1/2 - λ ln2/(4r)`,
`r (1 - C_r) = r² (1 - h(τ_r)) ≤ λ² ln2 / 8 + 3 λ⁴ ln³2 / (256 r²)`. -/
theorem r_mul_one_sub_Cside_le (r : ℕ) (lam : ℝ) (hr : 2 ≤ r)
    (hlam0 : 0 ≤ lam) (hlam : lam * Real.log 2 ≤ 1) :
    (r : ℝ) * (1 - Cside r (tauOf r lam))
      ≤ lam ^ 2 * Real.log 2 / 8 + 3 * lam ^ 4 * Real.log 2 ^ 3 / (256 * (r : ℝ) ^ 2) := by
  have hlog : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  set x : ℝ := lam * Real.log 2 / (4 * (r : ℝ)) with hxdef
  have hx0 : 0 ≤ x := by
    have : 0 ≤ lam * Real.log 2 := mul_nonneg hlam0 hlog.le
    positivity
  have hxle : x ≤ 1 / 8 := by
    rw [hxdef, div_le_div_iff₀ (by positivity) (by norm_num)]
    nlinarith [hlam, hr0]
  have hxabs : |x| ≤ 1 / 4 := by
    rw [abs_of_nonneg hx0]; linarith
  have htau : tauOf r lam = 1 / 2 - x := by
    simp only [tauOf, hxdef]; try ring
  have hb := (binEntropy_defect_bounds hxabs).2
  have hmul : (r : ℝ) * ((r : ℝ) * (1 - binaryEntropy (1 / 2 - x)))
      ≤ (r : ℝ) ^ 2 * (2 / Real.log 2 * x ^ 2 + 3 / Real.log 2 * x ^ 4) := by
    have := mul_le_mul_of_nonneg_left hb (by positivity : (0:ℝ) ≤ (r:ℝ) ^ 2)
    nlinarith [this]
  have hxsq : x ^ 2 = lam ^ 2 * Real.log 2 ^ 2 / (16 * (r : ℝ) ^ 2) := by
    rw [hxdef]; field_simp; ring
  have hx4 : x ^ 4 = lam ^ 4 * Real.log 2 ^ 4 / (256 * (r : ℝ) ^ 4) := by
    rw [hxdef]; field_simp; ring
  have hrhs : (r : ℝ) ^ 2 * (2 / Real.log 2 * x ^ 2 + 3 / Real.log 2 * x ^ 4)
      = lam ^ 2 * Real.log 2 / 8 + 3 * lam ^ 4 * Real.log 2 ^ 3 / (256 * (r : ℝ) ^ 2) := by
    rw [hxsq, hx4]; field_simp; try ring
  calc (r : ℝ) * (1 - Cside r (tauOf r lam))
      = (r : ℝ) * ((r : ℝ) * (1 - binaryEntropy (1 / 2 - x))) := by
        rw [one_sub_Cside, htau]
    _ ≤ (r : ℝ) ^ 2 * (2 / Real.log 2 * x ^ 2 + 3 / Real.log 2 * x ^ 4) := hmul
    _ = _ := hrhs

/-- **(W3) in general form.**  Combining the entropy defect with an upper bound
`width_r ≤ wub/r²` on the window gives an explicit `K₁`. -/
theorem K1_bound (r : ℕ) (lam betaR wub : ℝ) (hr : 2 ≤ r)
    (hlam0 : 0 ≤ lam) (hlam : lam * Real.log 2 ≤ 1)
    (hbeta : Cside r (tauOf r lam) - betaR = width r lam / 2)
    (hwub : width r lam ≤ wub / (r : ℝ) ^ 2) :
    (r : ℝ) * (1 - betaR)
      ≤ lam ^ 2 * Real.log 2 / 8 + 3 * lam ^ 4 * Real.log 2 ^ 3 / (256 * (r : ℝ) ^ 2)
        + wub / (2 * (r : ℝ)) := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hent := r_mul_one_sub_Cside_le r lam hr hlam0 hlam
  have hdec := one_sub_beta_eq r lam betaR hbeta
  have hw : (r : ℝ) * (width r lam / 2) ≤ wub / (2 * (r : ℝ)) := by
    have : (r : ℝ) * (width r lam / 2) ≤ (r : ℝ) * ((wub / (r : ℝ) ^ 2) / 2) := by
      have := mul_le_mul_of_nonneg_left hwub hrpos.le
      linarith
    refine le_trans this (le_of_eq ?_)
    field_simp
    try ring
  calc (r : ℝ) * (1 - betaR)
      = (r : ℝ) * (1 - Cside r (tauOf r lam)) + (r : ℝ) * (width r lam / 2) := by
        rw [hdec]; ring
    _ ≤ _ := by linarith [hent, hw]

/-! ## §5 The concrete corollary at `λ = 27/20 = 1.35` (paper §9.2)

`w = 0.00604` (a rounding-down of the paper's `6.0387×10⁻³` of §5.5) and an
upper window bound `wub = 0.018` (the paper's `r² width_r ↑ W(1.35) = 0.017284`
from below, so any `wub ≥ W(1.35)` is safe).
-/

/-- Numeric `K₁` at `λ = 27/20` for `r ≥ 2`, from `K1_bound`:
`r(1-β_r) ≤ 0.1657`.  (The paper's sharp value is `0.1614`; the loss is the
`3λ⁴ln³2/(256r²)` tail and the `wub/(2r)` window term at `r = 2`.) -/
theorem K1_numeric (r : ℕ) (betaR : ℝ) (hr : 2 ≤ r)
    (hbeta : Cside r (tauOf r (27 / 20)) - betaR = width r (27 / 20) / 2)
    (hwub : width r (27 / 20) ≤ (0.018 : ℝ) / (r : ℝ) ^ 2) :
    (r : ℝ) * (1 - betaR) ≤ 0.1657 := by
  have hlog_lt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlog_gt : 0.6931471803 < Real.log 2 := Real.log_two_gt_d9
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hlam : (27 / 20 : ℝ) * Real.log 2 ≤ 1 := by nlinarith [hlog_lt]
  have h := K1_bound r (27 / 20) betaR 0.018 hr (by norm_num) hlam hbeta hwub
  have h1 : (27 / 20 : ℝ) ^ 2 * Real.log 2 / 8 ≤ 0.157908 := by nlinarith [hlog_lt]
  have h2 : 3 * (27 / 20 : ℝ) ^ 4 * Real.log 2 ^ 3 / (256 * (r : ℝ) ^ 2) ≤ 0.00325 := by
    have hc0 : Real.log 2 ^ 3 ≤ (0.6931471808 : ℝ) ^ 3 := by
      have hn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
      nlinarith [hlog_lt, hn, sq_nonneg (Real.log 2), mul_nonneg hn hn]
    have hcube : Real.log 2 ^ 3 ≤ 0.3331 := le_trans hc0 (by norm_num)
    have hden : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith [hr0]
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hcube, hden, Real.log_pos (by norm_num : (1:ℝ) < 2)]
  have h3 : (0.018 : ℝ) / (2 * (r : ℝ)) ≤ 0.0045 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hr0]
  linarith [h, h1, h2, h3]

/-- **Theorem 2's exponent, explicit.**  At `λ = 27/20`, given
`width_r ≥ 0.00604/r²` and `width_r ≤ 0.018/r²` for `r ≥ 2`, at the midpoint
`β_r`, the admissible exponent satisfies

  `ε^max_r ≥ 0.00604 / (2 · 0.1657 · r²) ≥ 1/(55 r²)`  and
  `ε_r = ½ ε^max_r ≥ 1/(110 r²)`.

The paper's §9.2 chain gives `1/(107 r²)` from the sharp `K₁ = 0.1614`; the
`1/110` here is what the self-contained `K1_numeric` (`K₁ ≤ 0.1657`) supports. -/
theorem eps_explicit (r : ℕ) (betaR : ℝ) (hr : 2 ≤ r) (hbpos : betaR < 1)
    (hwidth : (0.00604 : ℝ) / (r : ℝ) ^ 2 ≤ width r (27 / 20))
    (hwub : width r (27 / 20) ≤ (0.018 : ℝ) / (r : ℝ) ^ 2)
    (hbeta : Cside r (tauOf r (27 / 20)) - betaR = width r (27 / 20) / 2) :
    1 / (55 * (r : ℝ) ^ 2) ≤ epsMaxR r (27 / 20) betaR ∧
      1 / (110 * (r : ℝ) ^ 2) ≤ epsR r (27 / 20) betaR (1 / 2) := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hK := K1_numeric r betaR hr hbeta hwub
  have hmax := epsMax_lower r (27 / 20) betaR 0.00604 0.1657 hr (by norm_num) (by norm_num) hbpos
    hwidth hbeta hK
  have hhalf := epsR_lower_half r (27 / 20) betaR 0.00604 0.1657 hr (by norm_num) (by norm_num) hbpos
    hwidth hbeta hK
  constructor
  · refine le_trans ?_ hmax
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((r : ℝ))]
  · refine le_trans ?_ hhalf
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((r : ℝ))]

end

end DegeneracyLedger
