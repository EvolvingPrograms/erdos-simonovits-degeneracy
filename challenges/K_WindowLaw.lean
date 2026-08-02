import Mathlib

/-!
# Challenge 3: the asymptotic window law (Theorem 3(a))

Frozen statement file.  All quantities are defined from scratch, in bits.
Target theorem: for every fixed `λ > 0` with `λ ln 2 < 1`,

  `r² · (C_r(τ_r) - A_r(λ)) → λ⁴ ln³2 / 64`   as `r → ∞`,

where `C_r(τ) = r h(τ) - (r-1)` is the density threshold,
`A_r(λ) = λ τ_r + sup G_r` is the exclusion threshold with Gibbs objective
`G_r`, and `τ_r = 1/2 - λ ln 2/(4r)` is the tuned Hamming radius.
-/

namespace WindowLaw

open Filter Finset
open scoped Topology

noncomputable section

/-- Base-2 logarithm. -/
def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- Binary entropy in bits. -/
def binaryEntropy (x : ℝ) : ℝ :=
  Real.binEntropy x / Real.log 2

/-- The Gibbs objective `G_r(q,v)` in bits. -/
def Gfun (r : ℕ) (lam q v : ℝ) : ℝ :=
  binaryEntropy q / 2 +
    ∑ j ∈ range (r + 1),
      (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) *
        logTwo (Real.sqrt (1 - v) * 2 ^ (-(lam * j) / r) +
                Real.sqrt v * 2 ^ (-(lam * (r - j : ℝ)) / r))

/-- `sup_{(q,v) ∈ [0,1]²} G_r(q,v)`. -/
def supG (r : ℕ) (lam : ℝ) : ℝ :=
  sSup (Set.image2 (Gfun r lam) (Set.Icc 0 1) (Set.Icc 0 1))

/-- The tuned Hamming radius `τ_r = 1/2 - λ ln 2 / (4r)`. -/
def tauOf (r : ℕ) (lam : ℝ) : ℝ := 1 / 2 - lam * Real.log 2 / (4 * r)

/-- The exclusion threshold `A_r = λ τ_r + sup G_r`. -/
def Aside (r : ℕ) (lam : ℝ) : ℝ := lam * tauOf r lam + supG r lam

/-- The density threshold `C_r(τ) = r h(τ) - (r - 1)`. -/
def Cside (r : ℕ) (tau : ℝ) : ℝ := r * binaryEntropy tau - (r - 1)

/-- The feasibility window. -/
def width (r : ℕ) (lam : ℝ) : ℝ := Cside r (tauOf r lam) - Aside r lam

/-- The limiting window constant `W(λ) = λ⁴ ln³2 / 64`. -/
def Wconst (lam : ℝ) : ℝ := lam ^ 4 * Real.log 2 ^ 3 / 64

theorem width_tendsto (lam : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam * Real.log 2 < 1) :
    Tendsto (fun r : ℕ => (r : ℝ) ^ 2 * width r lam) atTop (𝓝 (Wconst lam)) := by
  sorry

end

end WindowLaw
