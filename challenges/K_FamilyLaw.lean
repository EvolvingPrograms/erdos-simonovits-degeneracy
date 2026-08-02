import Mathlib

/-!
# Challenge 4: the exponent family law (Theorem 3(b))

Frozen statement file.  All quantities are defined from scratch, in bits.
Along the tuned weight sequence `λ_r = (1 - ln r / r)/ln 2` and the
in-window family `β_θ = A_r + θ · width_r`, the method's maximal exponent
gain `ε_r^max(β) = (C_r - β)/(r(1 - β))` obeys, for every fixed `θ`,

  `8 r² · ε_r^max(β_θ) → 1 - θ`   as `r → ∞`.

At the midpoint `θ = 1/2` this gives `16 r² ε → 1` (the constant `1/16`);
as `θ → 0` the limit approaches the supremal constant `1/8`.
-/

namespace FamilyLaw

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

/-- The method's maximal exponent gain at density parameter `β`. -/
def epsMaxR (r : ℕ) (lam betaR : ℝ) : ℝ :=
  (Cside r (tauOf r lam) - betaR) / ((r : ℝ) * (1 - betaR))

/-- The drift rate `ν_r = ln r / r`. -/
def nuR (r : ℕ) : ℝ := Real.log r / r

/-- The tuned Gibbs exponent `λ_r = (1 - ν_r)/ln 2`. -/
def lamR (r : ℕ) : ℝ := (1 - nuR r) / Real.log 2

/-- `β_θ := A_r + θ · width_r`, the general in-window parameter. -/
def betaTheta (r : ℕ) (lam theta : ℝ) : ℝ :=
  Aside r lam + theta * width r lam

theorem eight_rsq_epsMax_tendsto (theta : ℝ) :
    Tendsto (fun r : ℕ =>
      8 * (r : ℝ) ^ 2 * epsMaxR r (lamR r) (betaTheta r (lamR r) theta)) atTop
      (𝓝 (1 - theta)) := by
  sorry

end

end FamilyLaw
