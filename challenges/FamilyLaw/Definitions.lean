import Mathlib

/-!
# Definitions for the exponent family law

These mathematical definitions depend only on Mathlib.
The challenge and its solution import this same specification.
-/

namespace FamilyLaw

open Finset

noncomputable section

/-- Base-2 logarithm. -/
def logTwo (x : ℝ) : ℝ := Real.log x / Real.log 2

/-- The **binary entropy** in bits. -/
def binaryEntropy (x : ℝ) : ℝ :=
  Real.binEntropy x / Real.log 2

/-- The **Gibbs objective** `Gᵣ(q, v)` in bits. -/
def Gfun (r : ℕ) (lam q v : ℝ) : ℝ :=
  binaryEntropy q / 2 +
    ∑ j ∈ range (r + 1),
      (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) *
        logTwo
          (Real.sqrt (1 - v) * 2 ^ (-(lam * j) / r) +
            Real.sqrt v * 2 ^ (-(lam * (r - j : ℝ)) / r))

/-- The **supremum of the Gibbs objective** `sup {Gᵣ(q, v) : (q, v) ∈ [0, 1]²}`. -/
def supG (r : ℕ) (lam : ℝ) : ℝ :=
  sSup (Set.image2 (Gfun r lam) (Set.Icc 0 1) (Set.Icc 0 1))

/-- The **tuned Hamming radius** `τᵣ = 1 / 2 − λ log 2 / (4 r)`. -/
def tauOf (r : ℕ) (lam : ℝ) : ℝ :=
  1 / 2 - lam * Real.log 2 / (4 * r)

/-- The **exclusion threshold** `Aᵣ = λ τᵣ + sup Gᵣ`. -/
def Aside (r : ℕ) (lam : ℝ) : ℝ :=
  lam * tauOf r lam + supG r lam

/-- The **density threshold** `Cᵣ(τ) = r h(τ) − (r − 1)`. -/
def Cside (r : ℕ) (tau : ℝ) : ℝ :=
  r * binaryEntropy tau - (r - 1)

/-- The **feasibility window** `Cᵣ(τᵣ) − Aᵣ`. -/
def width (r : ℕ) (lam : ℝ) : ℝ :=
  Cside r (tauOf r lam) - Aside r lam

/-- The method's **maximal exponent gain** at density parameter `β`. -/
def epsMaxR (r : ℕ) (lam betaR : ℝ) : ℝ :=
  (Cside r (tauOf r lam) - betaR) / ((r : ℝ) * (1 - betaR))

/-- The **drift rate** `νᵣ = log r / r`. -/
def nuR (r : ℕ) : ℝ :=
  Real.log r / r

/-- The **tuned Gibbs exponent** `λᵣ = (1 − νᵣ) / log 2`. -/
def lamR (r : ℕ) : ℝ :=
  (1 - nuR r) / Real.log 2

/-- The **density parameter** `βθ = Aᵣ + θ · widthᵣ`.
For `0 < θ < 1`, it lies inside the window whenever `widthᵣ > 0`. -/
def betaTheta (r : ℕ) (lam theta : ℝ) : ℝ :=
  Aside r lam + theta * width r lam

end

end FamilyLaw
