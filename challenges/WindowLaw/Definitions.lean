import Mathlib

/-!
# Definitions for the asymptotic window law

These mathematical definitions depend only on Mathlib.
The challenge and its solution import this same specification.
-/

namespace WindowLaw

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

/-- The **limiting window constant** `W(λ) = λ⁴ (log 2)³ / 64`. -/
def Wconst (lam : ℝ) : ℝ :=
  lam ^ 4 * Real.log 2 ^ 3 / 64

end

end WindowLaw
