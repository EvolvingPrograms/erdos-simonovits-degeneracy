import CompactnessAndDegeneracy

/-!
# Shared definitions for the all-r law (Theorems 2-3 of the paper)

Conventions (fixed for the whole campaign — do not change):
* Everything is in BITS, via `TwoDegenerateGraphs.binaryEntropy` and
  `TwoDegenerateGraphs.logTwo` (`= Real.log x / Real.log 2`).
* `a = λ · ln 2` never appears as a separate definition; write `lam * Real.log 2`.
* The window is `width r lam = Cside r (tauOf r lam) - Aside r lam`.

Paper reference: PAPER.md §§4-6. Lemma names below match the paper.
-/

namespace DegeneracyLaw

open TwoDegenerateGraphs Finset

noncomputable section

/-- The Gibbs objective `G_r(q,v)` in bits (paper (3.2), α = 1/2). -/
def Gfun (r : ℕ) (lam q v : ℝ) : ℝ :=
  binaryEntropy q / 2 +
    ∑ j ∈ range (r + 1),
      (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) *
        logTwo (Real.sqrt (1 - v) * 2 ^ (-(lam * j) / r) +
                Real.sqrt v * 2 ^ (-(lam * (r - j : ℝ)) / r))

/-- `sup_{(q,v) ∈ [0,1]²} G_r(q,v)`. -/
def supG (r : ℕ) (lam : ℝ) : ℝ :=
  sSup (Set.image2 (Gfun r lam) (Set.Icc 0 1) (Set.Icc 0 1))

/-- The tuned Hamming radius `τ_r = 1/2 - λ ln 2 / (4r)` (paper §6). -/
def tauOf (r : ℕ) (lam : ℝ) : ℝ := 1 / 2 - lam * Real.log 2 / (4 * r)

/-- `A_r = λ τ_r + sup G_r`. -/
def Aside (r : ℕ) (lam : ℝ) : ℝ := lam * tauOf r lam + supG r lam

/-- `C_r(τ) = r h(τ) - (r - 1)`. -/
def Cside (r : ℕ) (tau : ℝ) : ℝ := r * binaryEntropy tau - (r - 1)

/-- The feasibility window. -/
def width (r : ℕ) (lam : ℝ) : ℝ := Cside r (tauOf r lam) - Aside r lam

/-- The limiting window constant `W(λ) = λ⁴ ln³2 / 64` (paper Theorem 3(a)). -/
def Wconst (lam : ℝ) : ℝ := lam ^ 4 * Real.log 2 ^ 3 / 64

/-- The far-field function `F_a(q)` of Lemma A, in bits. -/
def Ffun (a q : ℝ) : ℝ :=
  binaryEntropy q +
    logTwo (Real.exp (-(2 * a * q)) + Real.exp (-(2 * a * (1 - q))))

/-- The center value of `G_r` as a binomial log-cosh sum (paper (6.6)):
`G_r(1/2,1/2) = 1 - λ/2 + E[log₂ cosh(a X /(2r))]`, `X = 2J - r`. -/
def centerSum (r : ℕ) (lam : ℝ) : ℝ :=
  1 - lam / 2 +
    ∑ j ∈ range (r + 1),
      (r.choose j : ℝ) * 2⁻¹ ^ r *
        logTwo (Real.cosh (lam * Real.log 2 * (2 * j - r : ℝ) / (2 * r)))

end

end DegeneracyLaw
