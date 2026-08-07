import SuperCritical

/-!
# Sharpness of the Gibbs threshold `λ* = 1/ln 2`

Strictly above the threshold the rescaled window diverges: for `λ ln 2 > 1`,
`r² · width_r → -∞`. Together with Theorem 1.3(a) below the threshold, this
places the phase transition of the method exactly at Gibbs weight `2^λ = e`.

The supercritical lower bound on `G_r` that drives the divergence is
`proofs/lib/SuperCritical.lean`.
-/

namespace DegeneracyLawSuper

open DegeneracyLaw DegeneracyLaw.LemmaB TwoDegenerateGraphs Filter Topology

noncomputable section

/-! ## §6 Sharpness of the threshold -/

/-- **Threshold sharpness (the design notes §6.7).**  The Gibbs threshold
`λ* = 1/ln 2` is sharp: strictly above it the rescaled window diverges to
`-∞` (this file), while at and below it the window is positive of order
`r^{-2}` — Theorem 1.3(a) for fixed `λ < λ*` and
`DegeneracyLawB.width_tuned_tendsto` at `λ*` itself (Theorem 1.3(b)). -/
theorem threshold_sharp (lam : ℝ) (ha : 1 / Real.log 2 < lam) :
    Tendsto (fun r : ℕ => (r : ℝ) ^ 2 * width r lam) atTop atBot := by
  have hL := logTwo_pos
  refine rsq_width_tendsto_atBot lam ?_
  have h := (div_lt_iff₀ hL).1 ha
  linarith


end

end DegeneracyLawSuper
