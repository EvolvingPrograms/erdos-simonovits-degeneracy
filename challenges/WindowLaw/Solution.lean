import WindowLaw.Definitions
import Theorem13a

/-!
# Solution: the asymptotic window law

The statement below is supplied by the existing proof.
-/

namespace WindowLaw

open Filter
open scoped Topology

/-- For each **subcritical weight** `0 < λ < 1 / log 2`,
`r²` times the window width tends to `W(λ) = λ⁴ (log 2)³ / 64`. -/
theorem width_tendsto (lam : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam * Real.log 2 < 1) :
    Tendsto (fun r : ℕ => (r : ℝ) ^ 2 * width r lam) atTop (𝓝 (Wconst lam)) :=
  DegeneracyLaw.width_tendsto_unconditional_full lam hlam0 hlam1

end WindowLaw
