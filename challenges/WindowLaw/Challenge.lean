import WindowLaw.Definitions

/-!
# Challenge: the asymptotic window law

The placeholder specifies the statement that Comparator checks.
-/

namespace WindowLaw

open Filter
open scoped Topology

/-- For each **subcritical weight** `0 < λ < 1 / log 2`,
`r²` times the window width tends to `W(λ) = λ⁴ (log 2)³ / 64`. -/
theorem width_tendsto (lam : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam * Real.log 2 < 1) :
    Tendsto (fun r : ℕ => (r : ℝ) ^ 2 * width r lam) atTop (𝓝 (Wconst lam)) := by
  sorry

end WindowLaw
