import LedgerAsym

/-!
# Theorem 3(b): the exponent family law

Along the tuned schedule `λ_r = (1 - ln r / r)/ln 2` and the in-window family
`β_θ = A_r + θ · width_r`, the exponent gain certified by the method satisfies,
for every fixed `θ`,

  `8 r² · ε_r^max(β_θ) → 1 - θ`.

At the midpoint `θ = ½` this is `16 r² ε → 1`; as `θ → 0` the limit approaches
the supremal constant `1/8`, which by antitonicity of `ε^max` in `β`
(`DegeneracyLawB.epsMaxR_anti`, `lib/LedgerAsym.lean`) is the ceiling of the
method and is not attained.

The tuned schedule and its analytic input are `lib/LedgerTuned.lean`; the
`r(1 - β_r)` asymptotics that close the argument are `lib/LedgerAsym.lean`.
-/

namespace DegeneracyLawB

open Filter Topology DegeneracyLaw DegeneracyLedger TwoDegenerateGraphs

noncomputable section

/-- **The family law**: for every fixed `θ`, along the tuned sequence,
`8 r² ε^max_r(β_θ) → 1 - θ`.  At `θ = ½` this recovers
`sixteen_rsq_epsMax_tendsto'`; as `θ → 0` the limit approaches the supremal
constant `1/8`. -/
theorem eight_rsq_epsMax_theta_tendsto (theta : ℝ) :
    Tendsto (fun r : ℕ =>
      8 * (r : ℝ) ^ 2 * epsMaxR r (lamR r) (betaTheta r (lamR r) theta)) atTop
      (𝓝 (1 - theta)) := by
  have hL := logTwoPos
  have hne : (1 : ℝ) / (8 * Real.log 2) ≠ 0 := by positivity
  have hnum : Tendsto (fun r : ℕ =>
      8 * ((r : ℝ) ^ 2 * width r (lamR r)) * (1 - theta)) atTop
      (𝓝 (8 * (1 / (64 * Real.log 2)) * (1 - theta))) :=
    (width_tuned_tendsto.const_mul 8).mul_const _
  have hq := hnum.div (tendsto_r_one_sub_betaTheta theta) hne
  have hval : 8 * (1 / (64 * Real.log 2)) * (1 - theta) / (1 / (8 * Real.log 2))
      = 1 - theta := by
    field_simp
    ring
  rw [← hval]
  refine hq.congr' ?_
  filter_upwards [eventually_ge_atTop 1] with r hr
  simp only [Pi.div_apply]
  rw [epsMaxR, Cside_sub_betaTheta]
  ring

end

end DegeneracyLawB
