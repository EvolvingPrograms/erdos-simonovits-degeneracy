import FamilyLaw.Definitions
import Theorem13b

/-!
# Solution: the exponent family law

The statement below is supplied by the existing proof.
-/

namespace FamilyLaw

open Filter
open scoped Topology

/-- For **every fixed** `θ ∈ ℝ`, the scaled exponent gain tends to `1 − θ`. -/
theorem eight_rsq_epsMax_tendsto (theta : ℝ) :
    Tendsto
      (fun r : ℕ =>
        8 * (r : ℝ) ^ 2 * epsMaxR r (lamR r) (betaTheta r (lamR r) theta))
      atTop (𝓝 (1 - theta)) :=
  DegeneracyLawB.eight_rsq_epsMax_theta_tendsto theta

end FamilyLaw
