import AssemblySchedHost
import Theorem12

/-!
# Corollary 1.4: the two-tier counterexample

For every `δ ∈ (0,1)`, eventually in `r`, there is a connected bipartite
graph `H` of degeneracy exactly `r` and a constant `c > 0` with

  `c · n^(2 − 1/r + (1−δ)/(8 r²)) ≤ ex(n, H)`  for all large `n`.

The gain `(1 − δ)/(8 r²)` approaches the method's supremal constant
`1/(8 r²)` (Theorem 1.3(b)) up to the prescribed loss `δ`: the tuned schedule
`λ_r = (1 − ln r / r)/ln 2` recovers the ceiling that the fixed weight
`λ = 27/20` of Theorem 1.2 leaves by a factor of about `3.5`.

The pipeline is `proofs/lib/AssemblySchedHost.lean` (the host assembly at the
schedule parameters) over `proofs/lib/AssemblySched.lean` (the analytic layer);
this file only assembles the two eventual certificates.
-/

namespace RDegenerateGraphsTarget

open Filter SimpleGraph DegeneracyLawSched RAssemblySched

/-- **Corollary 1.4.**  For every `δ ∈ (0,1)` and every sufficiently large
`r`, a connected bipartite graph of degeneracy exactly `r` whose extremal
number exceeds `n^(2 − 1/r)` by the factor `n^((1−δ)/(8r²))`. -/
theorem twoTierExtremalCounterexample (delta : ℝ)
    (hd0 : 0 < delta) (hd1 : delta < 1) :
    ∀ᶠ r : ℕ in atTop,
      ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
        H.Connected ∧
        H.IsBipartite ∧
        IsDegenerate r H ∧
        ¬ IsDegenerate (r - 1) H ∧
        ∃ c : ℝ, 0 < c ∧
          ∀ᶠ n : ℕ in atTop,
            c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) +
                (1 - delta) / (8 * (r : ℝ) ^ 2)) ≤
              (SimpleGraph.extremalNumber n H : ℝ) := by
  filter_upwards [schedParams_admissible delta hd0, epsS_ge delta hd0,
    Filter.eventually_ge_atTop 2] with r hadm heps hr2
  obtain ⟨hw, hb0, hb1, -, -⟩ := hadm
  exact rDegenerateExtremalCounterexample_sched
    ⟨hr2, hd0, hd1, hw, hb0, hb1⟩ heps

end RDegenerateGraphsTarget
