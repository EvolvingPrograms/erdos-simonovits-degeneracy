# The exponent family law

For every fixed $\theta\in\mathbb R$,

$$8r^2\,\varepsilon_r^{\max}(\beta_\theta)
  \longrightarrow 1-\theta
  \qquad (r\to\infty).$$

Here the weight varies with $r$:

$$\nu_r=\frac{\log r}{r},\qquad
  \lambda_r=\frac{1-\nu_r}{\log 2},\qquad
  \beta_\theta=A_r+\theta\,\mathrm{width}_r.$$

All thresholds and widths in this formula are evaluated at $\lambda_r$.
For $0<\theta<1$, the density parameter lies inside the window whenever the
window has positive width. The formal limit statement holds for **every real
$\theta$**, not only that interval. It concerns the method's defined exponent
gain; the graph counterexamples are separate statements.

## Mathematics and Lean

The entropy, objective, and threshold definitions follow the
[window law](../WindowLaw/README.md#mathematics-and-lean) and are stated explicitly
in this topic's [Definitions.lean](Definitions.lean).

| Mathematics | Lean expression |
| --- | --- |
| Maximal gain $(C_r(\tau_r)-\beta)/(r(1-\beta))$ | `epsMaxR r lam betaR` |
| Drift $\nu_r=\log r/r$ | `nuR r` |
| Tuned weight $\lambda_r=(1-\nu_r)/\log 2$ | `lamR r` |
| Density $\beta_\theta=A_r+\theta\,\mathrm{width}_r$ | `betaTheta r lam theta` |
| Every fixed $\theta\in\mathbb R$ | `(theta : ℝ)` |
| Limit $1-\theta$ as $r\to\infty$ | `Tendsto ... atTop (𝓝 (1 - theta))` |

At $\theta=1/2$, the conclusion is $16r^2\varepsilon_r^{\max}\to1$.

## Challenge and solution

The [challenge](Challenge.lean) shows the varying weight and density explicitly:

```lean
/-- For **every fixed** `θ ∈ ℝ`, the scaled exponent gain tends to `1 − θ`. -/
theorem eight_rsq_epsMax_tendsto (theta : ℝ) :
    Tendsto
      (fun r : ℕ =>
        8 * (r : ℝ) ^ 2 * epsMaxR r (lamR r) (betaTheta r (lamR r) theta))
      atTop (𝓝 (1 - theta)) := by
  sorry
```

The [solution](Solution.lean) is supplied by
`DegeneracyLawB.eight_rsq_epsMax_theta_tendsto` in
[Theorem13b.lean](../../proofs/Theorem13b.lean).

## Files and verification

[Definitions.lean](Definitions.lean) imports only Mathlib.
[Challenge.lean](Challenge.lean) states the specification using those definitions.
[Solution.lean](Solution.lean) imports the same definitions and supplies the
existing proof; it does not import the challenge or its placeholders.

[comparator.json](comparator.json) selects the theorem names and permits only
`propext`, `Classical.choice`, and `Quot.sound`. Comparator compares the
statements and their definitions, checks the proof dependencies, and replays
the proof through Lean's kernel. The `sorry` in the challenge marks the
statement to be checked; the solution must have no `sorryAx` dependency.

See [running all comparisons](../README.md#running-the-comparisons) for the CI
workflow and local commands.
