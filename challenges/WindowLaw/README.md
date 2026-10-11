# The asymptotic window law

For every fixed **subcritical weight** $\lambda>0$ with $\lambda\log 2<1$,

$$r^2\,\mathrm{width}(r,\lambda)
  \longrightarrow \frac{\lambda^4(\log 2)^3}{64}
  \qquad (r\to\infty).$$

The logarithm is natural; entropy is measured in bits. The window is the density
threshold minus the exclusion threshold. All quantities are defined in
[Definitions.lean](Definitions.lean), independently of the proof.

## Mathematics and Lean

| Mathematics | Lean expression |
| --- | --- |
| Binary entropy in bits $h(x)$ | `binaryEntropy x` |
| Gibbs objective $G_r(q,v)$ at weight $\lambda$ | `Gfun r lam q v` |
| $\sup_{(q,v)\in[0,1]^2} G_r(q,v)$ | `supG r lam` |
| Tuned radius $\tau_r=1/2-\lambda\log 2/(4r)$ | `tauOf r lam` |
| Exclusion threshold $A_r=\lambda\tau_r+\sup G_r$ | `Aside r lam` |
| Density threshold $C_r(\tau)=r h(\tau)-(r-1)$ | `Cside r tau` |
| Window $C_r(\tau_r)-A_r$ | `width r lam` |
| Limit $W(\lambda)=\lambda^4(\log 2)^3/64$ | `Wconst lam` |
| Convergence as $r\to\infty$ | `Tendsto ... atTop (𝓝 (Wconst lam))` |

The definition of `supG` uses `sSup` of the objective's image on the closed unit
square. The statement does not assume a maximizer as an extra hypothesis.

## Challenge and solution

The [challenge](Challenge.lean) keeps both subcriticality hypotheses explicit:

```lean
/-- For each **subcritical weight** `0 < λ < 1 / log 2`,
`r²` times the window width tends to `W(λ) = λ⁴ (log 2)³ / 64`. -/
theorem width_tendsto (lam : ℝ) (hlam0 : 0 < lam)
    (hlam1 : lam * Real.log 2 < 1) :
    Tendsto (fun r : ℕ => (r : ℝ) ^ 2 * width r lam) atTop (𝓝 (Wconst lam)) := by
  sorry
```

The [solution](Solution.lean) is supplied by
`DegeneracyLaw.width_tendsto_unconditional_full` in
[Theorem13a.lean](../../proofs/Theorem13a.lean).

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
