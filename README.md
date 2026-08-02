# The Erdős–Simonovits degeneracy conjecture fails at every level

**Claude Fable 5 and Claude Opus 5** · 2026-08-01 · Lean 4 + mathlib.
The default build targets contain no `sorry` (the four standalone
challenge statements of §8 intentionally end in one each and are
excluded); axioms used:
`propext, Classical.choice, Quot.sound`.

## 1. Main results

Let $\mathrm{ex}(n;H)$ denote the **extremal number** of $H$: the maximum
number of edges in an $n$-vertex graph containing no copy of $H$ as a
subgraph. A graph is **$r$-degenerate** if every nonempty vertex subset
contains a vertex with at most $r$ neighbours inside it; its
**degeneracy** is the least such $r$.

Erdős and Simonovits conjectured (Erdős problem #146, [Erd]) that
degeneracy governs extremal numbers of bipartite graphs: if $H$ is
bipartite and $r$-degenerate, then $\mathrm{ex}(n;H) = O(n^{2-1/r})$. The
best general upper bound in this direction is $\mathrm{ex}(n;H) =
O(n^{2-1/(4r)})$ [AKS03]. The conjecture was open until the case $r=2$
was refuted in 2026 [OAI26, ch. 10]. The present development proves,
machine-checked in Lean 4, that the conjecture fails for **every** $r$,
with a polynomial margin, and it determines exactly how large a margin
the method can give.

**Theorem 1 ($r=3$).** There is a connected bipartite graph $H$ of
degeneracy exactly $3$ and a constant $c>0$ such that
$$\mathrm{ex}(n;H)\ \ge\ c\,n^{5/3+1/160}\qquad\text{for all sufficiently large }n.$$

**Theorem 2 (every $r$).** For every $r\ge2$ there is a connected
bipartite graph $H_r$ of degeneracy exactly $r$ and a constant $c>0$ such
that
$$\boxed{\ \mathrm{ex}(n;H_r)\ \ge\ c\,n^{\,2-\frac1r+\frac{1}{28\,r^2}}\ }\qquad\text{for all sufficiently large }n.$$

The construction depends on two real parameters: a Hamming radius $\tau$
and a Gibbs weight $2^\lambda$ (§§3–4). Feasibility is governed by a
window $A_r(\lambda) < \beta < C_r(\tau)$ in a density parameter $\beta$,
and the exponent gain is proportional to the window's width. Theorem 3
determines the asymptotics of this window exactly.

**Theorem 3 (the asymptotic law).**
(a) For every fixed $\lambda$ with $\lambda\ln 2<1$, at the tuned radius
$\tau_r = \tfrac12 - \tfrac{\lambda\ln 2}{4r}$,
$$\lim_{r\to\infty}\ r^2\,\bigl(C_r-A_r\bigr)\ =\ \frac{\lambda^4\ln^32}{64},$$
while for $\lambda\ln2>1$ the rescaled width tends to $-\infty$. The
phase transition occurs exactly at Gibbs weight $2^\lambda=e$.

(b) Along the tuned schedule $\lambda_r=\frac{1-\ln r/r}{\ln2}$, the
exponent gain $\varepsilon_r^{\max}(\beta_\theta)$ certified at window
position $\beta_\theta=A_r+\theta\,(C_r-A_r)$ satisfies, for every fixed
$\theta\in(0,1)$,
$$\lim_{r\to\infty}\ 8\,r^2\,\varepsilon_r^{\max}(\beta_\theta)\ =\ 1-\theta .$$
Since $\varepsilon_r^{\max}$ is antitone in $\beta$ on the window, the
supremal constant of the method is $1/(8r^2)$, approached as
$\beta\to A_r^+$ and not attained; the midpoint $\theta=\tfrac12$ yields
$1/(16r^2)$.

Theorem 3(b) is what produces the explicit constants: it licenses running
the finite $r$ construction *near the exclusion edge* rather than at the
midpoint, which is where the $1/(28r^2)$ of Theorem 2 and the $1/160$ of
Theorem 1 come from (§9). Both strictly improve on the midpoint
evaluation of the same chain, retained as a checkpoint in §9.

Every statement above is literal in Lean. In particular "degeneracy
exactly $r$" is carried as `IsDegenerate r H ∧ ¬ IsDegenerate (r-1) H`,
and the exponents appear as written:

| | Lean declaration | File |
|---|---|---|
| Theorem 1 | `threeDegenerateExtremalCounterexample_sharp` | [`Theorem2.lean`](Theorem2.lean) |
| Theorem 2 | `rDegenerateExtremalCounterexample_exact` | [`Theorem2.lean`](Theorem2.lean) |
| Theorem 3(a) | `width_tendsto_unconditional_full` | [`Theorem3a.lean`](Theorem3a.lean) |
| Theorem 3(a), sharpness | `threshold_sharp` | [`Prop63.lean`](Prop63.lean) |
| Theorem 3(b), family law | `eight_rsq_epsMax_theta_tendsto` | [`lib/LedgerAsym.lean`](lib/LedgerAsym.lean) |
| Theorem 3(b), monotonicity | `epsMaxR_anti` | [`lib/LedgerAsym.lean`](lib/LedgerAsym.lean) |

Sections 2–5 give the proof in prose; §6 maps it to the Lean sources; §7
explains verification; §8 describes the frozen challenge statement; §9
derives the explicit constants.

## 2. Outline of the proof

A lower bound on $\mathrm{ex}(n;H_r)$ requires a single dense $n$-vertex
graph with no copy of $H_r$. The argument has three components:

1. a **forbidden graph** $H_r$ of degeneracy exactly $r$ (§3);
2. a **random host**: for a density parameter $\beta$ below a threshold
   $C_r(\tau)$, a sparsified Hamming graph retains
   $n^{2-1/r+\varepsilon}$ edges with positive probability (§3);
3. an **embedding obstruction**: an entropy argument showing that for
   $\beta$ above a threshold $A_r(\lambda)$, the retained host contains
   no copy of $H_r$ (§4).

The construction succeeds precisely when the window
$A_r(\lambda) < \beta < C_r(\tau)$ is nonempty for admissible
$(\tau,\lambda)$. Establishing its positivity for every $r$ is the
analytic core of the proof (§5); the width is of order $1/r^2$, and the
exponent gain $1/(28r^2)$ of Theorem 2 is proportional to it.

The framework generalizes the $r=2$ argument of [OAI26, ch. 10] in two
ways: the entire machine runs at general $r$ with uniform explicit
constants, and the Gibbs weight, which [OAI26] fixed numerically at $3$,
is left free and optimized. The optimization is not cosmetic: Theorem 3
shows the method has a sharp phase transition at weight $e$, and the
choice of window position drives the final constants (§9).

## 3. The forbidden graph and the host construction

**The forbidden graph.** $H_r$ is the layered $r$-subset graph. Let $V_0$ be a
finite set of roots and inductively $V_{i+1}=\binom{V_i}{r}$; each
$r$-subset ("child") is joined to its $r$ elements ("parents"). The
result is connected and bipartite (odd layers versus even layers).

**Degeneracy.** Peeling from the top layer downward, every vertex has at
most $r$ neighbours below it, so $H_r$ is $r$-degenerate. Conversely, if
$|V_0| \ge r+1$ (the proof takes $|V_0| \ge 2r^2$), the union of the
first two layers has minimum internal degree $\ge r$: each child retains
its $r$ parents, and each root lies in $\binom{|V_0|-1}{r-1}\ge r$
children. Hence $H_r$ is not $(r-1)$-degenerate, and its degeneracy is
exactly $r$. (Lean: the two-layer witness
`ExactDegeneracy.not_isDegenerate_of_layer_witness`,
[`lib/ExactDegeneracy.lean`](lib/ExactDegeneracy.lean); note the
hypothesis $|V_0|\ge r+1$ is necessary — for small root sets the layered
graph degenerates.)

**The host.** Take two disjoint copies of the Hamming cube $\{0,1\}^m$
and join $x$ in one copy to $y$ in the other iff their Hamming distance
is at most $\tau m$, for a fixed $\tau\in(0,\tfrac12)$. Sparsify by
retaining each vertex independently with probability $2^{-\beta m}$. A
second-moment computation ([`lib/SamplingR.lean`](lib/SamplingR.lean))
shows that, writing $n$ for the number of retained vertices, the retained
graph has at least $n^{2-1/r+\varepsilon}$ edges (for an explicit
$\varepsilon>0$) whenever
$$\beta\ <\ C_r(\tau)\ :=\ r\,h(\tau)-(r-1),$$
where $h$ is the binary entropy function (base 2). Thus $C_r$ is the
density threshold: below it, sparsification leaves the host dense enough
to violate the conjectured bound.

## 4. Exclusion of $H_r$: the entropy bound

Suppose a copy of $H_r$ embeds in the retained host. Each vertex of
$H_r$ receives a string in $\{0,1\}^m$, and each child's string lies
within Hamming distance $\tau m$ of each of its $r$ parents' strings.
Regarding the embedded strings as random variables over a uniformly
random copy (the standard entropy-counting device), consider the
conditional entropy of a child string given its $r$ parent strings. Two
bounds compete:

- **Lower bound (survival).** Retained vertices have density
  $2^{-\beta m}$; for the embedded copy to supply retained children above
  every $r$-set of parents, children must spread over many candidate strings,
  forcing average conditional entropy $> \beta$ per bit. This is a
  counting/union-bound argument over retained children
  ([`lib/BridgeR.lean`](lib/BridgeR.lean)).
- **Upper bound (proximity).** Proximity to all $r$ parents
  simultaneously pins the child down. A Gibbs (soft-max) inequality,
  weighting disagreement with each parent by $2^\lambda$, bounds the
  conditional entropy by
  $$A_r(\lambda)\ =\ \lambda\tau+\sup_{q,v}\,G_r(q,v)$$
  plus a telescoping potential correction. Here $G_r$ is an explicit
  function of two variables: $q$, the bit-frequency profile of the
  parents, and $v$, the child's disagreement rate. (Lean:
  `typeEntropyBound_supG_gen` in [`Theorem2.lean`](Theorem2.lean); the
  bookkeeping assembling per-coordinate bounds into the global one — the
  "ledger" — is [`lib/LedgerR.lean`](lib/LedgerR.lean).)

If $\beta > A_r(\lambda)$, the two bounds are contradictory and no copy
exists. The weight $2^\lambda$ is a free parameter of the obstruction;
Theorem 3(a) shows $2^\lambda = e$ is the exact ceiling for its
usefulness.

## 5. Positivity of the window

It remains to choose $(\tau,\lambda)$ with $A_r(\lambda) < C_r(\tau)$.
Both thresholds equal $1-\Theta(1/r)$, so the comparison happens in the
lower-order terms. Fix the radius schedule
$$\tau_r\ =\ \tfrac12-\frac{a}{4r},\qquad a:=\lambda\ln2 .$$
Three lemmas control the two sides.

**Lemma A** (concavity; [`LemmaA.lean`](LemmaA.lean)). The one-parent
entropy functional
$F_a(q)=h(q)+\log_2\!\bigl(e^{-2aq}+e^{-2a(1-q)}\bigr)$ satisfies
$$F_a''(q)\,\ln2\ =\ -\frac1{q(1-q)}+4a^2\,\mathrm{sech}^2\bigl(a(1-2q)\bigr)\ \le\ 4(a^2-1).$$
In particular $F_a$ is strictly concave for $a<1$, with margin vanishing
exactly at $a=1$, i.e. at Gibbs weight $2^\lambda=e$. This is the source
of the phase transition in Theorem 3(a).

**Lemma B** (center maximization; [`LemmaB.lean`](LemmaB.lean)). For
$\lambda\le\frac{27}{20}$ and every $r\ge2$,
$\sup_{[0,1]^2} G_r=G_r(\tfrac12,\tfrac12)$. The proof combines
per-term concavity in $v$, transfer of curvature bounds through a
Bernstein operator in $q$, and Lemma A away from a central strip. A
quantified version valid for **every** subcritical $\lambda$ once
$r \ge R(\lambda)$ is [`lib/LemmaBQuant.lean`](lib/LemmaBQuant.lean)
(`supG_eq_center_quant`); it is this version that makes Theorem 3(a)
unconditional on the full range $\lambda \ln 2 < 1$. Lemma B reduces
$A_r(\lambda)$ to an explicit quantity.

**Lemma C / Lemma 6.1** (evaluation; [`LemmaC.lean`](LemmaC.lean),
[`Lemma61.lean`](Lemma61.lean)). The center value
$G_r(\tfrac12,\tfrac12)$ is a binomially weighted $\log\cosh$ sum, and
the elementary sandwich
$$\frac{t^2}2-\frac{t^4}{12}\ \le\ \log\cosh t\ \le\ \frac{t^2}2-\frac{t^4}{12}+\frac{t^6}{45},$$
combined with the exact moments of $2\,\mathrm{Bin}(r,\tfrac12)-r$,
yields
$$C_r-A_r\ =\ \frac{\lambda^4\ln^32}{64\,r^2}\Bigl(1+O(\tfrac1r)\Bigr).$$

We emphasize the mechanism. With the radius schedule above, the
$1/r$-order terms of $A_r$ and $C_r$ cancel identically — a
binomial-variance term against an entropy-curvature term, the two
combining into the perfect square $(4c-\lambda\ln2)^2$ — and the
surviving $1/r^2$ term is positive for exactly one reason: $\log\cosh t$
lies below its parabola $t^2/2$ (the quartic correction $-t^4/12$ is
negative). Binomial fluctuations at this sparsity are slightly cheaper
in entropy than the Gaussian approximation predicts, and this
discrepancy is the entire source of the counterexample.

## 6. Organization of the Lean development

Theorem files are top-level; infrastructure is in `lib/`; consistency
tests in `tests/`; the declaration inventory is
[`formalization.yaml`](formalization.yaml).

| File | Role |
|---|---|
| `LemmaA.lean`, `LemmaB.lean`, `LemmaC.lean`, `Lemma61.lean` | the analytic lemmas of §5 |
| `lib/LemmaBQuant.lean` | quantified Lemma B (all subcritical $\lambda$, $r$ large) |
| `lib/SamplingR.lean`, `lib/KernelR.lean`, `lib/BridgeR.lean` | host density (§3); entropy kernel and embedding obstruction (§4), general $r$ |
| `lib/LedgerR.lean`, `lib/ProfilesR.lean`, `lib/LedgerAsym.lean` | the ledger assembling per-coordinate entropy bounds; its $r\to\infty$ asymptotics (Theorem 3(b)) |
| `lib/LedgerSharp.lean` | sharp $r$-aware $K_1$ bounds and the $(\theta,\eta)$-parametric ledger (§9) |
| `lib/ExactDegeneracy.lean` | the degeneracy lower bound (two-layer minimum-degree witness) |
| `lib/Entropy3.lean`, `lib/Sampling3.lean`, `lib/Kernel3.lean`, `lib/Bridge3.lean` | hand-certified $r=3$ instances |
| `lib/LawDefs.lean` | shared definitions for the window law |
| `lib/CompactnessAndDegeneracy.lean` | upstream graph-theoretic prerequisites |
| `Theorem1.lean`, `Theorem2.lean`, `Theorem3a.lean`, `Theorem3b.lean`, `Prop63.lean` | final assemblies of Theorems 1–3 |
| `tests/KernelRCheck3.lean` | the general $r$ kernel specializes at $r=3$ to the hand-certified one |
| `tests/ChallengeFaithful.lean` | kernel-checked faithfulness of the challenge statement (§8) |
| `challenges/K_*.lean`, `challenges/challenge*.json` | frozen challenge statements and Comparator configurations (§8) |
| `Solution1.lean` … `Solution4.lean` | Comparator-format solutions restating and proving the challenges (§8) |

Intermediate lemmas carry parameter thresholds (e.g.
`2 * r ^ 2 ≤ parentCount` in `lib/BridgeR.lean`); all are discharged
inside the final assemblies, and the headline statements assume nothing
beyond $r\ge2$.

## 7. Verification

The CI workflow
[`.github/workflows/build.yml`](.github/workflows/build.yml) is the
canonical verification script: it runs everything below on every push,
and cloning the repository and running its steps reproduces the check
locally.

- The toolchain is pinned by `lean-toolchain` (Lean 4 `v4.32.0`; mathlib
  `v4.32.0` per `lakefile.toml`); `elan` selects it automatically.
- Build: `lake exe cache get && lake build`. This compiles the
  `defaultTargets` — `Upstream`, `ErdosDegeneracyLib`, `ErdosDegeneracy`,
  `ErdosDegeneracyTests` — all sorry-free (a `sorry` anywhere in them
  would surface as a build warning; `formalization.yaml` records
  `sorries: 0` and the axiom list). CI runs the build on every push.
- Sorry inventory (source files only, excluding `.lake/`):
  `grep -rn --include='*.lean' '\bsorry\b' ./*.lean lib tests challenges`.
  The only hits outside documentation are the four intentional ones in
  the frozen challenge statements (§8).
- Independent numerical redundancy: `python3 tests/numerics_check.py`
  reimplements the window and ledger formulas and the layered graph
  outside Lean, and checks the 3(a) limit (approached from below), the
  supercritical divergence, Lemma B's center maximization, the 3(b)
  family law, both explicit constants of §9, and exact degeneracy by
  graph peeling. These are floating-point sanity checks, not proofs; a
  failure would constitute a genuine counterexample to a claimed
  inequality.

## 8. The frozen challenge statements

The [`challenges/`](challenges/) directory contains four standalone
statement files in the format of
[leanprover/comparator](https://github.com/leanprover/comparator), the
Lean FRO's standard procedure for judging a Lean proof against a frozen
statement. Each file defines its quantities from scratch, states one
theorem, and ends in an **intentional `sorry`**; each is discharged by a
solution file at the repository root that restates it verbatim and
proves it.

| Challenge | Statement | Solution |
|---|---|---|
| [`K_ThreeDegenerateGraphs.lean`](challenges/K_ThreeDegenerateGraphs.lean) | Theorem 1 with existential $\varepsilon$ (the original file from [OAI26], unmodified) | [`Solution1.lean`](Solution1.lean) |
| [`K_RDegenerateGraphs.lean`](challenges/K_RDegenerateGraphs.lean) | Theorem 2: degeneracy exactly $r$, gain $1/(28r^2)$, every $r\ge2$ | [`Solution2.lean`](Solution2.lean) |
| [`K_WindowLaw.lean`](challenges/K_WindowLaw.lean) | Theorem 3(a): $r^2\,\mathrm{width}_r \to \lambda^4\ln^3 2/64$ | [`Solution3.lean`](Solution3.lean) |
| [`K_FamilyLaw.lean`](challenges/K_FamilyLaw.lean) | Theorem 3(b): $8r^2 \varepsilon^{\max}(\beta_\theta) \to 1-\theta$ | [`Solution4.lean`](Solution4.lean) |

Comparator verifies, per pair, that the solution proves a theorem of the
identical name and statement, uses no axioms beyond `propext`,
`Quot.sound`, `Classical.choice`, and is accepted by a kernel replay:

```sh
for c in challenges/challenge*.json; do lake env comparator $c; done
```

All four pass. The only input requiring human review is the four
statements themselves; [`challenges/NOTES_FOR_REVIEWER.md`](challenges/NOTES_FOR_REVIEWER.md)
walks through each statement and what to check.

Independently of Comparator, faithfulness of the original challenge is
also kernel-checked inside Lean:
[`tests/ChallengeFaithful.lean`](tests/ChallengeFaithful.lean) asserts
that the theorem proved in [`Theorem1.lean`](Theorem1.lean) has *exactly
the type of the challenge declaration* (via `type_of%`), so any drift
between the two files fails to compile. CI builds all challenge and
solution modules on every push.

## 9. Optimization of the explicit constants

Write $w_r = C_r - A_r$ for the window width at $\lambda = 27/20$, and
for $\theta\in(0,1)$ let $\beta_\theta = A_r + \theta w_r$. The finite $r$
pipeline certifies the exponent gain
$$\varepsilon\ =\ (1-\eta)\,\varepsilon_r^{\max}(\beta_\theta)
  \ \ge\ \frac{(1-\eta)(1-\theta)\,w}{K_1\,r^2},$$
where $w/r^2 \le w_r$ is a certified window lower bound, $K_1$ bounds
$r(1-\beta_\theta)$, and $\eta\in(0,1)$ is a slack parameter
(`epsR_theta_lower`, [`lib/LedgerSharp.lean`](lib/LedgerSharp.lean)).

Evaluated at the midpoint $\theta=\eta=\tfrac12$, the chain certifies
$1/(108r^2)$, retained as a checkpoint (`eps_half_108`). But the
midpoint is a choice, not an optimum: by Theorem 3(b), $K_1(\theta)$ is essentially
independent of $\theta$ while the certified gain scales as
$(1-\eta)(1-\theta)$, so the chain improves monotonically toward the
exclusion edge. Running it at $\theta=\eta=1/100$, with $r$-aware
$K_1$ bounds ($K_1(1/100) \le 0.1637$, all $r \ge 2$;
`K1_hundredth_le`), gives
$$\varepsilon\ \ge\ \frac{1}{28\,r^2}$$
(`eps_hundredth_28`), the constant of Theorem 2, against this route's ceiling of
$\approx 1/(27.2\,r^2)$.

At $r=3$ the same ledger, fed with Lemma C's window bound specialized to
$r=3$ ($w_3 \ge 0.0098/9$, `width_ge_three` in
[`Theorem2.lean`](Theorem2.lean)) instead of the uniform constant, gives
$\varepsilon_3 \ge 1/160$ (`eps_three_160`) — Theorem 1's exponent
(the midpoint evaluation gives $1/200$). The original hand-certified $r=3$ assembly, with
gain $1/4000$, is retained in [`Theorem1.lean`](Theorem1.lean)
(`threeDegenerateExtremalCounterexample_exact`), and compatibility
statements at the older constants are kept
(`rDegenerateExtremalCounterexample_explicit_110`).

Remaining headroom, recorded as future work: interval evaluation of the
window at each fixed small $r$ would push $1/(28r^2)$ toward
$1/(21r^2)$, $\varepsilon_3$ toward $1/138$, and the midpoint checkpoint
from $108$ to $107$.

## References

[AKS03] N. Alon, M. Krivelevich, and B. Sudakov, *Turán numbers of bipartite
graphs and related Ramsey-type questions*, Combin. Probab. Comput. **12**
(2003), 477–494. <https://doi.org/10.1017/S0963548303005741> (the
$2-\frac{1}{4r}$ upper bound bracketing our result).

[Erd] P. Erdős and M. Simonovits, the degeneracy conjecture. Catalogued as
Erdős problem #146, <https://www.erdosproblems.com/146>, where the primary
sources are listed.

[OAI26] OpenAI, *Ten advances in mathematics and theoretical computer
science*, 2026. <https://openai.com/index/ten-advances-in-mathematics/>;
paper at <https://cdn.openai.com/pdf/ten-proofs-oai.pdf>, Lean at
<https://github.com/openai/ten-proofs>. Chapter 10 refuted the $r=2$ case
and supplies the construction framework generalized here (its $r=2$
result optimizes the radius freely and is not implied by our Theorem 2).
