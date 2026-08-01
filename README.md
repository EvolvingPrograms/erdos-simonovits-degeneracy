# The Erdős–Simonovits degeneracy conjecture fails at every level

**Claude Fable 5 and Claude Opus 5** · 2026-08-01 · Lean 4 + mathlib, zero
sorries, axioms `propext, Classical.choice, Quot.sound` · full paper
forthcoming

## Abstract

The degeneracy conjecture of Erdős and Simonovits (Erdős problem #146) asserts
that $\mathrm{ex}(n;H) \ll n^{2-1/r}$ for every $r$-degenerate bipartite graph
$H$; the case $r=2$ was recently refuted in [OAI26]. We refute it at every
level: for each $r\ge2$ there is a connected bipartite graph $H_r$ of
degeneracy exactly $r$ with
$$\mathrm{ex}(n;H_r)\ \ge\ c\,n^{2-\frac1r+\varepsilon_r},\qquad
\varepsilon_r\ >\ \frac{1}{110\,r^2},$$
for all large $n$. Optimising the Gibbs weight in the entropy method of
[OAI26, ch. 10] exposes an exact law: the method's feasibility window
satisfies $r^2\cdot\mathrm{width}\to\lambda^4\ln^32/64$, maximised precisely
at Gibbs weight $e$ (beyond which it is $-\infty$), and the exponent gain
obeys $\lim 16r^2\varepsilon_r = 1$. All results below are machine-checked;
each theorem links to its Lean statement.

## 1. The construction

$H_r$ is the layered $r$-subset graph: $V_0$ finite,
$V_{i+1}=\binom{V_i}{r}$, each child joined to its $r$ parents; connected,
bipartite, degeneracy exactly $r$. The host is two copies of $\{0,1\}^m$
joined at Hamming distance $\le\tau m$, vertices retained independently with
probability $2^{-\beta m}$; a second-moment count gives it
$n^{2-1/r+\varepsilon}$ edges whenever $\beta < C_r(\tau) := rh(\tau)-(r-1)$
([`lib/SamplingR.lean`](lib/SamplingR.lean)).

## 2. Why $H_r$ cannot embed: the entropy window

If $H_r$ embedded in the host, each layer's bit-strings would need average
conditional entropy $>\beta$ given their parents (a counting/union-bound
argument over retained children, [`lib/BridgeR.lean`](lib/BridgeR.lean)). But
a Gibbs-inequality bound with *free* weight $2^\lambda$ (the one new dial
over [OAI26], whose weight was fixed at 3) caps that entropy by
$A_r(\lambda) = \lambda\tau + \sup_{q,v}G_r(q,v)$ plus a telescoping
potential ([`Theorem2.lean`](Theorem2.lean) `typeEntropyBound_supG_gen`;
ledger [`lib/LedgerR.lean`](lib/LedgerR.lean)). So the construction succeeds
exactly when the **window** $A_r < \beta < C_r$ is nonempty.

## 3. The window is open at every $r$: three lemmas

Take $\tau_r = \tfrac12 - \tfrac{\lambda\ln2}{4r}$, $a = \lambda\ln2$.

- **Lemma A** ([`LemmaA.lean`](LemmaA.lean)). For
  $F_a(q) = h(q)+\log_2(e^{-2aq}+e^{-2a(1-q)})$:
  the identity
  $F_a''\ln2 = -\tfrac1{q(1-q)} + 4a^2\mathrm{sech}^2(a(1-2q)) \le 4(a^2-1)$
  gives strict concavity in one line, with margin vanishing exactly at $a=1$.
- **Lemma B** ([`LemmaB.lean`](LemmaB.lean)). For $\lambda \le \tfrac{27}{20}$
  and all $r\ge2$, $\sup G_r = G_r(\tfrac12,\tfrac12)$: per-term concavity in
  $v$, a Bernstein-operator transfer of curvature bounds in $q$, Lemma A off a
  central strip. Quantified version ($r \ge R(\lambda)$, all subcritical
  $\lambda$): [`lib/LemmaBQuant.lean`](lib/LemmaBQuant.lean).
- **Lemmas C and 6.1** ([`LemmaC.lean`](LemmaC.lean),
  [`Lemma61.lean`](Lemma61.lean)). The center value is an explicit binomial
  log-cosh sum; $\tfrac{t^2}2-\tfrac{t^4}{12} \le \log\cosh t \le
  \tfrac{t^2}2-\tfrac{t^4}{12}+\tfrac{t^6}{45}$ with exact moments of
  $2\mathrm{Bin}(r,\tfrac12)-r$ sandwich the window:
  $C_r - A_r = \tfrac{\lambda^4\ln^32}{64\,r^2}\,(1+O(\tfrac1r))$.

The mechanism: at $\tau_r$ the $1/r$ terms of $A_r$ and $C_r$ cancel
*identically* (binomial variance against entropy curvature, the perfect
square $(4c-\lambda\ln2)^2$), and the surviving $1/r^2$ width is positive
because log-cosh is flatter than its parabola (negative quartic term).

## 4. Theorems

**Theorem 1 (the $r=3$ counterexample).** There is a connected bipartite
graph $H$ of degeneracy exactly $3$ and a $c>0$ with
$$\mathrm{ex}(n;H)\ \ge\ c\,n^{5/3+1/4000}\qquad\text{for all large }n.$$
**Lean:** [`Theorem1.lean`](Theorem1.lean) `threeDegenerateExtremalCounterexample`.

**Theorem 2 (failure at every level).** For every $r\ge2$ there exist a
connected bipartite graph $H_r$ of degeneracy exactly $r$ and a $c>0$ with
$$\boxed{\ \mathrm{ex}(n;H_r)\ \ge\ c\,n^{\,2-\frac1r+\frac{1}{110\,r^2}}\ }\qquad\text{for all large }n.$$
**Lean:** [`Theorem2.lean`](Theorem2.lean) `rDegenerateExtremalCounterexample_explicit`.

**Theorem 3 (the asymptotic law).** (a) For every fixed $\lambda$ with
$\lambda\ln2<1$,
$$\lim_{r\to\infty} r^2\bigl(C_r-A_r(\lambda)\bigr)\ =\ \frac{\lambda^4\ln^32}{64},$$
while for $\lambda\ln2>1$ the limit is $-\infty$: the threshold is exactly
Gibbs weight $2^\lambda=e$.
**Lean:** [`Theorem3a.lean`](Theorem3a.lean) `width_tendsto_unconditional`;
[`Prop63.lean`](Prop63.lean) `threshold_sharp`.

(b) Along the schedule $\lambda_r=\tfrac{1-\ln r/r}{\ln2}$ the maximal
admissible exponent gain $\varepsilon_r^{\max}$ (defined in
[`lib/LedgerR.lean`](lib/LedgerR.lean)) satisfies
$$\boxed{\ \lim_{r\to\infty}\ 16\,r^2\,\varepsilon_r^{\max}\ =\ 1\ .}$$
**Lean:** [`lib/LedgerAsym.lean`](lib/LedgerAsym.lean) `sixteen_rsq_epsMax_tendsto'`
(schedule and Lemma-B applicability: [`Theorem3b.lean`](Theorem3b.lean)).

## 5. Formalization notes

Build: `lake exe cache get && lake build`. Theorem files top-level, infrastructure in `lib/`,
faithfulness test in `tests/`; the challenge statement
[`K_ThreeDegenerateGraphs.lean`](K_ThreeDegenerateGraphs.lean) (the
human-auditable statement, intentionally ending in `sorry`, discharged by
`Theorem1.lean`) builds separately via `lake build Challenge`; inventory in
`formalization.yaml`. The full paper (forthcoming) proves the sharper
constants $1/(107r^2)$ and, at $r=3$, $1/200$ (via a sharp $K_1$ evaluation
and an interval-arithmetic certificate); the Lean constants $1/(110r^2)$ and
$1/4000$ are the machine-checked forms, and closing that gap is listed as
future work.

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
and supplies the construction framework generalized here (its $r=2$ result
optimises the radius freely and is not implied by our Theorem 2).
