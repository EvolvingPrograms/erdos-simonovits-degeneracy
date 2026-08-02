# The Erdős–Simonovits degeneracy conjecture fails at every level

**Claude Fable 5 and Claude Opus 5** · 2026-08-01 · Lean 4 + mathlib, zero
sorries in the default build targets (the standalone challenge statement
intentionally ends in `sorry`; see [§8](#8-the-challenge-statement)), axioms
`propext, Classical.choice, Quot.sound` · full paper forthcoming

## 1. What is proven

Two definitions, so that everything below is self-contained.

- The **extremal number** $\mathrm{ex}(n;H)$ is the largest number of edges
  an $n$-vertex graph can have while containing no copy of $H$ as a
  subgraph.
- A graph is **$r$-degenerate** if every subgraph of it (equivalently,
  every nonempty vertex subset) contains a vertex with at most $r$
  neighbours inside it. Degeneracy measures local sparsity: trees are
  1-degenerate, planar graphs are 5-degenerate.

Erdős and Simonovits conjectured (Erdős problem #146, [Erd]) that sparse
bipartite patterns are easy to force: if $H$ is bipartite and
$r$-degenerate, then $\mathrm{ex}(n;H) = O(n^{2-1/r})$. The best known
general upper bound in this direction is $\mathrm{ex}(n;H) =
O(n^{2-1/(4r)})$ [AKS03], and the conjecture was open for decades until the
case $r=2$ was refuted in 2026 [OAI26, ch. 10]. This repository proves,
machine-checked in Lean 4, that the conjecture fails **for every** $r$, and
by a polynomial margin:

**Theorem 1 (the $r=3$ counterexample).** There is a connected bipartite
graph $H$ of degeneracy exactly 3 and a $c>0$ with
$$\mathrm{ex}(n;H)\ \ge\ c\,n^{5/3+1/4000}\qquad\text{for all large }n.$$

**Theorem 2 (failure at every level).** For every $r\ge2$ there is a
connected bipartite graph $H_r$ of degeneracy exactly $r$ and a $c>0$ with
$$\boxed{\ \mathrm{ex}(n;H_r)\ \ge\ c\,n^{\,2-\frac1r+\frac{1}{48\,r^2}}\ }\qquad\text{for all large }n.$$

**Theorem 3 (the exact asymptotic law).** The proof method has one free
parameter (a "Gibbs weight" $2^\lambda$, explained in §4), and its power
can be computed exactly in the limit $r\to\infty$:

(a) For every fixed $\lambda$ with $\lambda\ln 2<1$, the method's
feasibility window (defined in §5) has width satisfying
$$\lim_{r\to\infty} r^2\cdot\mathrm{width}\ =\ \frac{\lambda^4\ln^32}{64},$$
while for $\lambda\ln2>1$ the limit is $-\infty$. The phase transition
sits exactly at Gibbs weight $2^\lambda=e$.

(b) Optimising $\lambda$ as $r$ grows (schedule
$\lambda_r=\frac{1-\ln r/r}{\ln2}$), the exponent gain
$\varepsilon_r^{\max}$ the method certifies satisfies
$$\boxed{\ \lim_{r\to\infty}\ 8\,r^2\,\varepsilon_r^{\max}(\beta_\theta)\ =\ 1-\theta\ }$$
at every position $\beta_\theta=A_r+\theta\,(C_r-A_r)$ of the window,
$\theta\in(0,1)$. So the method's best constant is $1/(8r^2)$ — approached
as $\beta$ nears the exclusion threshold, never attained — and the
canonical midpoint choice $\theta=\tfrac12$ certifies $1/(16r^2)$. The
$1/(48r^2)$ of Theorem 2 is the explicit finite-$r$ output of this family
at $(\theta,\eta)=(\tfrac14,\tfrac14)$ — the family law is what licenses
running the ledger off the midpoint.

Each theorem statement is literal in Lean — "degeneracy exactly $r$" is
carried as `IsDegenerate r H ∧ ¬ IsDegenerate (r-1) H`, and the exponents
appear as written:

| | Lean declaration | File |
|---|---|---|
| Theorem 1 | `threeDegenerateExtremalCounterexample_exact` | [`Theorem1.lean`](Theorem1.lean) |
| Theorem 2 | `rDegenerateExtremalCounterexample_exact` | [`Theorem2.lean`](Theorem2.lean) |
| Theorem 3(a) | `width_tendsto_unconditional_full` | [`Theorem3a.lean`](Theorem3a.lean) |
| Theorem 3(a), sharpness | `threshold_sharp` | [`Prop63.lean`](Prop63.lean) |
| Theorem 3(b) | `eight_rsq_epsMax_theta_tendsto` | [`lib/LedgerAsym.lean`](lib/LedgerAsym.lean) |

The rest of this README explains the proof in prose (§§2–5), then maps it
to the Lean development (§6) and tells you how to verify it (§§7–8).

## 2. The shape of the argument

To bound $\mathrm{ex}(n;H_r)$ from below one must exhibit a single dense
graph containing no copy of $H_r$. The argument has three moving parts:

1. **A pattern graph $H_r$** of degeneracy exactly $r$ (§3).
2. **A random host graph** which, for a parameter $\beta$ below a
   threshold $C_r$, has $n^{2-1/r+\varepsilon}$ edges with high
   probability (§3).
3. **An embedding obstruction**: an entropy argument showing that when
   $\beta$ is above a second threshold $A_r$, the host contains no copy
   of $H_r$ at all (§4).

The construction succeeds exactly when the **window** $A_r < \beta < C_r$
is nonempty. The heart of the proof — and all of the analytic difficulty —
is showing this window is open for every $r$ (§5). Its width turns out to
be of order $1/r^2$: tiny, but positive, and this $1/r^2$ is exactly the
$1/(48r^2)$ exponent gain in Theorem 2.

Everything is a generalization of the $r=2$ argument of [OAI26, ch. 10],
with two new ingredients: the whole machine is run at a general $r$
(uniformly, with explicit constants), and one parameter that [OAI26] fixed
numerically — the Gibbs weight — is left free and then optimised, which is
what exposes the exact law of Theorem 3.

## 3. The pattern and the host

**The pattern.** $H_r$ is the layered $r$-subset graph. Start with a
finite set $V_0$ of roots. Each subsequent layer consists of all
$r$-element subsets of the previous layer,
$V_{i+1}=\binom{V_i}{r}$, and each such subset — a "child" — is joined by
an edge to each of its $r$ elements — its "parents". Taking a few layers
gives a connected bipartite graph (odd layers on one side, even on the
other). For $|V_0| \ge r+1$ (the proof takes $|V_0| \ge 2r^2$) its
degeneracy is exactly $r$: peeling from the top layer down, every vertex
has at most $r$ neighbours below it; conversely the first two layers form
a subgraph of minimum degree $r$ — each child keeps its $r$ parents and
each root lies in $\binom{|V_0|-1}{r-1}\ge r$ children — forcing
degeneracy at least $r$ (Lean:
`ExactDegeneracy.not_isDegenerate_of_layer_witness` in
[`lib/ExactDegeneracy.lean`](lib/ExactDegeneracy.lean)).

**The host.** Take two disjoint copies of the Hamming cube
$\{0,1\}^m$ and join a vertex in one copy to a vertex in the other
whenever their Hamming distance is at most $\tau m$, where
$\tau\in(0,\tfrac12)$ is a proximity parameter. Then sparsify randomly:
keep each vertex independently with probability $2^{-\beta m}$. Writing
$n$ for the number of surviving vertices, a second-moment computation
([`lib/SamplingR.lean`](lib/SamplingR.lean)) shows the survivor graph has
$n^{2-1/r+\varepsilon}$ edges (for suitable $\varepsilon>0$ depending on
the parameters) as long as
$$\beta\ <\ C_r(\tau)\ :=\ r\,h(\tau)-(r-1),$$
where $h$ is the binary entropy function. So $C_r$ is the "density
budget": below it, sparsification leaves the host dense enough to beat
the conjectured bound.

## 4. Why $H_r$ cannot embed: entropy

Suppose, for contradiction, that a copy of $H_r$ sits inside the surviving
host. Every vertex of $H_r$ is then assigned a bit-string in $\{0,1\}^m$,
and each child's string lies within Hamming distance $\tau m$ of each of
its $r$ parents' strings.

Now regard the embedded strings as random variables (over a uniformly
random copy, in the standard entropy-counting fashion) and ask: given the
$r$ parent strings, how much conditional entropy can a child string have?
Two competing pressures:

- **A lower bound from survival.** Surviving vertices are rare (density
  $2^{-\beta m}$), so for the pattern to keep finding surviving children
  for every $r$-set of parents, children must be spread thinly across
  many candidate strings — which forces average conditional entropy
  **greater than $\beta$** (per bit). This is a counting/union-bound
  argument over retained children,
  [`lib/BridgeR.lean`](lib/BridgeR.lean).
- **An upper bound from proximity.** Being within distance $\tau m$ of
  all $r$ parents simultaneously pins the child down. A Gibbs-inequality
  (soft-max) bound, which weights disagreement with each parent by a
  factor $2^\lambda$, caps the conditional entropy by
  $$A_r(\lambda)\ =\ \lambda\tau+\sup_{q,v}G_r(q,v)$$
  plus a telescoping potential correction, where $G_r$ is an explicit
  two-variable function recording the entropy cost at "type" $(q,v)$ —
  $q$ the bit-frequency profile of the parents, $v$ the child's
  disagreement rate. (Lean: `typeEntropyBound_supG_gen` in
  [`Theorem2.lean`](Theorem2.lean); the bookkeeping that assembles
  per-coordinate bounds into the global one is the "ledger",
  [`lib/LedgerR.lean`](lib/LedgerR.lean).)

If $\beta > A_r(\lambda)$ the two bounds contradict each other, so no copy
of $H_r$ exists. The weight $2^\lambda$ is a genuinely free dial —
[OAI26] fixed it at 3; here it is optimised, and the optimum matters
(Theorem 3 says weight $e$ is the exact ceiling).

## 5. The window is open: where the $1/r^2$ comes from

We need $A_r(\lambda) < C_r(\tau)$ for some admissible choice of
$(\tau,\lambda)$. Both sides are $1-\Theta(1/r)$, so this is a fight over
lower-order terms. Choose
$$\tau_r\ =\ \tfrac12-\frac{\lambda\ln2}{4r},\qquad a:=\lambda\ln2 .$$

Three analytic lemmas control the two sides:

- **Lemma A** ([`LemmaA.lean`](LemmaA.lean)) — concavity of the
  one-parent entropy functional
  $F_a(q)=h(q)+\log_2(e^{-2aq}+e^{-2a(1-q)})$. The second derivative has
  the closed form
  $F_a''\ln2=-\frac1{q(1-q)}+4a^2\operatorname{sech}^2(a(1-2q))\le4(a^2-1)$,
  so strict concavity holds in one line, with margin degenerating exactly
  at $a=1$ — i.e. at Gibbs weight $2^\lambda=e$. This is where the phase
  transition of Theorem 3(a) originates.
- **Lemma B** ([`LemmaB.lean`](LemmaB.lean)) — the supremum of
  $G_r$ is attained at the symmetric point:
  $\sup G_r=G_r(\tfrac12,\tfrac12)$, valid for $\lambda\le\frac{27}{20}$
  and all $r\ge2$. (Proof: per-term concavity in $v$; transfer of
  curvature bounds through a Bernstein operator in $q$; Lemma A off a
  central strip. A quantified version covering every subcritical
  $\lambda$ for $r$ large is
  [`lib/LemmaBQuant.lean`](lib/LemmaBQuant.lean).) This reduces
  $A_r(\lambda)$ to an explicit number.
- **Lemmas C and 6.1** ([`LemmaC.lean`](LemmaC.lean),
  [`Lemma61.lean`](Lemma61.lean)) — evaluation. The centre value
  $G_r(\tfrac12,\tfrac12)$ is a binomially weighted log-cosh sum, and the
  elementary sandwich
  $\frac{t^2}2-\frac{t^4}{12}\le\log\cosh t\le\frac{t^2}2-\frac{t^4}{12}+\frac{t^6}{45}$,
  fed with the exact moments of $2\,\mathrm{Bin}(r,\tfrac12)-r$, pins the
  window width down to
  $$C_r-A_r\ =\ \frac{\lambda^4\ln^32}{64\,r^2}\Bigl(1+O(\tfrac1r)\Bigr).$$

The mechanism behind the positivity is a conspiracy at order $1/r$: with
$\tau_r$ as above, the $1/r$ terms of $A_r$ and $C_r$ cancel
**identically** — a binomial-variance term against an entropy-curvature
term, combining into the perfect square $(4c-\lambda\ln2)^2$ — and the
surviving $1/r^2$ term is positive for exactly one reason: $\log\cosh t$
lies **below** its parabola $t^2/2$ (the quartic correction $-t^4/12$ has
a negative sign). Sparse binomial fluctuations are slightly cheaper in
entropy than the Gaussian approximation predicts, and that sliver is the
counterexample.

## 6. Guide to the Lean development

Theorem files live top-level; infrastructure in `lib/`; a faithfulness
test in `tests/`; declaration inventory in
[`formalization.yaml`](formalization.yaml).

| File | Role |
|---|---|
| `LemmaA.lean`, `LemmaB.lean`, `LemmaC.lean`, `Lemma61.lean` | the analytic lemmas of §5 |
| `lib/LemmaBQuant.lean` | quantified Lemma B (all subcritical $\lambda$, $r$ large) |
| `lib/SamplingR.lean`, `lib/KernelR.lean`, `lib/BridgeR.lean` | host density (§3), entropy kernel and embedding obstruction (§4), at general $r$ |
| `lib/LedgerR.lean`, `lib/ProfilesR.lean`, `lib/LedgerAsym.lean` | the ledger assembling per-coordinate entropy bounds; its $r\to\infty$ asymptotics |
| `lib/Entropy3.lean`, `lib/Sampling3.lean`, `lib/Kernel3.lean`, `lib/Bridge3.lean` | hand-certified $r=3$ instances |
| `lib/LawDefs.lean` | shared definitions for the window law |
| `lib/CompactnessAndDegeneracy.lean` | upstream graph-theoretic prerequisites |
| `lib/ExactDegeneracy.lean` | the degeneracy lower bound (two-layer minimum-degree witness) |
| `Theorem1.lean`, `Theorem2.lean`, `Theorem3a.lean`, `Theorem3b.lean`, `Prop63.lean` | final assemblies of Theorems 1–3 |
| `tests/KernelRCheck3.lean` | checks the general-$r$ kernel specialises at $r=3$ to the hand-certified one |
| `K_ThreeDegenerateGraphs.lean` | the frozen challenge statement (§8) |

A note on hypotheses: intermediate lemmas carry parameter thresholds
(e.g. `2 * r ^ 2 ≤ parentCount` in `lib/BridgeR.lean`); these are all
discharged inside the final assemblies, and the headline theorem
statements assume nothing beyond $r\ge2$.

## 7. How to verify

- The toolchain is pinned by `lean-toolchain` (Lean 4 `v4.32.0`, mathlib
  `v4.32.0` per `lakefile.toml`); `elan` picks it up automatically.
- Build: `lake exe cache get && lake build`. This builds the
  `defaultTargets` from `lakefile.toml` — `Upstream`, `ErdosDegeneracyLib`,
  `ErdosDegeneracy`, `ErdosDegeneracyTests` — all of which are sorry-free
  (a `sorry` anywhere in them would surface as a build warning; the
  inventory in `formalization.yaml` records `sorries: 0` and the axiom
  list). CI runs this build on every push.
- Sorry inventory (scoped to sources, avoiding `.lake/`):
  `grep -rn --include='*.lean' '\bsorry\b' ./*.lean lib tests`.
  The only hit outside doc comments is the intentional one in the
  challenge statement (§8).
- Independent numerical redundancy: `python3 tests/numerics_check.py`
  reimplements the window/ledger formulas and the layered pattern outside
  Lean and checks the 3(a) limit (from below), the supercritical
  divergence, Lemma B's center maximization, the 3(b) family law, and
  exact degeneracy by graph peeling. Floating-point sanity checks, not
  proofs — a failure would be a genuine counterexample.

## 8. The challenge statement

[`K_ThreeDegenerateGraphs.lean`](K_ThreeDegenerateGraphs.lean) is a
40-line standalone statement file in the idiom of
`J_TwoDegenerateGraphs.lean` from [OAI26]: it defines degeneracy from
scratch and states Theorem 1, ending in an **intentional `sorry`**. It is
the frozen, human-auditable specification of what was to be proven — kept
verbatim (rather than importing the proof) so a referee can check the
target statement in isolation without trusting the development. It is
excluded from `defaultTargets` and builds separately via
`lake build Challenge`.

The discharge: the `ThreeDegenerateGraphsTarget` namespace at the end of
[`Theorem1.lean`](https://github.com/EvolvingPrograms/erdos-simonovits-degeneracy/blob/b7f33f4/Theorem1.lean#L1647)
restates the challenge statement token-for-token — same standalone
definitions, same theorem — and proves it (this is the copy the
sorry-free default build checks). Faithfulness is kernel-checked:
[`tests/ChallengeFaithful.lean`](tests/ChallengeFaithful.lean) asserts the
proven theorem has *exactly the type of the challenge declaration*
(`type_of%`), so any drift between the two files fails to compile; CI
runs `lake build Challenge ChallengeFaithful` on every push.

## 9. Beyond the paper constants

The paper's midpoint chain gives $1/(107r^2)$ (sharp $K_1=0.1614$) and, at
$r=3$, $1/200$. The Lean development now runs the ledger **off the
midpoint** — at window position $\theta=\tfrac14$ with slack
$\eta=\tfrac14$, licensed by Theorem 3(b)'s family law — and certifies
$1/(48r^2)$, strictly better than the paper's own headline constant
([`lib/LedgerSharp.lean`](lib/LedgerSharp.lean): the sharp $r$-aware $K_1$
bounds, the $(\theta,\eta)$-parametric ledger, and the paper's midpoint
chain reproduced as a `1/(108r^2)` checkpoint — the last hair to $107$ is
Lemma C's uniform window constant at $r=2$). A compatibility statement at
the old $1/(110r^2)$ is kept
(`rDegenerateExtremalCounterexample_explicit_110`). Remaining: the sharp
$r=3$ certificate (the same optimized ledger at $r=3$ targets
$\varepsilon_3 > 1/200$; the current machine-checked $r=3$ exponent gain
is $1/4000$).

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
