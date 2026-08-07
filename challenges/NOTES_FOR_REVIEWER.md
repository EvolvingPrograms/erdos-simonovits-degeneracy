# Notes for the reviewer: the four Comparator challenges

This directory contains four frozen challenge statements in the
[leanprover/comparator](https://github.com/leanprover/comparator) format:
each file states one theorem and ends in an intentional `sorry`. The
corresponding solutions (`proofs/Solution1.lean` … `proofs/Solution4.lean`)
restate each theorem verbatim and prove it. Comparator
verifies mechanically that the solution proves **the same statement**
using only the axioms `propext`, `Quot.sound`, `Classical.choice`, and
that the proof is accepted by the Lean kernel.

**The only thing that requires human judgment is the content of the four
statements below.** Everything else — that the proofs exist, match the
statements, and use no extra axioms — is machine-checked. Equivalently:
if you agree that each statement says what it claims to say, the theorem
is proved.

To run the checks (from the repository root, with `comparator`,
`lean4export` at the project toolchain, and `landrun` in `PATH`):

```sh
for c in challenges/challenge*.json; do lake env comparator $c; done
```

---

## Challenge 1 — `K_ThreeDegenerateGraphs.lean`

Our statement file, written in the idiom of OpenAI's
`J_TwoDegenerateGraphs.lean` ([OAI26], ch. 10) and frozen before the
proof. The definitions `neighborsWithin` and `IsDegenerate` are taken
verbatim from that file; the statement itself is not theirs — chapter 10
refutes the conjecture at r = 2, with exponent 3/2 + ε, and asserts
nothing at r = 3. It asserts a counterexample to Erdős problem #146 at
r = 3:

> There exist `q : ℕ` and a graph `H` on `Fin q` such that `H` is
> connected, bipartite, 3-degenerate, and for some `c, ε > 0`,
> `c · n^(5/3 + ε) ≤ ex(n; H)` for all sufficiently large `n`.

Points to check:

- `IsDegenerate r G` is defined as: every nonempty finite vertex subset
  `s` contains a vertex with at most `r` neighbors inside `s`. This is
  the standard definition of `r`-degeneracy.
- `SimpleGraph.extremalNumber n H` is mathlib's Turán-type extremal
  number: the maximum number of edges of an `H`-free graph on `n`
  vertices. The conclusion `c · n^(5/3+ε) ≤ ex(n; H)` therefore refutes
  `ex(n; H) = O(n^(2 - 1/3)) = O(n^(5/3))`.
- The exponent is `Real.rpow` (`(n : ℝ) ^ ((5:ℝ)/3 + ε)` with a real
  exponent), so there is no integer-power loophole.

This statement is additionally covered by `tests/ChallengeFaithful.lean`,
which asserts inside Lean (via `type_of%`) that the proved theorem has
exactly the challenge's type.

## Challenge 2 — `K_RDegenerateGraphs.lean`

The full conjecture, refuted at every level, with the degeneracy pinned
exactly and the exponent gain explicit:

> For every `r ≥ 2` there exist `q : ℕ` and a graph `H` on `Fin q` such
> that `H` is connected, bipartite, `r`-degenerate, **not**
> `(r−1)`-degenerate, and for some `c > 0`,
> `c · n^(2 − 1/r + 1/(28 r²)) ≤ ex(n; H)` for all sufficiently large `n`.

Points to check:

- The definitions of `neighborsWithin` and `IsDegenerate` are
  token-identical to Challenge 1's.
- `¬ IsDegenerate (r-1) H` together with `IsDegenerate r H` pins the
  degeneracy of `H` to exactly `r` — the forbidden graph is genuinely at
  level `r`, not accidentally sparser.
- The gain `1/(28 r²)` is a literal in the exponent; nothing is hidden
  behind an existential `ε`.
- The degeneracy conjecture predicts `ex(n; H) = O(n^(2 − 1/r))` for `r`-degenerate
  bipartite `H`; the statement exhibits a polynomial excess at every `r`.

## Challenge 3 — `K_WindowLaw.lean` (Theorem 1.3(a))

The asymptotic law for the feasibility window of the method. Unlike
Challenges 1–2 this is not a pure graph-theoretic statement: the
quantities are defined from scratch inside the file, and **the
definitions are the content** — review them against §§4–5 of the README.

> For every fixed `λ > 0` with `λ ln 2 < 1`:
> `r² · width(r, λ) → λ⁴ ln³2 / 64` as `r → ∞`.

The definitions to verify, in dependency order:

- `binaryEntropy x = Real.binEntropy x / Real.log 2` — binary entropy in
  bits (mathlib's `binEntropy` is in nats).
- `Gfun r lam q v` — the Gibbs objective
  `h(q)/2 + Σ_{j≤r} C(r,j) q^j (1−q)^{r−j} · log₂(√(1−v)·2^(−λj/r) + √v·2^(−λ(r−j)/r))`.
  This is the entropy functional whose supremum governs exclusion of the
  layered graph in the random host.
- `supG r lam` — supremum of `Gfun` over `(q,v) ∈ [0,1]²` (as an `sSup`
  of the image, so no differentiability or attainment is presupposed).
- `tauOf r lam = 1/2 − λ ln 2/(4r)` — the tuned Hamming radius.
- `Aside = λ·τ + supG` (exclusion threshold), `Cside = r·h(τ) − (r−1)`
  (density threshold), `width = Cside − Aside` (the feasibility window:
  admissible edge-density exponents `β` are those with `A < β < C`).
- `Wconst lam = λ⁴ ln³2 / 64` — the limiting constant.

The statement says the window is positive for large `r` (its scaled
width converges to a positive constant), for every subcritical weight
`λ ln 2 < 1`. The companion sharpness result (divergence to `−∞` for
`λ > 1/ln 2`) is proved in the development (`WindowSharp.lean`) but is not
part of this challenge.

## Challenge 4 — `K_FamilyLaw.lean` (Theorem 1.3(b))

The exponent family law. Same from-scratch definitions as Challenge 3,
plus:

- `epsMaxR r lam β = (Cside − β) / (r(1 − β))` — the method's maximal
  exponent gain when the host density parameter is `β`.
- `nuR r = ln r / r` and `lamR r = (1 − ν_r)/ln 2` — the tuned weight
  sequence approaching the critical weight `1/ln 2` from below.
- `betaTheta r lam θ = Aside + θ·width` — the in-window family: `θ = 0`
  is the exclusion edge `A`, `θ = 1` the density edge `C`.

> For every fixed `θ`:
> `8 r² · epsMaxR(r, λ_r, β_θ) → 1 − θ` as `r → ∞`.

Points to check:

- At `θ = 1/2` (the midpoint of the window) this gives `16 r² ε → 1`, i.e. the midpoint
  constant `1/(16 r²)`.
- As `θ → 0` the limit approaches the supremal constant `1/(8 r²)`; it is
  approached but not attained (the window edge itself is excluded).
  Together with the antitonicity of `epsMaxR` in `β`
  (`DegeneracyLawB.epsMaxR_anti` in `proofs/lib/LedgerAsym.lean`) this
  identifies `1/8` as the exact asymptotic ceiling of the method.
- Caveat, stated plainly: this challenge is about `epsMaxR`, a quantity
  *defined in the statement* — it asserts the asymptotics of the method's
  ledger, not a graph-theoretic fact. Its graph-theoretic consequences
  are what Challenges 1–2 certify (with `1/(28 r²)` and, at `r = 3`,
  `1/160` — see `RDegenerateGraphsTarget.threeDegenerateExtremalCounterexample_sharp`).

---

## What Comparator does and does not certify

Certifies (mechanically, per challenge):

1. The solution contains a theorem with the same fully qualified name
   whose statement — including every auxiliary definition it mentions —
   is identical to the challenge's.
2. The proof uses no axioms beyond `propext`, `Quot.sound`,
   `Classical.choice` (in particular no `sorryAx`).
3. The proof replays through the Lean kernel.

Does not certify:

- That the statements *mean* what the prose claims — that is exactly the
  human review requested above.
- The challenge files themselves are trusted input: review them, not the
  solutions (the solutions need no trust; that is the point of the
  procedure).

Note on sandboxing: on Linux, Comparator builds the solution inside a
`landrun` sandbox so that adversarial solution files cannot compromise
the judge. When judging this repository's own solutions on macOS, the
`fake-landrun.sh` shim (which does not sandbox) is sufficient; judging
untrusted third-party solutions should be done on Linux with real
`landrun`.
