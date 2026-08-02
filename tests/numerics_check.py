#!/usr/bin/env python3
"""Standalone numerical falsification harness (independent of Lean).

Reimplements the definitions of lib/LawDefs.lean and lib/LedgerR.lean in
floating point and checks, outside the proof assistant, that:

 1. r^2 * width(r, lam) approaches W(lam) = lam^4 ln^3(2)/64 from below for
    subcritical lam (Theorem 3(a));
 2. r^2 * width(r, lam) goes strongly negative for supercritical lam
    (Prop 6.3, threshold sharpness);
 3. the numerical maximizer of G_r over [0,1]^2 is the center (1/2, 1/2)
    for subcritical lam (Lemma B);
 4. 8 r^2 epsMax(beta_theta) approaches 1 - theta for the whole in-window
    family (Theorem 3(b) family law), midpoint theta = 1/2 giving 1/16;
 5. the layered r-subset pattern at the proof's parameter regime
    (baseSize >= r + 1) has exact degeneracy r, checked by graph peeling.

These are floating-point sanity checks, not proofs: a failure is a genuine
counterexample to a claimed inequality; success is redundancy on top of
the kernel-checked Lean development.

Run: python3 tests/numerics_check.py   (exit code 0 = all checks pass)
"""

import itertools
import math
import sys
from math import comb, log, sqrt

LOG2 = log(2.0)
failures = []


def check(name, ok, detail=""):
    print(f"{'ok  ' if ok else 'FAIL'} {name}" + (f"  [{detail}]" if detail else ""))
    if not ok:
        failures.append(name)


def h(x):  # binary entropy, bits
    if x <= 0.0 or x >= 1.0:
        return 0.0
    return -(x * log(x) + (1 - x) * log(1 - x)) / LOG2


def Gfun(r, lam, q, v):  # lib/LawDefs.lean Gfun
    s = h(q) / 2
    lgr = math.lgamma(r + 1)
    for j in range(r + 1):
        # binomial weight in log space (safe for large r)
        lw = lgr - math.lgamma(j + 1) - math.lgamma(r - j + 1)
        if 0.0 < q < 1.0:
            lw += j * log(q) + (r - j) * log(1 - q)
        elif (q == 0.0 and j > 0) or (q == 1.0 and j < r):
            continue
        inner = sqrt(max(1 - v, 0.0)) * 2 ** (-(lam * j) / r) + sqrt(
            max(v, 0.0)
        ) * 2 ** (-(lam * (r - j)) / r)
        s += math.exp(lw) * log(inner) / LOG2
    return s


def supG_center(r, lam):
    return Gfun(r, lam, 0.5, 0.5)


def tauOf(r, lam):
    return 0.5 - lam * LOG2 / (4 * r)


def Aside(r, lam):  # with sup G at the center (Lemma B)
    return lam * tauOf(r, lam) + supG_center(r, lam)


def Cside(r, tau):
    return r * h(tau) - (r - 1)


def width(r, lam):
    return Cside(r, tauOf(r, lam)) - Aside(r, lam)


def Wconst(lam):
    return lam**4 * LOG2**3 / 64


def epsMax(r, lam, beta):  # lib/LedgerR.lean epsMaxR
    return (Cside(r, tauOf(r, lam)) - beta) / (r * (1 - beta))


def lamR(r):  # tuned schedule of Theorem 3(b)
    return (1 - log(r) / r) / LOG2


def betaTheta(r, lam, theta):
    return Aside(r, lam) + theta * width(r, lam)


# ---- 1. subcritical convergence from below --------------------------------
for lam in (0.5, 1.0, 1.35, 1.44):
    W = Wconst(lam)
    prev = -math.inf
    monotone_ok, below_ok = True, True
    for r in (5, 10, 20, 40, 80, 160):
        val = r**2 * width(r, lam)
        monotone_ok &= val >= prev - 1e-12
        below_ok &= val <= W + 1e-9
        prev = val
    rel = abs(prev - W) / W
    check(
        f"3(a) lam={lam}: r^2*width -> W from below",
        monotone_ok and below_ok and rel < 0.05,
        f"r=160: {prev:.8f} vs W={W:.8f}",
    )

# ---- 2. supercritical divergence ------------------------------------------
# Above the threshold the sup of G_r is OFF-center, so compute it by grid
# search (a grid under-estimates the sup, hence over-estimates the width —
# conservative for a negativity check).
def width_gridsup(r, lam, n=60):
    sup = max(
        Gfun(r, lam, q / n, v / n) for q in range(1, n) for v in range(1, n)
    )
    return Cside(r, tauOf(r, lam)) - (lam * tauOf(r, lam) + sup)


for lam in (1.5, 2.0):
    vals = [r**2 * width_gridsup(r, lam) for r in (10, 30, 90)]
    check(
        f"6.3 lam={lam}: r^2*width decreasing and negative",
        vals[2] < vals[1] < 0,
        f"{[f'{v:.3f}' for v in vals]}",
    )

# ---- 3. Lemma B: center maximization (grid search) ------------------------
for lam in (0.5, 1.0, 1.35, 1.42):
    for r in (2, 5, 20):
        center = Gfun(r, lam, 0.5, 0.5)
        best = max(
            Gfun(r, lam, q / 40, v / 40)
            for q in range(1, 40)
            for v in range(1, 40)
        )
        check(
            f"B lam={lam} r={r}: sup G on grid = center",
            best <= center + 1e-9,
            f"grid max {best:.9f} vs center {center:.9f}",
        )

# ---- 4. Theorem 3(b) family law -------------------------------------------
r_big = 20000
for theta in (0.1, 0.25, 0.5, 0.9):
    val = 8 * r_big**2 * epsMax(r_big, lamR(r_big), betaTheta(r_big, lamR(r_big), theta))
    check(
        f"3(b) theta={theta}: 8 r^2 epsMax(beta_theta) ~ 1-theta",
        abs(val - (1 - theta)) < 0.02,
        f"r={r_big}: {val:.5f} vs {1 - theta}",
    )

# ---- 4b. Theorem 2's explicit constant: (theta,eta)=(1/4,1/4) ledger -------
# eps = (1-eta)(1-theta) * width / (r (1 - beta_theta)) must clear 1/(48 r^2)
# for every r >= 2 (Lean: DegeneracyLedgerSharp.eps_quarter_48).
lam2 = 27 / 20
vals = []
for r in range(2, 400):
    wd = width(r, lam2)
    beta = Aside(r, lam2) + 0.25 * wd
    vals.append(r**2 * 0.75 * 0.75 * wd / (r * (1 - beta)))
check(
    "Thm2 constant: min r^2 eps at (1/4,1/4) >= 1/48",
    min(vals) >= 1 / 48,
    f"min {min(vals):.6f} (=1/{1/min(vals):.1f}) vs 1/48={1/48:.6f}",
)

# ---- 5. exact degeneracy of the layered pattern ----------------------------
def layered(base, r, depth):
    layers = [[("L0", i) for i in range(base)]]
    edges = set()
    for d in range(depth):
        nxt = []
        for S in itertools.combinations(layers[-1], r):
            child = (f"L{d + 1}", S)
            nxt.append(child)
            for p in S:
                edges.add(frozenset((child, p)))
        layers.append(nxt)
    return [v for L in layers for v in L], edges


def degeneracy(V, E):
    adj = {v: set() for v in V}
    for e in E:
        a, b = tuple(e)
        adj[a].add(b)
        adj[b].add(a)
    left, deg = set(V), 0
    d = {v: len(adj[v]) for v in V}
    while left:
        v = min(left, key=lambda x: d[x])
        deg = max(deg, d[v])
        left.remove(v)
        for u in adj[v]:
            if u in left:
                d[u] -= 1
    return deg


for r, base, depth in [(2, 3, 1), (2, 8, 1), (2, 4, 2), (3, 4, 1), (3, 18, 1), (4, 5, 1)]:
    V, E = layered(base, r, depth)
    check(
        f"degeneracy r={r} base={base} depth={depth} (base >= r+1)",
        degeneracy(V, E) == r,
        f"|V|={len(V)} |E|={len(E)} got {degeneracy(V, E)}",
    )

print()
if failures:
    print(f"{len(failures)} check(s) FAILED: {failures}")
    sys.exit(1)
print("all checks passed")
