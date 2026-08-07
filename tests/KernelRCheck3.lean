import KernelR
import Entropy3

/-!
# Sanity check: `KernelR` at `r = 3` is `Kernel3`

`KernelR` states everything relative to the hypothesis
`RGenericKernel.TypeEntropyBound r A lam`.  This file discharges that
hypothesis at `r = 3` from `Entropy3`'s hand-certified
`ThreeDegenerateGraphs.conditional_entropy_bound`, confirming that the
`r`-generic packaging is faithful: the `r+1` binomially weighted terms of
`TypeEntropyBound` expand to exactly the four terms of the `r = 3` lemma.

Consequently every `KernelR` theorem specializes at `r = 3` to its `Kernel3`
counterpart (with the `r²/L = 9/L` without-replacement correction in place of
the published `4/L`).

This file is *not* imported by `KernelR`, which depends only on
`CompactnessAndDegeneracy`.
-/

open RGenericKernel Finset

/-- The `r = 3` instance of the `KernelR` entropy hypothesis, with
`A₀ = 17/80` and `λ = 7/4`. -/
theorem typeEntropyBound_three : TypeEntropyBound 3 (17 / 80) (7 / 4) := by
  intro q v d p hq hq' hv0 hv1 hp0 hp1 hv hd
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add] at hv hd ⊢
  norm_num at hv hd ⊢
  refine (le_of_eq (by ring)).trans
    ((ThreeDegenerateGraphs.conditional_entropy_bound q v d (p 0) (p 1) (p 2) (p 3)
      hq hq' hv0 hv1 (hp0 0) (hp1 0) (hp0 1) (hp1 1) (hp0 2) (hp1 2) (hp0 3) (hp1 3)
      (by linarith [hv]) (by linarith [hd])).trans (le_of_eq (by ring)))
