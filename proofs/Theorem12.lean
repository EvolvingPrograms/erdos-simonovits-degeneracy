import AssemblyR

/-!
# Theorem 1.2: the counterexample at every level `r ≥ 2`

For every `r ≥ 2` there is a connected bipartite graph `H_r` of degeneracy
exactly `r` and a constant `c > 0` with

  `c · n^(2 - 1/r + 1/(28 r²)) ≤ ex(n, H_r)`  eventually,

refuting `ex(n; H) = O(n^(2 - 1/r))` (Erdős problem #146) at every level.

The assembly -- the forbidden graph, the sparsified Hamming host, the entropy
obstruction and the ledger that turns the window into an exponent gain -- is
`proofs/lib/AssemblyR.lean`. This file states the target theorems.

The `r = 3` specialization of the same pipeline, with the sharp constant
`1/160`, is stated in `Theorem12r3.lean`.
-/
/-! ## The target statement -/

namespace RDegenerateGraphsTarget

open Filter Finset SimpleGraph

noncomputable def neighborsWithin {V : Type*} (G : SimpleGraph V)
    (s : Finset V) (v : V) : Finset V := by
  classical
  exact s.filter (G.Adj v)

def IsDegenerate {V : Type*} (r : ℕ) (G : SimpleGraph V) : Prop :=
  ∀ s : Finset V, s.Nonempty →
    ∃ v ∈ s, (neighborsWithin G s v).card ≤ r

open Classical in
theorem rDegenerateExtremalCounterexample (r : ℕ) (hr : 2 ≤ r) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsDegenerate r H ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + ε) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  obtain ⟨q, H, hcon, hbip, hdeg, -, hbnd⟩ :=
    RAssembly.rDegenerateExtremalCounterexample r hr
  exact ⟨q, H, hcon, hbip, hdeg, hbnd⟩

-- The same, with the degeneracy pinned exactly: `H` is `r`-degenerate but
-- not `(r-1)`-degenerate.
open Classical in
theorem rDegenerateExtremalCounterexample_exact (r : ℕ) (hr : 2 ≤ r) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsDegenerate r H ∧
      ¬ IsDegenerate (r - 1) H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (28 * (r : ℝ) ^ 2)) ≤
            (SimpleGraph.extremalNumber n H : ℝ) :=
  RAssembly.rDegenerateExtremalCounterexample_explicit r hr

-- The same, with the exponent gain pinned to `ε = 1/(28 r²)`.
open Classical in
theorem rDegenerateExtremalCounterexample_explicit (r : ℕ) (hr : 2 ≤ r) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsDegenerate r H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (28 * (r : ℝ) ^ 2)) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  obtain ⟨q, H, hcon, hbip, hdeg, -, hbnd⟩ :=
    RAssembly.rDegenerateExtremalCounterexample_explicit r hr
  exact ⟨q, H, hcon, hbip, hdeg, hbnd⟩

-- Compatibility form at the previous constant `ε = 1/(110 r²)` (weaker
-- exponent, follows from the `1/(28 r²)` statement by monotonicity).
open Classical in
theorem rDegenerateExtremalCounterexample_explicit_110 (r : ℕ) (hr : 2 ≤ r) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsDegenerate r H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (110 * (r : ℝ) ^ 2)) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  obtain ⟨q, H, hcon, hbip, hdeg, c, hc0, hbnd⟩ :=
    rDegenerateExtremalCounterexample_explicit r hr
  refine ⟨q, H, hcon, hbip, hdeg, c, hc0, ?_⟩
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  filter_upwards [hbnd, Filter.eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hexp : 1 / (110 * (r : ℝ) ^ 2) ≤ 1 / (28 * (r : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((r : ℝ))]
  have hmono : (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (110 * (r : ℝ) ^ 2)) ≤
      (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (28 * (r : ℝ) ^ 2)) :=
    Real.rpow_le_rpow_of_exponent_le hn1' (by linarith)
  calc c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (110 * (r : ℝ) ^ 2))
      ≤ c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (28 * (r : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hmono hc0.le
    _ ≤ (SimpleGraph.extremalNumber n H : ℝ) := hn

end RDegenerateGraphsTarget
