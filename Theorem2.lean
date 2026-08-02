import SamplingR
import BridgeR
import Theorem3a
import LedgerR
import LedgerSharp
import ExactDegeneracy

/-!
# Theorem 2: the `r`-generic degeneracy counterexample

For every `r ≥ 2` there is a connected bipartite `r`-degenerate graph `H` and
constants `c, ε > 0` with `c · n^(2 − 1/r + ε) ≤ ex(n, H)` eventually.

This is the `r`-generic analogue of `Theorem1.lean` (the `r = 3` assembly).
The structure follows `research/results_Z_lean_bridgeR.md` §5:

* **Block A** — the forbidden graph: `RParentSystem`, the layered `r`-graph on
  `RGenericProfiles.RLayer`, bipartiteness, `r`-degeneracy, connectivity, and
  the transport to a graph on `Fin q`.
* **Block D** — the asymptotic endgame: host vertex count, the bracketing
  argument, padding, and `extremalNumber` monotonicity.
* **Block E** — the numeric parameters, generic in `r`, taken from `LedgerR`
  (`betaMid`, `deltaR`, `sR`, `epsR`) with the window supplied by
  `DegeneracyLaw.width_pos_all` (proved below) and the two-sided window bounds
  of `Theorem3a`.
* **Block F** — the `SimpleGraph.Copy` transport (`Theorem1.lean` 1018–1555),
  phrased over the generic counterparts, on top of `BridgeR` §7.
-/

namespace DegeneracyLaw

/-- **Theorem 2's analytic engine, unconditional.** Window positivity at
`λ = 27/20` for every `r ≥ 2`: Lemma B (`LemmaB.supG_eq_center`) discharges the
`hB` hypothesis of `Theorem3a.width_pos_at_135'`. -/
theorem width_pos_all (r : ℕ) (hr : 2 ≤ r) : 0 < width r (27/20) :=
  width_pos_at_135' r hr
    (fun r' hr' => LemmaB.supG_eq_center r' (27/20) hr' (by norm_num) (by norm_num))

end DegeneracyLaw

namespace RAssembly

open Finset TwoDegenerateGraphs RGenericProfiles RGenericBridge RGenericKernel
open RGenericSampling ThreeSampling
open Filter Topology
open scoped BigOperators NNReal

/-! ## Block A: the forbidden graph -/

/-- A `ParentSystem` with at most `r` parents per vertex. -/
structure RParentSystem (r : ℕ) (V : Type*) where
  level : V → ℕ
  parents : V → Finset V
  parent_level : ∀ ⦃v u : V⦄, u ∈ parents v → level u + 1 = level v
  parent_card : ∀ v : V, (parents v).card ≤ r

namespace RParentSystem

variable {r : ℕ}

def graph {V : Type*} (P : RParentSystem r V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v u => u ∈ P.parents v)

theorem graph_adj_iff {V : Type*} (P : RParentSystem r V) (v u : V) :
    (P.graph).Adj v u ↔ v ≠ u ∧ (u ∈ P.parents v ∨ v ∈ P.parents u) := Iff.rfl

theorem graph_isBipartite {V : Type*} (P : RParentSystem r V) :
    P.graph.IsBipartite := by
  refine ⟨SimpleGraph.Coloring.mk
    (fun v => (⟨P.level v % 2, by omega⟩ : Fin 2)) ?_⟩
  intro v u hadj
  apply Fin.ne_of_val_ne
  change P.level v % 2 ≠ P.level u % 2
  rcases (P.graph_adj_iff v u).mp hadj with ⟨_, huv | huv⟩
  · have hlevel := P.parent_level huv
    omega
  · have hlevel := P.parent_level huv
    omega

theorem graph_isDegenerate {V : Type*} (P : RParentSystem r V) :
    IsDegenerate r P.graph := by
  classical
  intro s hs
  obtain ⟨v, hv, hmax⟩ := Finset.exists_max_image s P.level hs
  refine ⟨v, hv, ?_⟩
  have hsubset : neighborsWithin P.graph s v ⊆ P.parents v := by
    intro u hu
    have hus : u ∈ s ∧ P.graph.Adj v u := by
      simpa [neighborsWithin] using hu
    rcases (P.graph_adj_iff v u).mp hus.2 with ⟨_, hparent | hchild⟩
    · exact hparent
    · have hlevel := P.parent_level hchild
      have hle := hmax u hus.1
      omega
  exact (Finset.card_le_card hsubset).trans (P.parent_card v)

end RParentSystem

/-! ### The layered `r`-graph -/

abbrev RVertex (baseSize r depth : ℕ) :=
  Σ i : Fin (depth + 1), RLayer baseSize r i.val

def rLayerEmbedding (baseSize r depth i : ℕ) (hi : i < depth + 1) :
    RLayer baseSize r i ↪ RVertex baseSize r depth where
  toFun v := ⟨⟨i, hi⟩, v⟩
  inj' := by intro v w heq; cases heq; rfl

noncomputable def rParents (baseSize r depth : ℕ) :
    RVertex baseSize r depth → Finset (RVertex baseSize r depth)
  | ⟨⟨0, _⟩, _⟩ => ∅
  | ⟨⟨i + 1, hi⟩, v⟩ =>
      v.val.map (rLayerEmbedding baseSize r depth i (by omega))

noncomputable def rParentSystem (baseSize r depth : ℕ) :
    RParentSystem r (RVertex baseSize r depth) where
  level v := v.1.val
  parents := rParents baseSize r depth
  parent_level := by
    classical
    rintro ⟨⟨i, hi⟩, v⟩ ⟨⟨j, hj⟩, u⟩ hparent
    cases i with
    | zero => simp [rParents] at hparent
    | succ i =>
        change {parents : Finset (RLayer baseSize r i) // parents.card = r} at v
        simp only [rParents, Finset.mem_map] at hparent
        obtain ⟨w, _, hw⟩ := hparent
        have hlevels := congrArg
          (fun z : RVertex baseSize r depth => z.1.val) hw
        change i = j at hlevels
        change j + 1 = i + 1
        omega
  parent_card := by
    classical
    rintro ⟨⟨i, hi⟩, v⟩
    cases i with
    | zero => simp [rParents]
    | succ i =>
        change {parents : Finset (RLayer baseSize r i) // parents.card = r} at v
        simp [rParents, v.property]

def rBaseVertex (baseSize r depth : ℕ) (a : Fin baseSize) :
    RVertex baseSize r depth :=
  rLayerEmbedding baseSize r depth 0 (by omega) a

theorem rLayer_reaches_base (baseSize r depth : ℕ) (hr : 1 ≤ r) :
    ∀ (i : ℕ) (hi : i < depth + 1) (v : RLayer baseSize r i),
      ∃ a : Fin baseSize,
        (rParentSystem baseSize r depth).graph.Reachable
          (rLayerEmbedding baseSize r depth i hi v)
          (rBaseVertex baseSize r depth a) := by
  intro i
  induction i with
  | zero => intro hi v; exact ⟨v, SimpleGraph.Reachable.rfl⟩
  | succ i ih =>
      intro hi v
      change {parents : Finset (RLayer baseSize r i) // parents.card = r} at v
      have hnonempty : v.val.Nonempty := by
        apply Finset.card_pos.mp; rw [v.property]; omega
      obtain ⟨parent, hparent⟩ := hnonempty
      let lower := rLayerEmbedding baseSize r depth i (by omega) parent
      let upper := rLayerEmbedding baseSize r depth (i + 1) hi v
      have hedge : (rParentSystem baseSize r depth).graph.Adj upper lower := by
        apply (RParentSystem.graph_adj_iff _ upper lower).mpr
        constructor
        · intro heq
          have hlevels := congrArg
            (fun x : RVertex baseSize r depth => x.1.val) heq
          change i + 1 = i at hlevels
          omega
        · left
          change lower ∈ rParents baseSize r depth upper
          change lower ∈
            v.val.map (rLayerEmbedding baseSize r depth i (by omega))
          exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
      obtain ⟨a, ha⟩ := ih (by omega) parent
      exact ⟨a, hedge.reachable.trans ha⟩

theorem rBaseVertices_reachable (baseSize r depth : ℕ)
    (hr : 2 ≤ r) (hbase : r ≤ baseSize) (hdepth : 0 < depth)
    (a b : Fin baseSize) :
    (rParentSystem baseSize r depth).graph.Reachable
      (rBaseVertex baseSize r depth a)
      (rBaseVertex baseSize r depth b) := by
  classical
  letI : DecidableEq (RLayer baseSize r 0) := Classical.decEq _
  let a' : RLayer baseSize r 0 := a
  let b' : RLayer baseSize r 0 := b
  let s : Finset (RLayer baseSize r 0) := {a', b'}
  have hcard : s.card ≤ r :=
    (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton]; omega)
  have huniv : r ≤ (Finset.univ : Finset (RLayer baseSize r 0)).card := by
    have hc : Fintype.card (RLayer baseSize r 0) = baseSize :=
      rLayer_card_zero baseSize r
    simpa [Finset.card_univ, hc] using hbase
  obtain ⟨c, hsub, -, hcr⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ s) hcard huniv
  have ha : a' ∈ c := hsub (Finset.mem_insert_self _ _)
  have hb : b' ∈ c := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  let sub : RLayer baseSize r 1 := ⟨c, hcr⟩
  let bridge := rLayerEmbedding baseSize r depth 1 (by omega) sub
  have hadj (x : RLayer baseSize r 0) (hx : x ∈ c) :
      (rParentSystem baseSize r depth).graph.Adj
        bridge (rBaseVertex baseSize r depth x) := by
    apply (RParentSystem.graph_adj_iff _ bridge _).mpr
    constructor
    · intro heq
      have hlevels := congrArg
        (fun z : RVertex baseSize r depth => z.1.val) heq
      change 1 = 0 at hlevels
      omega
    · left
      change rBaseVertex baseSize r depth x ∈ rParents baseSize r depth bridge
      change rLayerEmbedding baseSize r depth 0 (by omega) x ∈
        c.map (rLayerEmbedding baseSize r depth 0 (by omega))
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
  exact (hadj a ha).symm.reachable.trans (hadj b hb).reachable

theorem rGraph_connected (baseSize r depth : ℕ)
    (hr : 2 ≤ r) (hbase : r ≤ baseSize) (hdepth : 0 < depth) :
    (rParentSystem baseSize r depth).graph.Connected := by
  have hpos : 0 < baseSize := by omega
  let root : Fin baseSize := ⟨0, hpos⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨rBaseVertex baseSize r depth root, ?_⟩
  rintro ⟨⟨i, hi⟩, v⟩
  obtain ⟨a, ha⟩ := rLayer_reaches_base baseSize r depth (by omega) i hi v
  exact (rBaseVertices_reachable baseSize r depth hr hbase hdepth root a).trans ha.symm

theorem rGraph_isBipartite (baseSize r depth : ℕ) :
    (rParentSystem baseSize r depth).graph.IsBipartite :=
  RParentSystem.graph_isBipartite _

theorem rGraph_isDegenerate (baseSize r depth : ℕ) :
    IsDegenerate r (rParentSystem baseSize r depth).graph :=
  RParentSystem.graph_isDegenerate _

noncomputable instance rVertexFintype (baseSize r depth : ℕ) :
    Fintype (RVertex baseSize r depth) := by
  classical infer_instance

noncomputable def rGraphOverFin (baseSize r depth : ℕ) :
    SimpleGraph (Fin (Fintype.card (RVertex baseSize r depth))) :=
  (rParentSystem baseSize r depth).graph.overFin rfl

noncomputable def rGraphOverFinIso (baseSize r depth : ℕ) :
    (rParentSystem baseSize r depth).graph ≃g rGraphOverFin baseSize r depth :=
  (rParentSystem baseSize r depth).graph.overFinIso rfl

theorem isDegenerate_of_iso {V W : Type*} {r : ℕ}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : IsDegenerate r G) : IsDegenerate r H := by
  classical
  intro s hs
  let t : Finset V := s.map e.symm.toEquiv.toEmbedding
  have ht : t.Nonempty := by
    obtain ⟨w, hw⟩ := hs
    exact ⟨e.symm w, Finset.mem_map.mpr ⟨w, hw, rfl⟩⟩
  obtain ⟨v, hv, hcard⟩ := hG t ht
  refine ⟨e v, ?_, ?_⟩
  · obtain ⟨w, hw, heq⟩ := Finset.mem_map.mp hv
    have hwv : w = e v := by apply e.symm.toEquiv.injective; simpa using heq
    simpa [← hwv] using hw
  · have hneighbors :
        neighborsWithin H s (e v) = (neighborsWithin G t v).map e.toEquiv.toEmbedding := by
      ext w
      simp only [neighborsWithin, Finset.mem_filter, Finset.mem_map_equiv]
      have hmembership : e.symm w ∈ t ↔ w ∈ s := by
        constructor
        · intro hmember
          obtain ⟨u, hu, heq⟩ := Finset.mem_map.mp hmember
          have huw : u = w := e.symm.toEquiv.injective heq
          simpa [huw] using hu
        · intro hmember; exact Finset.mem_map.mpr ⟨w, hmember, rfl⟩
      have hadjacency : G.Adj v (e.symm w) ↔ H.Adj (e v) w := by
        simpa using (e.map_rel_iff (a := v) (b := e.symm w)).symm
      exact (and_congr hmembership hadjacency).symm
    rw [hneighbors, Finset.card_map]
    exact hcard

theorem rGraphOverFin_connected (baseSize r depth : ℕ)
    (hr : 2 ≤ r) (hbase : r ≤ baseSize) (hdepth : 0 < depth) :
    (rGraphOverFin baseSize r depth).Connected :=
  (rGraphOverFinIso baseSize r depth).connected_iff.mp
    (rGraph_connected baseSize r depth hr hbase hdepth)

theorem rGraphOverFin_isBipartite (baseSize r depth : ℕ) :
    (rGraphOverFin baseSize r depth).IsBipartite :=
  isBipartite_of_iso (rGraphOverFinIso baseSize r depth)
    (rGraph_isBipartite baseSize r depth)

theorem rGraphOverFin_isDegenerate (baseSize r depth : ℕ) :
    IsDegenerate r (rGraphOverFin baseSize r depth) :=
  isDegenerate_of_iso (rGraphOverFinIso baseSize r depth)
    (rGraph_isDegenerate baseSize r depth)

/-! ### Exact degeneracy: the lower bound

`IsDegenerate r` is only an upper bound (degeneracy at most `r`).  For
`baseSize ≥ r + 1` the layered graph also has degeneracy at least `r`, by
the generic two-layer witness `ExactDegeneracy.not_isDegenerate_of_layer_witness`
applied to layers 0 and 1. -/

theorem rGraph_not_isDegenerate (baseSize r depth : ℕ) (hr : 1 ≤ r)
    (hbase : r + 1 ≤ baseSize) (hdepth : 0 < depth) :
    ¬ IsDegenerate (r - 1) (rParentSystem baseSize r depth).graph := by
  classical
  have h0 : (0 : ℕ) < depth + 1 := by omega
  have h1 : (1 : ℕ) < depth + 1 := by omega
  set emb0 := rLayerEmbedding baseSize r depth 0 h0 with hemb0
  set emb1 := rLayerEmbedding baseSize r depth 1 h1 with hemb1
  -- layer-0 and layer-1 vertices sit at different levels, so never coincide
  have hne01 : ∀ (a : RLayer baseSize r 0) (c : RLayer baseSize r 1),
      emb0 a ≠ emb1 c := by
    intro a c heq
    have := congrArg (fun z : RVertex baseSize r depth => z.1.val) heq
    simp [hemb0, hemb1, rLayerEmbedding] at this
  -- adjacency between a root and a layer-1 child containing it
  have hadj : ∀ (a : RLayer baseSize r 0)
      (c : {parents : Finset (RLayer baseSize r 0) // parents.card = r}),
      a ∈ c.val →
        (rParentSystem baseSize r depth).graph.Adj (emb0 a) (emb1 c) := by
    intro a c hac
    refine ((rParentSystem baseSize r depth).graph_adj_iff _ _).mpr
      ⟨hne01 a c, Or.inr ?_⟩
    show emb0 a ∈ rParents baseSize r depth (emb1 c)
    exact Finset.mem_map_of_mem emb0 hac
  exact ExactDegeneracy.not_isDegenerate_of_layer_witness hr
    (by rw [rLayer_card_zero]; omega) emb0 emb1 hadj

/-- Exact degeneracy transported to the `Fin q` form. -/
theorem rGraphOverFin_not_isDegenerate (baseSize r depth : ℕ) (hr : 1 ≤ r)
    (hbase : r + 1 ≤ baseSize) (hdepth : 0 < depth) :
    ¬ IsDegenerate (r - 1) (rGraphOverFin baseSize r depth) := by
  intro h
  exact rGraph_not_isDegenerate baseSize r depth hr hbase hdepth
    (ExactDegeneracy.isDegenerate_of_iso (rGraphOverFinIso baseSize r depth).symm h)

/-! ### Layer equivalences and parent/child adjacency -/

noncomputable def rLayerFinEquiv (baseSize r layer : ℕ) :
    RLayer baseSize r layer ≃
      Fin (Fintype.card (RLayer baseSize r layer)) :=
  Fintype.equivFin (RLayer baseSize r layer)

noncomputable def rLayerSubEquiv (baseSize r layer : ℕ) :
    RLayer (Fintype.card (RLayer baseSize r layer)) r 1 ≃
      RLayer baseSize r (layer + 1) := by
  classical
  change
    {parents : Finset (Fin (Fintype.card (RLayer baseSize r layer))) //
        parents.card = r} ≃
      {parents : Finset (RLayer baseSize r layer) // parents.card = r}
  exact
    (rLayerFinEquiv baseSize r layer).symm.finsetCongr.subtypeEquiv
      (fun parents => by simp [Equiv.finsetCongr_apply])

theorem rLayerSub_nonempty {parentCount r : ℕ} (hparents : r ≤ parentCount) :
    Nonempty (RLayer parentCount r 1) := by
  apply Fintype.card_pos_iff.mp
  rw [rLayer_card_succ parentCount r 0, rLayer_card_zero]
  exact Nat.choose_pos hparents

theorem rGraph_parent_child_adj
    (baseSize r depth layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (child : RLayer baseSize r (layer + 1))
    (parent : RLayer baseSize r layer)
    (hparent : parent ∈ child.val) :
    (rParentSystem baseSize r depth).graph.Adj
      (rLayerEmbedding baseSize r depth (layer + 1) hlayer child)
      (rLayerEmbedding baseSize r depth layer (by omega) parent) := by
  apply (RParentSystem.graph_adj_iff _ _ _).mpr
  constructor
  · intro hequal
    have hlevels := congrArg
      (fun vertex : RVertex baseSize r depth => vertex.1.val) hequal
    change layer + 1 = layer at hlevels
    omega
  · left
    change rLayerEmbedding baseSize r depth layer (by omega) parent ∈
      rParents baseSize r depth
        (rLayerEmbedding baseSize r depth (layer + 1) hlayer child)
    change rLayerEmbedding baseSize r depth layer (by omega) parent ∈
      child.val.map (rLayerEmbedding baseSize r depth layer (by omega))
    exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩


/-! ## Block E: the parameters, generic in `r`

All constants come from `LedgerR`/`LedgerSharp` at `λ = 27/20`, at the
**optimized window position** `θ = ¼` with slack `η = ¼` (the midpoint
`θ = η = ½` of the paper costs a factor ≈ 2.3 in the final constant —
see `lib/LedgerSharp.lean` and Theorem 3(b)'s family law):

* `betaC r = β_r = A_r + ¼·width_r` (`betaTheta` at `θ = ¼`),
* `slackC r = δ_r = (β_r − A_r)/4 = width_r/16` (`deltaR`),
* `endpointC r = A_r = λ τ_r + sup G_r` (`Aside`) — the ledger endpoint,
* `epsC r = ¾ ε^max_r` (`epsR` at `η = ¼`),
* `depthC r = ⌈4/width_r⌉ + 1` (so `depth · increment > 1` at the
  per-layer increment `width_r/4`).

The only input is `0 < width r (27/20)` (`DegeneracyLaw.width_pos_all`,
unconditional) plus the *upper* window bound of Lemma 6.1 (`Theorem3a`). -/

namespace Params

open DegeneracyLaw DegeneracyLedger DegeneracyLawB TwoDegenerateGraphs

noncomputable def betaC (r : ℕ) : ℝ := betaTheta r (27 / 20) (1 / 4)
noncomputable def slackC (r : ℕ) : ℝ := deltaR r (27 / 20) (betaC r)
noncomputable def endpointC (r : ℕ) : ℝ := Aside r (27 / 20)
noncomputable def epsC (r : ℕ) : ℝ := epsR r (27 / 20) (betaC r) (1 / 4)
noncomputable def depthC (r : ℕ) : ℕ := ⌈4 / width r (27 / 20)⌉₊ + 1

theorem lam_log_le : (27 / 20 : ℝ) * Real.log 2 ≤ 1 := by
  have := Real.log_two_lt_d9; nlinarith

theorem lam_log_lt : (27 / 20 : ℝ) * Real.log 2 < 1 := by
  have := Real.log_two_lt_d9; nlinarith

theorem width_pos (r : ℕ) (hr : 2 ≤ r) : 0 < width r (27 / 20) :=
  DegeneracyLaw.width_pos_all r hr

/-- `W(27/20) = (27/20)^4 ln³2 / 64 ≤ 0.018`. -/
theorem Wconst_le : Wconst (27 / 20 : ℝ) ≤ 0.018 := by
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have hcube : Real.log 2 ^ 3 ≤ 0.3331 := by nlinarith [hlt, hn, sq_nonneg (Real.log 2)]
  rw [Wconst]
  nlinarith [hcube]

theorem Wconst_nonneg : (0 : ℝ) ≤ Wconst (27 / 20 : ℝ) :=
  (Wconst_pos (by norm_num)).le

/-- **The window upper bound**, from Lemma 6.1. -/
theorem width_le (r : ℕ) (hr : 2 ≤ r) : width r (27 / 20) ≤ 0.018 / (r : ℝ) ^ 2 := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have h := rsq_width_le_upperSeq (27 / 20) (by norm_num) lam_log_lt hr
  have hfac : upperSeq (27 / 20 : ℝ) r ≤ Wconst (27 / 20 : ℝ) := by
    rw [upperSeq]
    have : (0 : ℝ) ≤ 1 / (r : ℝ) := by positivity
    nlinarith [Wconst_nonneg]
  have hsq : (0 : ℝ) < (r : ℝ) ^ 2 := by positivity
  rw [le_div_iff₀ hsq]
  calc width r (27 / 20) * (r : ℝ) ^ 2 = (r : ℝ) ^ 2 * width r (27 / 20) := by ring
    _ ≤ upperSeq (27 / 20 : ℝ) r := h
    _ ≤ Wconst (27 / 20 : ℝ) := hfac
    _ ≤ 0.018 := Wconst_le

/-- `C_r(τ_r) ≥ 0.9` for every `r ≥ 2`: the entropy defect at `τ_r` is `O(1/r)`. -/
theorem Cside_ge (r : ℕ) (hr : 2 ≤ r) : (0.9 : ℝ) ≤ Cside r (tauOf r (27 / 20)) := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  have h := r_mul_one_sub_Cside_le r (27 / 20) hr (by norm_num) lam_log_le
  have h1 : (27 / 20 : ℝ) ^ 2 * Real.log 2 / 8 ≤ 0.157908 := by nlinarith [hlt]
  have hcube : Real.log 2 ^ 3 ≤ 0.3331 := by nlinarith [hlt, hn, sq_nonneg (Real.log 2)]
  have hden : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith [hr0]
  have h2 : 3 * (27 / 20 : ℝ) ^ 4 * Real.log 2 ^ 3 / (256 * (r : ℝ) ^ 2) ≤ 0.00325 := by
    rw [div_le_iff₀ (by positivity)]
    nlinarith [hcube, hden, Real.log_pos (by norm_num : (1 : ℝ) < 2)]
  have hsum : (r : ℝ) * (1 - Cside r (tauOf r (27 / 20))) ≤ 0.1657 := by linarith
  rcases le_or_gt (Cside r (tauOf r (27 / 20))) 1 with hle | hgt
  · nlinarith [hsum, hr0]
  · linarith

theorem betaC_spec (r : ℕ) :
    Cside r (tauOf r (27 / 20)) - betaC r = 3 / 4 * width r (27 / 20) := by
  have h := Cside_sub_betaTheta r (27 / 20) (1 / 4)
  unfold betaC
  linarith

theorem betaC_spec' (r : ℕ) : betaC r - Aside r (27 / 20) = width r (27 / 20) / 4 := by
  simp only [betaC, betaTheta]
  ring

theorem betaC_pos (r : ℕ) (hr : 2 ≤ r) : 0 < betaC r := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hC := Cside_ge r hr
  have hw := width_le r hr
  have hspec := betaC_spec r
  have hsq : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by nlinarith [hr0]
  have hquot : (0.018 : ℝ) / (r : ℝ) ^ 2 ≤ 0.0045 := by
    rw [div_le_iff₀ (by positivity)]; nlinarith
  linarith

theorem betaC_nonneg (r : ℕ) (hr : 2 ≤ r) : 0 ≤ betaC r := (betaC_pos r hr).le

theorem betaC_lt_one (r : ℕ) (hr : 2 ≤ r) : betaC r < 1 := by
  have hCle : Cside r (tauOf r (27 / 20)) ≤ 1 := by
    have h := one_sub_Cside r (tauOf r (27 / 20))
    have hent : binaryEntropy (tauOf r (27 / 20)) ≤ 1 := binaryEntropy_le_one _
    have hrpos : (0 : ℝ) ≤ (r : ℝ) := Nat.cast_nonneg r
    nlinarith [h, hent, hrpos]
  have hw := width_pos r hr
  have hspec := betaC_spec r
  linarith

theorem tauC_nonneg (r : ℕ) (hr : 2 ≤ r) : 0 ≤ tauOf r (27 / 20) := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have hlt : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [tauOf, sub_nonneg, div_le_iff₀ (by positivity)]
  nlinarith [hlt, hr0]

theorem tauC_le_one (r : ℕ) (hr : 2 ≤ r) : tauOf r (27 / 20) ≤ 1 := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by
    have : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
    linarith
  have hn : (0 : ℝ) ≤ Real.log 2 := Real.log_nonneg (by norm_num)
  rw [tauOf]
  have : (0 : ℝ) ≤ (27 / 20 : ℝ) * Real.log 2 / (4 * (r : ℝ)) := by positivity
  linarith

/-- `δ_r = width_r / 16`. -/
theorem slackC_eq (r : ℕ) : slackC r = width r (27 / 20) / 16 := by
  have h := betaC_spec' r
  simp only [slackC, deltaR]
  linarith

theorem slackC_pos (r : ℕ) (hr : 2 ≤ r) : 0 < slackC r := by
  rw [slackC_eq]; linarith [width_pos r hr]

/-- The per-layer potential increment is exactly `width_r / 4`. -/
theorem increment_eq (r : ℕ) :
    RGenericBridge.potentialIncrement (betaC r) (slackC r) (endpointC r) =
      width r (27 / 20) / 4 := by
  have h := betaC_spec' r
  simp only [RGenericBridge.potentialIncrement, endpointC, slackC_eq]
  linarith

theorem depthC_pos (r : ℕ) : 0 < depthC r := by
  simp [depthC]

theorem depthC_increment (r : ℕ) (hr : 2 ≤ r) :
    1 < (depthC r : ℝ) *
      RGenericBridge.potentialIncrement (betaC r) (slackC r) (endpointC r) := by
  have hw := width_pos r hr
  have hceil : 4 / width r (27 / 20) ≤ (⌈4 / width r (27 / 20)⌉₊ : ℝ) := Nat.le_ceil _
  have hcast : ((depthC r : ℕ) : ℝ) = (⌈4 / width r (27 / 20)⌉₊ : ℝ) + 1 := by
    simp [depthC]
  rw [increment_eq, hcast]
  have hlow : 4 / width r (27 / 20) * (width r (27 / 20) / 4) = 1 := by
    field_simp
  nlinarith [hceil, hw]

/-! ### The exponent -/

theorem epsMax_pos (r : ℕ) (hr : 2 ≤ r) : 0 < epsMaxR r (27 / 20) (betaC r) := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hb := betaC_lt_one r hr
  have hspec := betaC_spec r
  have hw := width_pos r hr
  rw [epsMaxR]
  apply div_pos (by linarith) (by nlinarith)

theorem epsC_pos (r : ℕ) (hr : 2 ≤ r) : 0 < epsC r := by
  have h := epsMax_pos r hr
  simp only [epsC, epsR]
  linarith

theorem epsC_lt_max (r : ℕ) (hr : 2 ≤ r) : epsC r < epsMaxR r (27 / 20) (betaC r) := by
  have h := epsMax_pos r hr
  simp only [epsC, epsR]
  linarith

/-- **The exponent gap.**  Any `ε < ε^max_r` satisfies the sampling hypothesis
`(1 − β)(2 − 1/r + ε) < 1 − 2β + h(τ_r)`; at `ε = ε^max_r` it is an equality. -/
theorem rExponentGap_of_lt {r : ℕ} {lam betaR eps : ℝ} (hr : 0 < r) (hb : betaR < 1)
    (heps : eps < epsMaxR r lam betaR) :
    RGenericSampling.RExponentGap r (tauOf r lam) betaR eps := by
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hden : (0 : ℝ) < (r : ℝ) * (1 - betaR) := by
    have : (0 : ℝ) < 1 - betaR := by linarith
    positivity
  have hkey : eps * ((r : ℝ) * (1 - betaR)) < Cside r (tauOf r lam) - betaR := by
    rw [epsMaxR, lt_div_iff₀ hden] at heps; exact heps
  have hC : (r : ℝ) * binaryEntropy (tauOf r lam)
      = Cside r (tauOf r lam) + ((r : ℝ) - 1) := by rw [Cside]; ring
  have hLHS : (r : ℝ) * ((1 - betaR) * ((2 - 1 / (r : ℝ)) + eps))
      = (1 - betaR) * (2 * (r : ℝ) - 1) + eps * ((r : ℝ) * (1 - betaR)) := by
    field_simp
  have hRHS : (r : ℝ) * (1 - 2 * betaR + binaryEntropy (tauOf r lam))
      = (r : ℝ) * (1 - 2 * betaR) + (Cside r (tauOf r lam) + ((r : ℝ) - 1)) := by
    rw [← hC]; ring
  have hmul : (r : ℝ) * ((1 - betaR) * ((2 - 1 / (r : ℝ)) + eps))
      < (r : ℝ) * (1 - 2 * betaR + binaryEntropy (tauOf r lam)) := by
    rw [hLHS, hRHS]; nlinarith [hkey]
  exact lt_of_mul_lt_mul_left hmul hrpos.le

end Params

/-! ## Block D: the asymptotic endgame -/

open Finset TwoDegenerateGraphs RGenericProfiles RGenericBridge RGenericKernel
open RGenericSampling ThreeSampling
open Filter Topology
open scoped BigOperators NNReal
open Params DegeneracyLaw DegeneracyLedger

/-- `β_r` as a nonnegative real, for the retention measure. -/
noncomputable def betaNN (r : ℕ) : ℝ≥0 := Real.toNNReal (betaC r)

theorem betaNN_coe (r : ℕ) (hr : 2 ≤ r) : ((betaNN r : ℝ≥0) : ℝ) = betaC r :=
  Real.coe_toNNReal _ (betaC_nonneg r hr)

/-- The tuned Hamming radius `⌊τ_r · m⌋`. -/
noncomputable def radiusC (r dimension : ℕ) : ℕ :=
  RGenericSampling.rHammingRadius (tauOf r (27 / 20)) dimension

/-- The extremal exponent `2 − 1/r + ε_r`. -/
noncomputable def powerC (r : ℕ) : ℝ := (2 - 1 / (r : ℝ)) + epsC r

/-- The sampled edge entropy rate `(1 − 2β_r) ln 2 + h_nat(τ_r)`. -/
noncomputable def rateC (r : ℕ) : ℝ :=
  RGenericSampling.sampledREdgeEntropyRate (betaNN r) (tauOf r (27 / 20))

theorem powerC_pos (r : ℕ) (hr : 2 ≤ r) : 0 < powerC r := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have h1 : 1 / (r : ℝ) ≤ 1 := by
    rw [div_le_one (by linarith)]; linarith
  have := epsC_pos r hr
  unfold powerC; linarith

theorem exponentGap (r : ℕ) (hr : 2 ≤ r) :
    RGenericSampling.RExponentGap r (tauOf r (27 / 20)) (betaC r) (epsC r) :=
  rExponentGap_of_lt (by omega) (betaC_lt_one r hr) (epsC_lt_max r hr)

theorem rateC_gt (r : ℕ) (hr : 2 ≤ r) :
    (1 - betaC r) * powerC r * Real.log 2 < rateC r := by
  have h := RGenericSampling.sampledREdgeEntropyRate_gt (betaNN r) (r := r)
    (tauOf r (27 / 20)) (epsC r) (by rw [betaNN_coe r hr]; exact exponentGap r hr)
  rw [betaNN_coe r hr] at h
  unfold rateC powerC
  exact h

theorem rateC_pos (r : ℕ) (hr : 2 ≤ r) : 0 < rateC r := by
  have h := RGenericSampling.sampledREdgeEntropyRate_pos (betaNN r) (r := r)
    (tauOf r (27 / 20)) (epsC r) (by omega) (epsC_pos r hr).le
    (by rw [betaNN_coe r hr]; exact betaC_lt_one r hr)
    (by rw [betaNN_coe r hr]; exact exponentGap r hr)
  exact h

/-- Half the slack in the exponent inequality. -/
noncomputable def gapC (r : ℕ) : ℝ :=
  (rateC r - (1 - betaC r) * powerC r * Real.log 2) / 2

theorem gapC_pos (r : ℕ) (hr : 2 ≤ r) : 0 < gapC r := by
  have := rateC_gt r hr; unfold gapC; linarith

theorem rateC_eq_power (r : ℕ) :
    rateC r = (1 - betaC r) * powerC r * Real.log 2 + 2 * gapC r := by
  unfold gapC; ring

/-! ### The expected retained edge count grows like `exp(m · rate)` -/

theorem eventually_expectedRetainedEdge_entropy_lower (r : ℕ) (hr : 2 ≤ r)
    (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ dimension : ℕ in atTop,
      Real.exp ((dimension : ℝ) * (rateC r - loss)) / ((dimension + 1 : ℕ) : ℝ) ≤
        threeExpectedRetainedEdgeCount (betaNN r) dimension (radiusC r dimension) := by
  filter_upwards [RGenericSampling.eventually_rHammingRadius_binEntropy_ge
    (tauOf r (27 / 20)) (tauC_nonneg r hr) loss hloss] with dimension hentropy0
  have hentropy : Real.binEntropy (tauOf r (27 / 20)) - loss ≤
      Real.binEntropy ((radiusC r dimension : ℝ) / (dimension : ℝ)) := hentropy0
  have hdegree :
      Real.exp ((dimension : ℝ) *
          Real.binEntropy ((radiusC r dimension : ℝ) / (dimension : ℝ))) /
          ((dimension + 1 : ℕ) : ℝ) ≤
        ((∑ distance ∈ Finset.range (radiusC r dimension + 1),
          dimension.choose distance : ℕ) : ℝ) := by
    have hball := RGenericSampling.rHammingBall_card_entropy_lower
      (tauOf r (27 / 20)) (tauC_nonneg r hr) (tauC_le_one r hr) dimension
      (fun _ : Fin dimension => false)
    rw [hammingBall_card] at hball
    exact hball
  calc
    Real.exp ((dimension : ℝ) * (rateC r - loss)) / ((dimension + 1 : ℕ) : ℝ) =
      (threeRetentionProbability (betaNN r) dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        (Real.exp ((dimension : ℝ) *
            (Real.binEntropy (tauOf r (27 / 20)) - loss)) /
          ((dimension + 1 : ℕ) : ℝ)) := by
        rw [threeRetentionProbability_sq_mul_wordCount_eq_exp,
          ← mul_div_assoc, ← Real.exp_add]
        congr 1
        unfold rateC RGenericSampling.sampledREdgeEntropyRate
        ring_nf
    _ ≤ (threeRetentionProbability (betaNN r) dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        (Real.exp ((dimension : ℝ) *
            Real.binEntropy ((radiusC r dimension : ℝ) / (dimension : ℝ))) /
          ((dimension + 1 : ℕ) : ℝ)) := by gcongr
    _ ≤ (threeRetentionProbability (betaNN r) dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        ((∑ distance ∈ Finset.range (radiusC r dimension + 1),
          dimension.choose distance : ℕ) : ℝ) := by gcongr
    _ = threeExpectedRetainedEdgeCount (betaNN r) dimension (radiusC r dimension) := by
      rw [threeExpectedRetainedEdgeCount_eq]

theorem expectedRetainedEdgeCount_tendsto_atTop (r : ℕ) (hr : 2 ≤ r) :
    Tendsto
      (fun dimension : ℕ =>
        threeExpectedRetainedEdgeCount (betaNN r) dimension (radiusC r dimension))
      atTop atTop := by
  have hrate := rateC_pos r hr
  have hloss : 0 < rateC r / 2 := by positivity
  have hlower := eventually_expectedRetainedEdge_entropy_lower r hr (rateC r / 2) hloss
  have hgrowth := exp_mul_div_nat_succ_tendsto_atTop (rateC r / 2) hloss
  have hhalf : rateC r - rateC r / 2 = rateC r / 2 := by ring
  apply tendsto_atTop_mono' atTop _ hgrowth
  filter_upwards [hlower] with dimension hdimension
  simpa only [hhalf, mul_comm] using hdimension

theorem expectedRetainedEdgeCount_inv_tendsto_zero (r : ℕ) (hr : 2 ≤ r) :
    Tendsto
      (fun dimension : ℕ =>
        1 / threeExpectedRetainedEdgeCount (betaNN r) dimension (radiusC r dimension))
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    (expectedRetainedEdgeCount_tendsto_atTop r hr)
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]

/-! ### The host vertex count -/

noncomputable def vertexCountC (r dimension : ℕ) : ℕ :=
  ⌈3 * threeRetentionProbability (betaNN r) dimension * ((2 ^ dimension : ℕ) : ℝ)⌉₊

open Classical in
theorem retainedVertex_card_le_vertexCountC (r dimension : ℕ)
    (retained : Set (Bool × HammingWord dimension))
    (hvertices :
      threeRetainedVertexCount dimension retained <
        3 * threeRetentionProbability (betaNN r) dimension *
          ((2 ^ dimension : ℕ) : ℝ)) :
    Fintype.card retained ≤ vertexCountC r dimension := by
  have hreal : (Fintype.card retained : ℝ) ≤ (vertexCountC r dimension : ℝ) := by
    calc (Fintype.card retained : ℝ) = threeRetainedVertexCount dimension retained :=
          (threeRetainedVertexCount_eq_card dimension retained).symm
      _ ≤ 3 * threeRetentionProbability (betaNN r) dimension *
            ((2 ^ dimension : ℕ) : ℝ) := hvertices.le
      _ ≤ (vertexCountC r dimension : ℝ) := Nat.le_ceil _
  exact_mod_cast hreal

theorem vertexCountC_le_four_wordMean (r dimension : ℕ)
    (hmean : 1 ≤ threeRetentionProbability (betaNN r) dimension *
      ((2 ^ dimension : ℕ) : ℝ)) :
    (vertexCountC r dimension : ℝ) ≤
      4 * (threeRetentionProbability (betaNN r) dimension *
        ((2 ^ dimension : ℕ) : ℝ)) := by
  have hpos := threeRetentionProbability_pos (betaNN r) dimension
  have hargument :
      0 ≤ 3 * threeRetentionProbability (betaNN r) dimension *
        ((2 ^ dimension : ℕ) : ℝ) := by positivity
  have hceiling :
      (vertexCountC r dimension : ℝ) <
        3 * threeRetentionProbability (betaNN r) dimension *
          ((2 ^ dimension : ℕ) : ℝ) + 1 := by
    unfold vertexCountC
    exact Nat.ceil_lt_add_one hargument
  nlinarith

theorem eventually_vertexCountC_le_four_wordMean (r : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ dimension : ℕ in atTop,
      (vertexCountC r dimension : ℝ) ≤
        4 * (threeRetentionProbability (betaNN r) dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
  have hlarge := Filter.tendsto_atTop.1
    (threeRetentionProbability_mul_wordCount_tendsto_atTop (betaNN r)
      (by rw [betaNN_coe r hr]; exact betaC_lt_one r hr)) (1 : ℝ)
  filter_upwards [hlarge] with dimension hdimension
  exact vertexCountC_le_four_wordMean r dimension hdimension

theorem eventually_gapC_dominates_power_constant (r : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ dimension : ℕ in atTop,
      2 * (4 : ℝ) ^ powerC r ≤
        Real.exp (gapC r * (dimension : ℝ)) / ((dimension + 1 : ℕ) : ℝ) :=
  Filter.tendsto_atTop.1
    (exp_mul_div_nat_succ_tendsto_atTop (gapC r) (gapC_pos r hr))
    (2 * (4 : ℝ) ^ powerC r)

theorem eventually_vertexCountC_power_le_expectedRetainedEdge (r : ℕ) (hr : 2 ≤ r) :
    ∀ᶠ dimension : ℕ in atTop,
      (vertexCountC r dimension : ℝ) ^ powerC r ≤
        threeExpectedRetainedEdgeCount (betaNN r) dimension (radiusC r dimension) / 2 := by
  have hlower := eventually_expectedRetainedEdge_entropy_lower r hr (gapC r) (gapC_pos r hr)
  filter_upwards [hlower, eventually_vertexCountC_le_four_wordMean r hr,
    eventually_gapC_dominates_power_constant r hr] with dimension
    hedge_lower hvertex_bound hconstant_bound
  have hbeta : ((betaNN r : ℝ≥0) : ℝ) = betaC r := betaNN_coe r hr
  have hconstant_half :
      (4 : ℝ) ^ powerC r ≤
        (Real.exp (gapC r * (dimension : ℝ)) / ((dimension + 1 : ℕ) : ℝ)) / 2 := by
    linarith
  have hexponent :
      ((1 - ((betaNN r : ℝ≥0) : ℝ)) * (dimension : ℝ) * Real.log 2) * powerC r +
            gapC r * (dimension : ℝ) =
        (dimension : ℝ) * (rateC r - gapC r) := by
    rw [hbeta, rateC_eq_power]; ring
  have hppos := threeRetentionProbability_pos (betaNN r) dimension
  calc
    (vertexCountC r dimension : ℝ) ^ powerC r ≤
      (4 * (threeRetentionProbability (betaNN r) dimension *
        ((2 ^ dimension : ℕ) : ℝ))) ^ powerC r := by
        apply Real.rpow_le_rpow (by positivity) hvertex_bound (powerC_pos r hr).le
    _ = (4 : ℝ) ^ powerC r *
        Real.exp (((1 - ((betaNN r : ℝ≥0) : ℝ)) * (dimension : ℝ) *
          Real.log 2) * powerC r) := by
      rw [threeRetentionProbability_mul_wordCount_eq_exp,
        Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
    _ ≤ Real.exp (((1 - ((betaNN r : ℝ≥0) : ℝ)) * (dimension : ℝ) *
            Real.log 2) * powerC r) *
        ((Real.exp (gapC r * (dimension : ℝ)) / ((dimension + 1 : ℕ) : ℝ)) / 2) := by
      rw [mul_comm ((4 : ℝ) ^ powerC r)]
      exact mul_le_mul_of_nonneg_left hconstant_half (Real.exp_pos _).le
    _ = (Real.exp (((1 - ((betaNN r : ℝ≥0) : ℝ)) * (dimension : ℝ) *
            Real.log 2) * powerC r + gapC r * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
      rw [Real.exp_add]; ring
    _ = (Real.exp ((dimension : ℝ) * (rateC r - gapC r)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by rw [hexponent]
    _ ≤ threeExpectedRetainedEdgeCount (betaNN r) dimension (radiusC r dimension) / 2 := by
        gcongr

theorem vertexCountC_tendsto_atTop (r : ℕ) (hr : 2 ≤ r) :
    Tendsto (vertexCountC r) atTop atTop := by
  have hscaled :
      Tendsto (fun dimension : ℕ =>
          3 * (threeRetentionProbability (betaNN r) dimension *
            ((2 ^ dimension : ℕ) : ℝ))) atTop atTop :=
    (threeRetentionProbability_mul_wordCount_tendsto_atTop (betaNN r)
      (by rw [betaNN_coe r hr]; exact betaC_lt_one r hr)).const_mul_atTop (by norm_num)
  have hceiling := tendsto_nat_ceil_atTop.comp hscaled
  apply hceiling.congr'
  filter_upwards [] with dimension
  change ⌈3 * (threeRetentionProbability (betaNN r) dimension *
    ((2 ^ dimension : ℕ) : ℝ))⌉₊ = vertexCountC r dimension
  unfold vertexCountC
  congr 1
  ring

theorem vertexCountC_succ_le_two_mul (r : ℕ) (hr : 2 ≤ r) (dimension : ℕ) :
    vertexCountC r (dimension + 1) ≤ 2 * vertexCountC r dimension := by
  have hbeta : ((betaNN r : ℝ≥0) : ℝ) = betaC r := betaNN_coe r hr
  have hbpos : (0 : ℝ) < ((betaNN r : ℝ≥0) : ℝ) := by
    rw [hbeta]; exact betaC_pos r hr
  have hfactor :
      Real.exp ((1 - ((betaNN r : ℝ≥0) : ℝ)) * Real.log 2) ≤ (2 : ℝ) := by
    have hstep := Real.exp_le_exp.mpr
      (show (1 - ((betaNN r : ℝ≥0) : ℝ)) * Real.log 2 ≤ Real.log 2 by
        nlinarith [mul_pos hbpos log_two_pos])
    rwa [Real.exp_log (by norm_num : (0 : ℝ) < 2)] at hstep
  have hrecurrence :
      threeRetentionProbability (betaNN r) (dimension + 1) *
          ((2 ^ (dimension + 1) : ℕ) : ℝ) =
        Real.exp ((1 - ((betaNN r : ℝ≥0) : ℝ)) * Real.log 2) *
          (threeRetentionProbability (betaNN r) dimension *
            ((2 ^ dimension : ℕ) : ℝ)) := by
    rw [threeRetentionProbability_mul_wordCount_eq_exp,
      threeRetentionProbability_mul_wordCount_eq_exp, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hppos := threeRetentionProbability_pos (betaNN r) dimension
  unfold vertexCountC
  apply Nat.ceil_le.mpr
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    3 * threeRetentionProbability (betaNN r) (dimension + 1) *
        ((2 ^ (dimension + 1) : ℕ) : ℝ) =
      Real.exp ((1 - ((betaNN r : ℝ≥0) : ℝ)) * Real.log 2) *
        (3 * threeRetentionProbability (betaNN r) dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
        rw [show 3 * threeRetentionProbability (betaNN r) (dimension + 1) *
              ((2 ^ (dimension + 1) : ℕ) : ℝ) =
            3 * (threeRetentionProbability (betaNN r) (dimension + 1) *
              ((2 ^ (dimension + 1) : ℕ) : ℝ)) by ring, hrecurrence]
        ring
    _ ≤ 2 * (3 * threeRetentionProbability (betaNN r) dimension *
          ((2 ^ dimension : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ ≤ 2 * (⌈3 * threeRetentionProbability (betaNN r) dimension *
            ((2 ^ dimension : ℕ) : ℝ)⌉₊ : ℝ) := by
        gcongr
        exact Nat.le_ceil _

theorem exists_vertexCountC_bracket (r : ℕ) (hr : 2 ≤ r) (minimum n : ℕ)
    (hminimum : vertexCountC r minimum ≤ n) :
    ∃ dimension : ℕ, minimum ≤ dimension ∧
      vertexCountC r dimension ≤ n ∧ n < vertexCountC r (dimension + 1) := by
  have hlarge : ∀ᶠ dimension : ℕ in atTop, n < vertexCountC r dimension := by
    have hevent := Filter.tendsto_atTop.1 (vertexCountC_tendsto_atTop r hr) (n + 1)
    filter_upwards [hevent] with dimension hdimension
    omega
  obtain ⟨dimension, hdimension, hafter⟩ :=
    (hlarge.and (Filter.eventually_ge_atTop minimum)).exists
  have hexists : ∃ offset : ℕ, n < vertexCountC r (minimum + offset) := by
    refine ⟨dimension - minimum, ?_⟩
    rw [Nat.add_sub_of_le hafter]
    exact hdimension
  let offset : ℕ := Nat.find hexists
  have hnext : n < vertexCountC r (minimum + offset) := Nat.find_spec hexists
  have hoffset : 0 < offset := by
    by_contra hnot
    have hzero : offset = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hzero, Nat.add_zero] at hnext
    omega
  refine ⟨minimum + (offset - 1), by omega, ?_, ?_⟩
  · exact Nat.le_of_not_gt (Nat.find_min hexists (by omega))
  · rw [show minimum + (offset - 1) + 1 = minimum + offset by omega]
    exact hnext

/-! ### The counting hypothesis, generic in `r`

`L + (r+1)·log₂(C(L,r)+1) − δ·C(L,r) < −1`.  Two crude but uniform estimates
suffice: `C(L,r) ≤ 2^L` for the logarithm, and `C(L,r) ≥ L²/(4·r!)` for the
subtracted term (this is where `2 ≤ r` is used — a linear lower bound would not
beat the linear left-hand side). -/

theorem logTwo_choose_add_one_le (L r : ℕ) :
    logTwo ((L.choose r + 1 : ℕ) : ℝ) ≤ (L : ℝ) + 1 := by
  have hle : (L.choose r + 1 : ℕ) ≤ 2 ^ (L + 1) := by
    have h1 := Nat.choose_le_two_pow L r
    have h2 : (1 : ℕ) ≤ 2 ^ L := Nat.one_le_two_pow
    have h3 : 2 ^ (L + 1) = 2 ^ L + 2 ^ L := by rw [pow_succ]; ring
    omega
  have hpos : (0 : ℝ) < ((L.choose r + 1 : ℕ) : ℝ) := by positivity
  have hlog : Real.log ((L.choose r + 1 : ℕ) : ℝ) ≤ Real.log ((2 : ℝ) ^ (L + 1)) := by
    apply Real.log_le_log hpos
    exact_mod_cast hle
  rw [Real.log_pow] at hlog
  show Real.log ((L.choose r + 1 : ℕ) : ℝ) / Real.log 2 ≤ (L : ℝ) + 1
  rw [div_le_iff₀ log_two_pos]
  push_cast at hlog ⊢
  linarith

theorem choose_ge_sq_div (L r : ℕ) (hr : 2 ≤ r) (hL : 2 * r ≤ L) :
    (L : ℝ) ^ 2 / (4 * (Nat.factorial r : ℝ)) ≤ (L.choose r : ℝ) := by
  have hfac : (0 : ℝ) < (Nat.factorial r : ℝ) := by exact_mod_cast r.factorial_pos
  have hrL : r ≤ L := by omega
  have hLreal : (2 : ℝ) * (r : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hcast : ((L + 1 - r : ℕ) : ℝ) = (L : ℝ) + 1 - (r : ℝ) := by
    have h : (r : ℕ) ≤ L + 1 := by omega
    push_cast [Nat.cast_sub h]
    ring
  have hhalf : (1 : ℝ) ≤ (L : ℝ) / 2 := by linarith
  have hbase : (L : ℝ) / 2 ≤ ((L + 1 - r : ℕ) : ℝ) := by rw [hcast]; linarith
  have hpow2 : ((L : ℝ) / 2) ^ 2 ≤ ((L : ℝ) / 2) ^ r := pow_le_pow_right₀ hhalf hr
  have hpow : ((L : ℝ) / 2) ^ r ≤ ((L + 1 - r : ℕ) : ℝ) ^ r :=
    pow_le_pow_left₀ (by linarith) hbase r
  have hpc := Nat.pow_le_choose (α := ℝ) r L
  have hnum : (L : ℝ) ^ 2 / 4 ≤ ((L + 1 - r : ℕ) : ℝ) ^ r := by
    have : ((L : ℝ) / 2) ^ 2 = (L : ℝ) ^ 2 / 4 := by ring
    linarith [this ▸ hpow2, hpow]
  calc (L : ℝ) ^ 2 / (4 * (Nat.factorial r : ℝ)) = ((L : ℝ) ^ 2 / 4) / (Nat.factorial r : ℝ) := by
        rw [div_div]
    _ ≤ ((L + 1 - r : ℕ) : ℝ) ^ r / (Nat.factorial r : ℝ) := by gcongr
    _ ≤ (L.choose r : ℝ) := hpc

theorem exists_counting_base (r : ℕ) (hr : 2 ≤ r) (slack : ℝ) (hslack : 0 < slack) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L →
      (L : ℝ) + ((r : ℝ) + 1) * logTwo ((L.choose r + 1 : ℕ) : ℝ) -
        slack * (L.choose r : ℝ) < -1 := by
  classical
  set K : ℝ := 4 * (Nat.factorial r : ℝ) * (2 * (r : ℝ) + 4) / slack with hK
  refine ⟨max (2 * r) (⌈K⌉₊ + 1), fun L hL => ?_⟩
  have hfac : (0 : ℝ) < (Nat.factorial r : ℝ) := by exact_mod_cast r.factorial_pos
  have hL2r : 2 * r ≤ L := le_trans (le_max_left _ _) hL
  have hceil : ⌈K⌉₊ + 1 ≤ L := le_trans (le_max_right _ _) hL
  have hLK : K < (L : ℝ) := by
    have hlt : (⌈K⌉₊ : ℝ) < (L : ℝ) := by exact_mod_cast (by omega : ⌈K⌉₊ < L)
    exact lt_of_le_of_lt (Nat.le_ceil K) hlt
  have hr2 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hLreal : (4 : ℝ) ≤ (L : ℝ) := by
    have : (4 : ℕ) ≤ L := by omega
    exact_mod_cast this
  have hlog := logTwo_choose_add_one_le L r
  have hchoose := choose_ge_sq_div L r hr hL2r
  -- `slack · L > 4 · r! · (2r+4)`
  have hslackL : 4 * (Nat.factorial r : ℝ) * (2 * (r : ℝ) + 4) < slack * (L : ℝ) := by
    rw [hK, div_lt_iff₀ hslack] at hLK
    linarith
  have hLpos : (0 : ℝ) < (L : ℝ) := by linarith
  have hkey : (2 * (r : ℝ) + 4) * (L : ℝ) <
      slack * ((L : ℝ) ^ 2 / (4 * (Nat.factorial r : ℝ))) := by
    have hpos : (0 : ℝ) < 4 * (Nat.factorial r : ℝ) := by positivity
    have heq : slack * ((L : ℝ) ^ 2 / (4 * (Nat.factorial r : ℝ))) =
        (slack * (L : ℝ)) * (L : ℝ) / (4 * (Nat.factorial r : ℝ)) := by
      field_simp
    rw [heq, lt_div_iff₀ hpos]
    nlinarith [mul_lt_mul_of_pos_right hslackL hLpos]
  have hlow : slack * ((L : ℝ) ^ 2 / (4 * (Nat.factorial r : ℝ))) ≤ slack * (L.choose r : ℝ) :=
    mul_le_mul_of_nonneg_left hchoose hslack.le
  have hupper : (L : ℝ) + ((r : ℝ) + 1) * logTwo ((L.choose r + 1 : ℕ) : ℝ) + 1 ≤
      (2 * (r : ℝ) + 4) * (L : ℝ) := by
    have hbound : ((r : ℝ) + 1) * logTwo ((L.choose r + 1 : ℕ) : ℝ) ≤
        ((r : ℝ) + 1) * ((L : ℝ) + 1) := by
      apply mul_le_mul_of_nonneg_left hlog (by linarith)
    nlinarith [hbound, hLreal, hr2]
  linarith

/-- The without-replacement correction tends to `0` in the layer size. -/
theorem worCorrectionR_tendsto_zero (r : ℕ) (lam : ℝ) :
    Tendsto (fun L : ℕ => worCorrectionR r L lam) atTop (𝓝 0) := by
  have hinv : Tendsto (fun L : ℕ => (r : ℝ) ^ 2 / (L : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_one_div_atTop_nhds_zero_nat.const_mul ((r : ℝ) ^ 2)
    rw [mul_zero] at h
    exact Filter.Tendsto.congr (fun x => mul_one_div _ _) h
  have hent : Tendsto (fun L : ℕ => binaryEntropy ((r : ℝ) ^ 2 / (L : ℝ)))
      atTop (𝓝 0) := by
    have hcont : Tendsto binaryEntropy (𝓝 (0 : ℝ)) (𝓝 (binaryEntropy 0)) :=
      binaryEntropy_continuous.continuousAt.tendsto
    have hzero : binaryEntropy (0 : ℝ) = 0 := by unfold binaryEntropy; simp
    rw [hzero] at hcont
    exact hcont.comp hinv
  have hsum := (hinv.add (hinv.const_mul lam)).add (hent.div_const 2)
  simp only [mul_zero, zero_div, add_zero] at hsum
  exact hsum

theorem exists_worCorrection_base (r : ℕ) (lam slack : ℝ) (hslack : 0 < slack) :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → worCorrectionR r L lam < slack :=
  Filter.eventually_atTop.1
    ((tendsto_order.1 (worCorrectionR_tendsto_zero r lam)).2 slack hslack)

/-! ### The sampling budget holds eventually -/

theorem eventually_budget (r : ℕ) (hr : 2 ≤ r) (depth : ℕ) :
    ∀ᶠ dimension : ℕ in atTop,
      ((2 * depth : ℕ) : ℝ) * Real.exp (-(dimension : ℝ) * Real.log 2) +
        4 / threeExpectedRetainedVertexCount (betaNN r) dimension +
        (4 / threeExpectedRetainedEdgeCount (betaNN r) dimension (radiusC r dimension) +
          8 / (threeRetentionProbability (betaNN r) dimension *
            ((2 ^ dimension : ℕ) : ℝ))) < 1 := by
  have hbeta : ((betaNN r : ℝ≥0) : ℝ) < 1 := by
    rw [betaNN_coe r hr]; exact betaC_lt_one r hr
  have h1 : Tendsto (fun dimension : ℕ =>
      ((2 * depth : ℕ) : ℝ) * Real.exp (-(dimension : ℝ) * Real.log 2))
      atTop (𝓝 0) := pairLayerExclusionProbability_tendsto_zero depth
  have h2 : Tendsto (fun dimension : ℕ =>
      4 / threeExpectedRetainedVertexCount (betaNN r) dimension) atTop (𝓝 0) := by
    have h := (threeExpectedRetainedVertexCount_inv_tendsto_zero (betaNN r)
      hbeta).const_mul (4 : ℝ)
    rw [mul_zero] at h
    exact Filter.Tendsto.congr (fun x => mul_one_div 4 _) h
  have h3 : Tendsto (fun dimension : ℕ =>
      4 / threeExpectedRetainedEdgeCount (betaNN r) dimension
        (radiusC r dimension)) atTop (𝓝 0) := by
    have h := (expectedRetainedEdgeCount_inv_tendsto_zero r hr).const_mul (4 : ℝ)
    rw [mul_zero] at h
    exact Filter.Tendsto.congr (fun x => mul_one_div 4 _) h
  have h4 : Tendsto (fun dimension : ℕ =>
      8 / (threeRetentionProbability (betaNN r) dimension *
        ((2 ^ dimension : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h := (threeRetentionProbability_mul_wordCount_inv_tendsto_zero (betaNN r)
      hbeta).const_mul (8 : ℝ)
    rw [mul_zero] at h
    exact Filter.Tendsto.congr (fun x => mul_one_div 8 _) h
  have hsum := ((h1.add h2).add (h3.add h4))
  simpa using (tendsto_order.1 hsum).2 1 (by norm_num)

/-! ### No isolated vertices -/

theorem baseSize_le_rVertex_card (baseSize r depth : ℕ) :
    baseSize ≤ Fintype.card (RVertex baseSize r depth) := by
  calc baseSize = Fintype.card (RLayer baseSize r 0) := (rLayer_card_zero baseSize r).symm
    _ ≤ Fintype.card (RVertex baseSize r depth) :=
      Fintype.card_le_of_embedding (rLayerEmbedding baseSize r depth 0 (by omega))

theorem rGraphOverFin_forall_exists_adj (baseSize r depth : ℕ)
    (hr : 2 ≤ r) (hbase : r ≤ baseSize) (hdepth : 0 < depth) :
    ∀ vertex : Fin (Fintype.card (RVertex baseSize r depth)),
      ∃ neighbor, (rGraphOverFin baseSize r depth).Adj vertex neighbor := by
  have hcard : 2 ≤ Fintype.card (RVertex baseSize r depth) := by
    have := baseSize_le_rVertex_card baseSize r depth
    omega
  letI : Nontrivial (Fin (Fintype.card (RVertex baseSize r depth))) :=
    Fin.nontrivial_iff_two_le.mpr hcard
  intro vertex
  exact (rGraphOverFin_connected baseSize r depth hr hbase hdepth).preconnected
    |>.exists_adj_of_nontrivial vertex

/-! ### From a free dense host to the extremal number -/

open Classical in
theorem eventually_expectedRetainedEdge_le_extremalNumber
    {baseSize r depth : ℕ} (hr : 2 ≤ r) (hbase : r ≤ baseSize) (hdepth : 0 < depth)
    (hhosts : ∀ᶠ dimension : ℕ in atTop,
      ∃ retained : Set (Bool × HammingWord dimension),
        (rGraphOverFin baseSize r depth).Free
            (retainedHammingHost dimension (radiusC r dimension) retained) ∧
        threeRetainedVertexCount dimension retained <
          3 * threeRetentionProbability (betaNN r) dimension *
            ((2 ^ dimension : ℕ) : ℝ) ∧
        threeExpectedRetainedEdgeCount (betaNN r) dimension (radiusC r dimension) / 2 ≤
          hammingRetainedEdgeCount dimension (radiusC r dimension) retained) :
    ∀ᶠ dimension : ℕ in atTop,
      threeExpectedRetainedEdgeCount (betaNN r) dimension (radiusC r dimension) / 2 ≤
        (SimpleGraph.extremalNumber (vertexCountC r dimension)
          (rGraphOverFin baseSize r depth) : ℝ) := by
  filter_upwards [hhosts] with dimension hhost
  obtain ⟨retained, hfree, hvertices, hedges⟩ := hhost
  have hcard := retainedVertex_card_le_vertexCountC r dimension retained hvertices
  have hembedding : Nonempty (retained ↪ Fin (vertexCountC r dimension)) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa using hcard
  obtain ⟨embedding⟩ := hembedding
  let paddedHost : SimpleGraph (Fin (vertexCountC r dimension)) :=
    (retainedHammingHost dimension (radiusC r dimension) retained).map embedding
  have hpadded_free : (rGraphOverFin baseSize r depth).Free paddedHost :=
    CompactnessConjecture.free_map_of_no_isolated
      (rGraphOverFin baseSize r depth)
      (rGraphOverFin_forall_exists_adj baseSize r depth hr hbase hdepth)
      embedding hfree
  have hpadded_edges :
      paddedHost.edgeFinset.card ≤
        SimpleGraph.extremalNumber (vertexCountC r dimension)
          (rGraphOverFin baseSize r depth) := by
    simpa using (SimpleGraph.card_edgeFinset_le_extremalNumber hpadded_free)
  calc
    threeExpectedRetainedEdgeCount (betaNN r) dimension (radiusC r dimension) / 2 ≤
      hammingRetainedEdgeCount dimension (radiusC r dimension) retained := hedges
    _ = ((retainedHammingHost dimension (radiusC r dimension)
        retained).edgeFinset.card : ℝ) :=
      hammingRetainedEdgeCount_eq_edgeFinset_card dimension
        (radiusC r dimension) retained
    _ = (paddedHost.edgeFinset.card : ℝ) := by
      congr 1
      exact (SimpleGraph.card_edgeFinset_map embedding
        (retainedHammingHost dimension (radiusC r dimension) retained)).symm
    _ ≤ (SimpleGraph.extremalNumber (vertexCountC r dimension)
        (rGraphOverFin baseSize r depth) : ℝ) := by exact_mod_cast hpadded_edges

-- The final assembly, modulo the existence of a free dense retained host.
open Classical in
theorem rDegenerateExtremalCounterexample_of_hosts
    {baseSize r depth : ℕ} (hr : 2 ≤ r) (hbase1 : r + 1 ≤ baseSize) (hdepth : 0 < depth)
    (hhosts : ∀ᶠ dimension : ℕ in atTop,
      ∃ retained : Set (Bool × HammingWord dimension),
        (rGraphOverFin baseSize r depth).Free
            (retainedHammingHost dimension (radiusC r dimension) retained) ∧
        threeRetainedVertexCount dimension retained <
          3 * threeRetentionProbability (betaNN r) dimension *
            ((2 ^ dimension : ℕ) : ℝ) ∧
        threeExpectedRetainedEdgeCount (betaNN r) dimension (radiusC r dimension) / 2 ≤
          hammingRetainedEdgeCount dimension (radiusC r dimension) retained) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧ H.IsBipartite ∧ IsDegenerate r H ∧ ¬ IsDegenerate (r - 1) H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + epsC r) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  classical
  have hbase : r ≤ baseSize := by omega
  set forbidden := rGraphOverFin baseSize r depth with hforbidden
  have hnoisolated :
      ∀ vertex : Fin (Fintype.card (RVertex baseSize r depth)),
        ∃ neighbor, forbidden.Adj vertex neighbor :=
    rGraphOverFin_forall_exists_adj baseSize r depth hr hbase hdepth
  have hsubsequence :
      ∀ᶠ dimension : ℕ in atTop,
        (vertexCountC r dimension : ℝ) ^ powerC r ≤
          (SimpleGraph.extremalNumber (vertexCountC r dimension) forbidden : ℝ) := by
    filter_upwards [eventually_vertexCountC_power_le_expectedRetainedEdge r hr,
      eventually_expectedRetainedEdge_le_extremalNumber hr hbase hdepth hhosts]
      with dimension hpower hbound
    exact hpower.trans hbound
  refine ⟨Fintype.card (RVertex baseSize r depth), forbidden,
    rGraphOverFin_connected baseSize r depth hr hbase hdepth,
    rGraphOverFin_isBipartite baseSize r depth,
    rGraphOverFin_isDegenerate baseSize r depth,
    rGraphOverFin_not_isDegenerate baseSize r depth (by omega) hbase1 hdepth,
    1 / (2 : ℝ) ^ powerC r,
    one_div_pos.mpr (Real.rpow_pos_of_pos (by norm_num) (powerC r)), ?_⟩
  obtain ⟨minimum, hminimum⟩ := Filter.eventually_atTop.1 hsubsequence
  apply Filter.eventually_atTop.2
  refine ⟨vertexCountC r minimum, ?_⟩
  intro n hn
  obtain ⟨dimension, hdimension, hbelow, habove⟩ :=
    exists_vertexCountC_bracket r hr minimum n hn
  have hdouble := vertexCountC_succ_le_two_mul r hr dimension
  have hn_bound : n ≤ 2 * vertexCountC r dimension := by omega
  have hn_real : (n : ℝ) ≤ 2 * (vertexCountC r dimension : ℝ) := by exact_mod_cast hn_bound
  have hsubseq := hminimum dimension hdimension
  have hmonotone :
      SimpleGraph.extremalNumber (vertexCountC r dimension) forbidden ≤
        SimpleGraph.extremalNumber n forbidden :=
    CompactnessConjecture.extremalNumber_monotone_of_no_isolated
      forbidden hnoisolated hbelow
  have hpower_eq : (2 : ℝ) - 1 / (r : ℝ) + epsC r = powerC r := by
    unfold powerC; ring
  rw [hpower_eq]
  calc
    (1 / (2 : ℝ) ^ powerC r) * (n : ℝ) ^ powerC r ≤
      (1 / (2 : ℝ) ^ powerC r) * (2 * (vertexCountC r dimension : ℝ)) ^ powerC r := by
        apply mul_le_mul_of_nonneg_left
        · exact Real.rpow_le_rpow (Nat.cast_nonneg n) hn_real (powerC_pos r hr).le
        · positivity
    _ = (vertexCountC r dimension : ℝ) ^ powerC r := by
        rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg (vertexCountC r dimension))]
        have htwo : (2 : ℝ) ^ powerC r ≠ 0 :=
          (Real.rpow_pos_of_pos (by norm_num) (powerC r)).ne'
        field_simp
    _ ≤ (SimpleGraph.extremalNumber (vertexCountC r dimension) forbidden : ℝ) := hsubseq
    _ ≤ (SimpleGraph.extremalNumber n forbidden : ℝ) := by exact_mod_cast hmonotone

/-! ## The Gibbs variational bound

`TypeEntropyBound r A λ` with `A = sup G_r(λ)` is paper §3's Gibbs/Legendre
duality: the per-type conditional-entropy inequality whose optimal constant is
exactly the supremum of the Gibbs objective `G_r`.  At `r = 3` the same
statement with the hand-certified constant `A₀ = 17/80` (`λ = 7/4`) is
`ThreeDegenerateGraphs.conditional_entropy_bound` of `Entropy3.lean`; see
`erdos-degeneracy/tests/KernelRCheck3.lean`.

The generic proof below is `Entropy3`'s derivation with `r` and `λ` kept
symbolic and with **no numerics at all** — that is the whole point of stating
the ledger constant as `sup G_r` rather than as a certified numeral.  For each
type `j` one applies the Gibbs (log-sum) inequality
`TwoDegenerateGraphs.binary_log_sum_bound` with the two weights

* `w₀(j) = √(1-v) · 2^(-λ j / r)`,
* `w₁(j) = √v · 2^(-λ (r-j) / r)`,

whose logarithms split as `log √(1-v) - (λ j / r) log 2` and
`log √v - (λ (r-j) / r) log 2`.  Averaging the `r + 1` resulting inequalities
against the binomial type masses `P(j) = C(r,j) qʲ (1-q)^{r-j}` and using

* `∑ⱼ P(j) = 1` (binomial theorem),
* `∑ⱼ P(j) pⱼ = v` (the marginal hypothesis),
* `∑ⱼ P(j) (j(1-pⱼ) + (r-j)pⱼ) = r d` (the disagreement hypothesis),

collapses the two `√` terms to `h(v)/2` and the two exponent terms to
`λ (log 2) d`, leaving exactly `G_r(λ; q, v) · log 2 - h(q)/2` from the
log-sum right-hand sides.  Finally `G_r(λ; q, v) ≤ sup G_r(λ)` because
`(q, v) ∈ [0,1]²` and the image is bounded above (`Lemma61`'s
`bddAbove_image2_Gfun`). -/
theorem typeEntropyBound_supG_gen (r : ℕ) (hr : 1 ≤ r) (lam : ℝ) :
    TypeEntropyBound r (supG r lam) lam := by
  classical
  intro q v d p hq hq' hv0 hv1 hp0 hp1 hv hd
  have hrpos : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hrne : (r : ℝ) ≠ 0 := hrpos.ne'
  have hLpos : (0 : ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hLne : Real.log 2 ≠ 0 := hLpos.ne'
  have hq1 : (0 : ℝ) ≤ 1 - q := by linarith
  -- the two square roots
  have hz : (0 : ℝ) < Real.sqrt (1 - v) := Real.sqrt_pos.mpr (by linarith)
  have ho : (0 : ℝ) < Real.sqrt v := Real.sqrt_pos.mpr hv0
  have hlogz : Real.log (Real.sqrt (1 - v)) = Real.log (1 - v) / 2 :=
    Real.log_sqrt (by linarith)
  have hlogo : Real.log (Real.sqrt v) = Real.log v / 2 := Real.log_sqrt hv0.le
  have hbinv : Real.binEntropy v
      = -(v * Real.log v) - (1 - v) * Real.log (1 - v) := by
    unfold Real.binEntropy
    rw [Real.log_inv, Real.log_inv]; ring
  -- the binomial type masses
  have hw : ∀ j : ℕ, (0 : ℝ) ≤ (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) := by
    intro j
    exact mul_nonneg (mul_nonneg (by positivity) (pow_nonneg hq j)) (pow_nonneg hq1 _)
  have hwsum : ∑ j ∈ range (r + 1),
      ((r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j)) = 1 := by
    have h := add_pow q (1 - q) r
    rw [show q + (1 - q) = 1 by ring, one_pow] at h
    exact Eq.trans (Finset.sum_congr rfl fun j _ => by ring) h.symm
  -- the per-type Gibbs inequality
  have key : ∀ j ∈ range (r + 1),
      (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) * Real.binEntropy (p j)
        + ((r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) * (1 - p j)) *
            Real.log (Real.sqrt (1 - v))
        + ((r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) * p j) *
            Real.log (Real.sqrt v)
        - lam * Real.log 2 / (r : ℝ) *
            ((r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) *
              ((j : ℝ) * (1 - p j) + ((r - j : ℕ) : ℝ) * p j))
      ≤ (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) *
          Real.log (Real.sqrt (1 - v) * 2 ^ (-(lam * (j : ℝ)) / (r : ℝ)) +
            Real.sqrt v * 2 ^ (-(lam * ((r : ℝ) - (j : ℝ))) / (r : ℝ))) := by
    intro j hj
    have hjr : j ≤ r := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
    have hcast : ((r - j : ℕ) : ℝ) = (r : ℝ) - (j : ℝ) := by
      exact Nat.cast_sub hjr
    have e0 : (0 : ℝ) < (2 : ℝ) ^ (-(lam * (j : ℝ)) / (r : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have e1 : (0 : ℝ) < (2 : ℝ) ^ (-(lam * ((r : ℝ) - (j : ℝ))) / (r : ℝ)) :=
      Real.rpow_pos_of_pos (by norm_num) _
    have g := binary_log_sum_bound (p j)
      (Real.sqrt (1 - v) * 2 ^ (-(lam * (j : ℝ)) / (r : ℝ)))
      (Real.sqrt v * 2 ^ (-(lam * ((r : ℝ) - (j : ℝ))) / (r : ℝ)))
      (hp0 j) (hp1 j) (by positivity) (by positivity)
    rw [Real.log_mul hz.ne' e0.ne', Real.log_mul ho.ne' e1.ne',
      Real.log_rpow (by norm_num), Real.log_rpow (by norm_num)] at g
    have hmul := mul_le_mul_of_nonneg_left g (hw j)
    rw [hcast]
    refine le_trans (le_of_eq ?_) hmul
    field_simp
    ring
  have hsum := Finset.sum_le_sum key
  -- expand the averaged left-hand side
  have hexp : ∑ j ∈ range (r + 1),
      ((r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) * Real.binEntropy (p j)
        + ((r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) * (1 - p j)) *
            Real.log (Real.sqrt (1 - v))
        + ((r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) * p j) *
            Real.log (Real.sqrt v)
        - lam * Real.log 2 / (r : ℝ) *
            ((r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) *
              ((j : ℝ) * (1 - p j) + ((r - j : ℕ) : ℝ) * p j)))
      = (∑ j ∈ range (r + 1),
            (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) * Real.binEntropy (p j))
          + (1 - v) * Real.log (Real.sqrt (1 - v))
          + v * Real.log (Real.sqrt v)
          - lam * Real.log 2 / (r : ℝ) * ((r : ℝ) * d) := by
    rw [Finset.sum_sub_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.sum_mul, ← Finset.sum_mul, ← Finset.mul_sum, ← hd]
    congr 2
    · congr 1
      have hsplit : ∑ j ∈ range (r + 1),
          ((r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) * (1 - p j))
          = (∑ j ∈ range (r + 1),
              ((r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j)))
            - ∑ j ∈ range (r + 1),
              ((r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) * p j) := by
        rw [← Finset.sum_sub_distrib]
        exact Finset.sum_congr rfl fun j _ => by ring
      rw [hsplit, hwsum, ← hv]
    · rw [← hv]
  rw [hexp] at hsum
  -- the right-hand sides assemble into `G_r`
  have hGfun : Gfun r lam q v * Real.log 2
      = Real.binEntropy q / 2
        + ∑ j ∈ range (r + 1),
            (r.choose j : ℝ) * q ^ j * (1 - q) ^ (r - j) *
              Real.log (Real.sqrt (1 - v) * 2 ^ (-(lam * (j : ℝ)) / (r : ℝ)) +
                Real.sqrt v * 2 ^ (-(lam * ((r : ℝ) - (j : ℝ))) / (r : ℝ))) := by
    unfold Gfun binaryEntropy logTwo
    rw [add_mul, Finset.sum_mul]
    congr 1
    · field_simp
    · exact Finset.sum_congr rfl fun j _ => by field_simp
  have hsup : Gfun r lam q v ≤ supG r lam :=
    le_csSup (bddAbove_image2_Gfun r lam hr)
      (Set.mem_image2_of_mem ⟨hq, hq'⟩ ⟨hv0.le, hv1.le⟩)
  have hsupL : Gfun r lam q v * Real.log 2 ≤ supG r lam * Real.log 2 :=
    mul_le_mul_of_nonneg_right hsup hLpos.le
  have hd' : lam * Real.log 2 / (r : ℝ) * ((r : ℝ) * d) = lam * Real.log 2 * d := by
    field_simp
  rw [hlogz, hlogo, hd'] at hsum
  rw [hbinv]
  linarith [hsum, hGfun, hsupL]

theorem typeEntropyBound_supG (r : ℕ) (hr : 2 ≤ r) :
    TypeEntropyBound r (supG r (27 / 20)) (27 / 20) :=
  typeEntropyBound_supG_gen r (by omega) (27 / 20)

/-! ## Block F: the layered copy machinery -/

section Copy

variable {baseSize r depth dimension radius : ℕ}

theorem rGraphCopy_layer_side_eq
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (hr : 2 ≤ r) (hbase : r + 1 ≤ baseSize)
    (layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (first second : RLayer baseSize r layer) :
    (copy (rLayerEmbedding baseSize r depth layer (by omega) first)).val.1 =
    (copy (rLayerEmbedding baseSize r depth layer (by omega) second)).val.1 := by
  classical
  by_cases hequal : first = second
  · subst second; rfl
  · letI : DecidableEq (RLayer baseSize r layer) := Classical.decEq _
    have hcard : ({first, second} : Finset (RLayer baseSize r layer)).card ≤ r := by
      rw [Finset.card_pair hequal]; omega
    have huniv : r ≤ (Finset.univ : Finset (RLayer baseSize r layer)).card := by
      have hge := RGenericBridge.rLayer_card_ge_base (r := r) baseSize layer (by omega) hbase
      rw [Finset.card_univ]
      omega
    obtain ⟨c, hsub, -, hcr⟩ :=
      Finset.exists_subsuperset_card_eq (Finset.subset_univ
        ({first, second} : Finset (RLayer baseSize r layer))) hcard huniv
    have hfirst_mem : first ∈ c := hsub (Finset.mem_insert_self _ _)
    have hsecond_mem : second ∈ c :=
      hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    let bridge : RLayer baseSize r (layer + 1) := ⟨c, hcr⟩
    have hfirst_source := rGraph_parent_child_adj baseSize r depth layer
      hlayer bridge first hfirst_mem
    have hsecond_source := rGraph_parent_child_adj baseSize r depth layer
      hlayer bridge second hsecond_mem
    have hfirst_edge := copy.toHom.map_rel hfirst_source
    have hsecond_edge := copy.toHom.map_rel hsecond_source
    change (hammingHost dimension radius).Adj
      (copy (rLayerEmbedding baseSize r depth (layer + 1) hlayer bridge)).val
      (copy (rLayerEmbedding baseSize r depth layer (by omega) first)).val
      at hfirst_edge
    change (hammingHost dimension radius).Adj
      (copy (rLayerEmbedding baseSize r depth (layer + 1) hlayer bridge)).val
      (copy (rLayerEmbedding baseSize r depth layer (by omega) second)).val
      at hsecond_edge
    have hfirst_side := (hammingHost_adj_iff dimension radius _ _).mp hfirst_edge
    have hsecond_side := (hammingHost_adj_iff dimension radius _ _).mp hsecond_edge
    cases hbridge :
      (copy (rLayerEmbedding baseSize r depth (layer + 1) hlayer bridge)).val.1 <;>
      cases hf :
        (copy (rLayerEmbedding baseSize r depth layer (by omega) first)).val.1 <;>
      cases hs :
        (copy (rLayerEmbedding baseSize r depth layer (by omega) second)).val.1 <;>
      simp_all

theorem rGraphCopy_child_layer_side_eq
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (hr : 2 ≤ r) (hbase : r + 1 ≤ baseSize)
    (layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (first second : RLayer baseSize r (layer + 1)) :
    (copy (rLayerEmbedding baseSize r depth (layer + 1) hlayer first)).val.1 =
    (copy (rLayerEmbedding baseSize r depth (layer + 1) hlayer second)).val.1 := by
  classical
  have hfirst_nonempty : first.val.Nonempty := by
    apply Finset.card_pos.mp; rw [first.property]; omega
  have hsecond_nonempty : second.val.Nonempty := by
    apply Finset.card_pos.mp; rw [second.property]; omega
  obtain ⟨firstParent, hfirstParent⟩ := hfirst_nonempty
  obtain ⟨secondParent, hsecondParent⟩ := hsecond_nonempty
  have hparent_side := rGraphCopy_layer_side_eq retained copy hr hbase layer
    hlayer firstParent secondParent
  have hfirst_edge := copy.toHom.map_rel
    (rGraph_parent_child_adj baseSize r depth layer hlayer first
      firstParent hfirstParent)
  have hsecond_edge := copy.toHom.map_rel
    (rGraph_parent_child_adj baseSize r depth layer hlayer second
      secondParent hsecondParent)
  change (hammingHost dimension radius).Adj
    (copy (rLayerEmbedding baseSize r depth (layer + 1) hlayer first)).val
    (copy (rLayerEmbedding baseSize r depth layer (by omega) firstParent)).val
    at hfirst_edge
  change (hammingHost dimension radius).Adj
    (copy (rLayerEmbedding baseSize r depth (layer + 1) hlayer second)).val
    (copy (rLayerEmbedding baseSize r depth layer (by omega) secondParent)).val
    at hsecond_edge
  have hfirst_side := (hammingHost_adj_iff dimension radius _ _).mp hfirst_edge
  have hsecond_side := (hammingHost_adj_iff dimension radius _ _).mp hsecond_edge
  cases hf :
    (copy (rLayerEmbedding baseSize r depth (layer + 1) hlayer first)).val.1 <;>
    cases hs :
      (copy (rLayerEmbedding baseSize r depth (layer + 1) hlayer second)).val.1 <;>
    cases hfp :
      (copy (rLayerEmbedding baseSize r depth layer
        (by omega) firstParent)).val.1 <;>
    cases hsp :
      (copy (rLayerEmbedding baseSize r depth layer
        (by omega) secondParent)).val.1 <;>
    simp_all

noncomputable def rGraphCopyParentWords
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    Fin (Fintype.card (RLayer baseSize r layer.val)) → HammingWord dimension :=
  fun parent =>
    (copy (rLayerEmbedding baseSize r depth layer.val (by omega)
      ((rLayerFinEquiv baseSize r layer.val).symm parent))).val.2

noncomputable def rGraphCopyChildWords
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    RLayer (Fintype.card (RLayer baseSize r layer.val)) r 1 → HammingWord dimension :=
  fun sub =>
    (copy (rLayerEmbedding baseSize r depth (layer.val + 1) (by omega)
      ((rLayerSubEquiv baseSize r layer.val) sub))).val.2

noncomputable def rGraphCopyChildSide
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (reference : RLayer (Fintype.card (RLayer baseSize r layer.val)) r 1) : Bool :=
  (copy (rLayerEmbedding baseSize r depth (layer.val + 1) (by omega)
    ((rLayerSubEquiv baseSize r layer.val) reference))).val.1

noncomputable def rGraphCopyLayerPotential
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin (depth + 1)) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      (((booleanWordOnes
        (fun vertex : RLayer baseSize r layer.val =>
          (copy (rLayerEmbedding baseSize r depth layer.val layer.isLt
            vertex)).val.2 coordinate)).card : ℝ) /
        (Fintype.card (RLayer baseSize r layer.val) : ℝ))) /
    (dimension : ℝ)

theorem rGraphCopy_parentPotential_eq
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    RGenericBridge.rParentArrayEntropyPotential
        (rGraphCopyParentWords retained copy layer) =
      rGraphCopyLayerPotential retained copy ⟨layer.val, by omega⟩ := by
  unfold RGenericBridge.rParentArrayEntropyPotential rGraphCopyLayerPotential
  apply congrArg (fun numerator : ℝ => numerator / (dimension : ℝ))
  apply Finset.sum_congr rfl
  intro coordinate _
  unfold pairParentCoordinateOneCount rGraphCopyParentWords
  rw [booleanWordOnes_card_equiv
    (rLayerFinEquiv baseSize r layer.val).symm
    (fun vertex : RLayer baseSize r layer.val =>
      (copy (rLayerEmbedding baseSize r depth layer.val (by omega)
        vertex)).val.2 coordinate)]

theorem rGraphCopy_childPotential_eq
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    RGenericBridge.rChildArrayEntropyPotential r
        (rGraphCopyChildWords retained copy layer) =
      rGraphCopyLayerPotential retained copy ⟨layer.val + 1, by omega⟩ := by
  unfold RGenericBridge.rChildArrayEntropyPotential rGraphCopyLayerPotential
  apply congrArg (fun numerator : ℝ => numerator / (dimension : ℝ))
  apply Finset.sum_congr rfl
  intro coordinate _
  unfold RGenericBridge.rChildCoordinateOneCount rGraphCopyChildWords
  rw [booleanWordOnes_card_equiv
    (rLayerSubEquiv baseSize r layer.val)
    (fun vertex : RLayer baseSize r (layer.val + 1) =>
      (copy (rLayerEmbedding baseSize r depth (layer.val + 1) (by omega)
        vertex)).val.2 coordinate)]
  rw [rLayer_card_succ]

theorem rGraphCopyLayerPotential_mem_Icc
    (hr : 2 ≤ r) (hbase : r + 1 ≤ baseSize) (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin (depth + 1)) :
    0 ≤ rGraphCopyLayerPotential retained copy layer ∧
      rGraphCopyLayerPotential retained copy layer ≤ 1 := by
  classical
  have hlayer : 0 < Fintype.card (RLayer baseSize r layer.val) := by
    have hcard := RGenericBridge.rLayer_card_ge_base (r := r) baseSize layer.val (by omega) hbase
    omega
  have hlayer_real : (0 : ℝ) < (Fintype.card (RLayer baseSize r layer.val) : ℝ) := by
    exact_mod_cast hlayer
  have hdimension_real : (0 : ℝ) < (dimension : ℝ) := by exact_mod_cast hdimension
  have hterm (coordinate : Fin dimension) :
      0 ≤ binaryEntropy
          (((booleanWordOnes
            (fun vertex : RLayer baseSize r layer.val =>
              (copy (rLayerEmbedding baseSize r depth layer.val layer.isLt
                vertex)).val.2 coordinate)).card : ℝ) /
            (Fintype.card (RLayer baseSize r layer.val) : ℝ)) ∧
      binaryEntropy
          (((booleanWordOnes
            (fun vertex : RLayer baseSize r layer.val =>
              (copy (rLayerEmbedding baseSize r depth layer.val layer.isLt
                vertex)).val.2 coordinate)).card : ℝ) /
            (Fintype.card (RLayer baseSize r layer.val) : ℝ)) ≤ 1 := by
    have hcount :
        (booleanWordOnes
          (fun vertex : RLayer baseSize r layer.val =>
            (copy (rLayerEmbedding baseSize r depth layer.val layer.isLt
              vertex)).val.2 coordinate)).card ≤
          Fintype.card (RLayer baseSize r layer.val) := by
      unfold booleanWordOnes
      simpa using
        (Finset.card_filter_le
          (Finset.univ : Finset (RLayer baseSize r layer.val))
          (fun vertex =>
            (copy (rLayerEmbedding baseSize r depth layer.val layer.isLt
              vertex)).val.2 coordinate = true))
    have hzero : 0 ≤
        ((booleanWordOnes
          (fun vertex : RLayer baseSize r layer.val =>
            (copy (rLayerEmbedding baseSize r depth layer.val layer.isLt
              vertex)).val.2 coordinate)).card : ℝ) /
          (Fintype.card (RLayer baseSize r layer.val) : ℝ) := by positivity
    have hone :
        ((booleanWordOnes
          (fun vertex : RLayer baseSize r layer.val =>
            (copy (rLayerEmbedding baseSize r depth layer.val layer.isLt
              vertex)).val.2 coordinate)).card : ℝ) /
          (Fintype.card (RLayer baseSize r layer.val) : ℝ) ≤ 1 := by
      apply (div_le_one hlayer_real).mpr
      exact_mod_cast hcount
    exact ⟨binaryEntropy_nonneg hzero hone, binaryEntropy_le_one _⟩
  unfold rGraphCopyLayerPotential
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun coordinate _ => (hterm coordinate).1)
      hdimension_real.le
  · apply (div_le_one hdimension_real).mpr
    calc (∑ coordinate : Fin dimension,
        binaryEntropy
          (((booleanWordOnes
            (fun vertex : RLayer baseSize r layer.val =>
              (copy (rLayerEmbedding baseSize r depth layer.val layer.isLt
                vertex)).val.2 coordinate)).card : ℝ) /
            (Fintype.card (RLayer baseSize r layer.val) : ℝ))) ≤
        ∑ _coordinate : Fin dimension, (1 : ℝ) :=
          Finset.sum_le_sum fun coordinate _ => (hterm coordinate).2
      _ = (dimension : ℝ) := by simp

theorem rGraphCopyChildWords_injective
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (hr : 2 ≤ r) (hbase : r + 1 ≤ baseSize)
    (layer : Fin depth) :
    Function.Injective (rGraphCopyChildWords retained copy layer) := by
  intro first second hwords
  have hside := rGraphCopy_child_layer_side_eq retained copy hr hbase
    layer.val (by omega)
    ((rLayerSubEquiv baseSize r layer.val) first)
    ((rLayerSubEquiv baseSize r layer.val) second)
  have hvertices :
      (copy (rLayerEmbedding baseSize r depth (layer.val + 1) (by omega)
        ((rLayerSubEquiv baseSize r layer.val) first))).val =
      (copy (rLayerEmbedding baseSize r depth (layer.val + 1) (by omega)
        ((rLayerSubEquiv baseSize r layer.val) second))).val :=
    Prod.ext hside hwords
  have himages :
      copy (rLayerEmbedding baseSize r depth (layer.val + 1) (by omega)
        ((rLayerSubEquiv baseSize r layer.val) first)) =
      copy (rLayerEmbedding baseSize r depth (layer.val + 1) (by omega)
        ((rLayerSubEquiv baseSize r layer.val) second)) :=
    Subtype.ext hvertices
  have hsources := copy.injective himages
  have hsubs :=
    (rLayerEmbedding baseSize r depth (layer.val + 1) (by omega)).injective hsources
  exact (rLayerSubEquiv baseSize r layer.val).injective hsubs

theorem rGraphCopyChildWords_retained
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (hr : 2 ≤ r) (hbase : r + 1 ≤ baseSize)
    (layer : Fin depth)
    (reference : RLayer (Fintype.card (RLayer baseSize r layer.val)) r 1) :
    retained ∈
      RGenericSampling.rChildRetentionEvent
        (rGraphCopyChildSide retained copy layer reference)
        (rGraphCopyChildWords retained copy layer) := by
  intro sub
  have hside := rGraphCopy_child_layer_side_eq retained copy hr hbase
    layer.val (by omega)
    ((rLayerSubEquiv baseSize r layer.val) reference)
    ((rLayerSubEquiv baseSize r layer.val) sub)
  have hretained :=
    (copy (rLayerEmbedding baseSize r depth (layer.val + 1) (by omega)
      ((rLayerSubEquiv baseSize r layer.val) sub))).property
  change
    (rGraphCopyChildSide retained copy layer reference,
      rGraphCopyChildWords retained copy layer sub) ∈ retained
  unfold rGraphCopyChildSide rGraphCopyChildWords
  rw [hside]
  exact hretained

theorem rGraphCopy_parent_child_hammingDist_le
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (sub : RLayer (Fintype.card (RLayer baseSize r layer.val)) r 1)
    (parent : RLayer (Fintype.card (RLayer baseSize r layer.val)) r 0)
    (hparent : parent ∈ sub.val) :
    hammingDist
      (rGraphCopyParentWords retained copy layer parent)
      (rGraphCopyChildWords retained copy layer sub) ≤ radius := by
  have hactualParent :
      (rLayerFinEquiv baseSize r layer.val).symm parent ∈
        ((rLayerSubEquiv baseSize r layer.val) sub).val := by
    change (rLayerFinEquiv baseSize r layer.val).symm parent ∈
      sub.val.map (rLayerFinEquiv baseSize r layer.val).symm.toEmbedding
    exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
  have hsource := rGraph_parent_child_adj baseSize r depth layer.val
    (by omega) ((rLayerSubEquiv baseSize r layer.val) sub)
    ((rLayerFinEquiv baseSize r layer.val).symm parent) hactualParent
  have hedge := copy.toHom.map_rel hsource
  change (hammingHost dimension radius).Adj
    (copy (rLayerEmbedding baseSize r depth (layer.val + 1) (by omega)
      ((rLayerSubEquiv baseSize r layer.val) sub))).val
    (copy (rLayerEmbedding baseSize r depth layer.val (by omega)
      ((rLayerFinEquiv baseSize r layer.val).symm parent))).val at hedge
  have hdist := ((hammingHost_adj_iff dimension radius _ _).mp hedge).2
  simpa [rGraphCopyParentWords, rGraphCopyChildWords, hammingDist_comm] using hdist

theorem rGraphCopy_averageDisagreement_le_tau
    (hr : 2 ≤ r) (hbase : r + 1 ≤ baseSize) (hdimension : 0 < dimension)
    (hradius : (radius : ℝ) ≤ tauOf r (27 / 20) * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    RGenericBridge.rChildArrayAverageDisagreement r
      (rGraphCopyParentWords retained copy layer)
      (rGraphCopyChildWords retained copy layer) ≤ tauOf r (27 / 20) := by
  have hdimension_real : (0 : ℝ) < (dimension : ℝ) := by exact_mod_cast hdimension
  have hparents : r ≤ Fintype.card (RLayer baseSize r layer.val) := by
    have := RGenericBridge.rLayer_card_ge_base (r := r) baseSize layer.val (by omega) hbase
    omega
  refine le_trans
    (RGenericBridge.rChildArrayAverageDisagreement_le_radius (by omega) hparents
      hdimension _ _ radius
      (fun sub parent hparent =>
        rGraphCopy_parent_child_hammingDist_le retained copy layer
          sub parent hparent))
    ((div_le_iff₀ hdimension_real).mpr hradius)

theorem rGraphCopy_entropy_lower_of_exclusion
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (hr : 2 ≤ r) (hbase : r + 1 ≤ baseSize)
    (layer : Fin depth)
    (reference : RLayer (Fintype.card (RLayer baseSize r layer.val)) r 1)
    (threshold : ℝ)
    (hexclusion :
      retained ∉
        RGenericSampling.badRLayerRetentionEvent
          (Fintype.card (RLayer baseSize r layer.val)) dimension r
          (rGraphCopyChildSide retained copy layer reference)
          threshold) :
    threshold <
      rChildArrayEntropy
        (rGraphCopyParentWords retained copy layer)
        (rGraphCopyChildWords retained copy layer) := by
  classical
  by_contra hnot
  have hbad_entropy :
      rChildArrayEntropy
        (rGraphCopyParentWords retained copy layer)
        (rGraphCopyChildWords retained copy layer) ≤ threshold := le_of_not_gt hnot
  have hbad_array :
      rGraphCopyChildWords retained copy layer ∈
        badRChildArrays r (rGraphCopyParentWords retained copy layer) threshold := by
    unfold badRChildArrays
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad_entropy⟩
  have hinjective :
      rGraphCopyChildWords retained copy layer ∈
        (badRChildArrays r
          (rGraphCopyParentWords retained copy layer) threshold).filter
            Function.Injective :=
    Finset.mem_filter.mpr
      ⟨hbad_array, rGraphCopyChildWords_injective retained copy hr hbase layer⟩
  apply hexclusion
  change retained ∈
    ⋃ parents :
        Fin (Fintype.card (RLayer baseSize r layer.val)) → HammingWord dimension,
      RGenericSampling.badRChildRetentionEvent r parents
        (rGraphCopyChildSide retained copy layer reference) threshold
  apply Set.mem_iUnion.mpr
  refine ⟨rGraphCopyParentWords retained copy layer, ?_⟩
  change retained ∈
    ⋃ children ∈
        (badRChildArrays r
          (rGraphCopyParentWords retained copy layer) threshold).filter
            Function.Injective,
      RGenericSampling.rChildRetentionEvent
        (rGraphCopyChildSide retained copy layer reference) children
  exact Set.mem_iUnion.mpr
    ⟨rGraphCopyChildWords retained copy layer,
      Set.mem_iUnion.mpr
        ⟨hinjective,
          rGraphCopyChildWords_retained retained copy hr hbase layer reference⟩⟩

theorem rGraphCopy_layer_entropy_upper
    (hr : 2 ≤ r) (hGibbs : TypeEntropyBound r (supG r (27 / 20)) (27 / 20)) (hbase : 2 * r ^ 2 ≤ baseSize) (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (rParentSystem baseSize r depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (hdis : RGenericBridge.rChildArrayAverageDisagreement r
        (rGraphCopyParentWords retained copy layer)
        (rGraphCopyChildWords retained copy layer) ≤ tauOf r (27 / 20)) :
    rChildArrayEntropy
        (rGraphCopyParentWords retained copy layer)
        (rGraphCopyChildWords retained copy layer) ≤
      endpointC r +
        (rGraphCopyLayerPotential retained copy ⟨layer.val + 1, by omega⟩ -
          rGraphCopyLayerPotential retained copy ⟨layer.val, by omega⟩) / 2 +
        worCorrectionR r (Fintype.card (RLayer baseSize r layer.val)) (27 / 20) := by
  have hr1 : (2 : ℕ) ≤ r := hr
  have hb2 : r + 1 ≤ 2 * r ^ 2 := by nlinarith
  have hbase' : r + 1 ≤ baseSize := le_trans hb2 hbase
  have hcard : 2 * r ^ 2 ≤ Fintype.card (RLayer baseSize r layer.val) := by
    have hge := RGenericBridge.rLayer_card_ge_base (r := r) baseSize layer.val (by omega) hbase'
    omega
  have hbound := RGenericBridge.rChildArrayEntropy_empirical_bound
    (A := supG r (27 / 20)) (lam := (27 / 20 : ℝ))
    (by omega) (by norm_num) hGibbs hcard hdimension
    (rGraphCopyParentWords retained copy layer)
    (rGraphCopyChildWords retained copy layer)
  rw [rGraphCopy_childPotential_eq retained copy layer,
    rGraphCopy_parentPotential_eq retained copy layer] at hbound
  have hend : endpointC r = supG r (27 / 20) + (27 / 20 : ℝ) * tauOf r (27 / 20) := by
    unfold endpointC Aside; ring
  rw [hend]
  nlinarith [hbound, hdis]

theorem rGraph_free_of_layer_exclusion
    (hr : 2 ≤ r) (hGibbs : TypeEntropyBound r (supG r (27 / 20)) (27 / 20)) (hbase : 2 * r ^ 2 ≤ baseSize) (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) *
      RGenericBridge.potentialIncrement (betaC r) (slackC r) (endpointC r))
    (hradius : (radius : ℝ) ≤ tauOf r (27 / 20) * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion : ∀ (side : Bool) (layer : Fin depth),
      retained ∉ RGenericSampling.badRLayerRetentionEvent
        (Fintype.card (RLayer baseSize r layer.val)) dimension r side
        (betaC r - slackC r))
    (herror : ∀ layer : Fin depth,
      worCorrectionR r (Fintype.card (RLayer baseSize r layer.val)) (27 / 20) <
        slackC r) :
    (rParentSystem baseSize r depth).graph.Free
      (retainedHammingHost dimension radius retained) := by
  classical
  have hr1 : (2 : ℕ) ≤ r := hr
  have hb2 : r + 1 ≤ 2 * r ^ 2 := by nlinarith
  have hbase' : r + 1 ≤ baseSize := le_trans hb2 hbase
  intro hcontained
  obtain ⟨copy⟩ := hcontained
  set potential : ℕ → ℝ := fun level =>
    if hlevel : level < depth + 1 then
      rGraphCopyLayerPotential retained copy ⟨level, hlevel⟩ else 0
    with hpotential
  apply RGenericBridge.potential_layers_impossible depth potential
    (RGenericBridge.potentialIncrement (betaC r) (slackC r) (endpointC r))
  · intro level hlevel
    have hinrange : level < depth + 1 := by omega
    simpa [hpotential, hinrange, show level ≤ depth from by omega] using
      rGraphCopyLayerPotential_mem_Icc hr1 hbase' hdimension retained copy
        ⟨level, hinrange⟩
  · intro level hlevel
    have hnext : level + 1 < depth + 1 := by omega
    have hcurrent : level < depth + 1 := by omega
    have hsize : r ≤ Fintype.card (RLayer baseSize r level) := by
      have hge := RGenericBridge.rLayer_card_ge_base (r := r) baseSize level (by omega) hbase'
      omega
    let reference : RLayer (Fintype.card (RLayer baseSize r level)) r 1 :=
      Classical.choice (rLayerSub_nonempty hsize)
    have hlower := rGraphCopy_entropy_lower_of_exclusion retained copy
      hr1 hbase' ⟨level, hlevel⟩ reference (betaC r - slackC r)
      (hexclusion
        (rGraphCopyChildSide retained copy ⟨level, hlevel⟩ reference)
        ⟨level, hlevel⟩)
    have hupper := rGraphCopy_layer_entropy_upper hr hGibbs hbase hdimension retained
      copy ⟨level, hlevel⟩
      (rGraphCopy_averageDisagreement_le_tau hr1 hbase' hdimension hradius
        retained copy ⟨level, hlevel⟩)
    have hincrement := RGenericBridge.potential_increment
      (betaC r) (slackC r) (endpointC r)
      (rGraphCopyLayerPotential retained copy ⟨level, hcurrent⟩)
      (rGraphCopyLayerPotential retained copy ⟨level + 1, hnext⟩)
      (rChildArrayEntropy
        (rGraphCopyParentWords retained copy ⟨level, hlevel⟩)
        (rGraphCopyChildWords retained copy ⟨level, hlevel⟩))
      (worCorrectionR r (Fintype.card (RLayer baseSize r level)) (27 / 20))
      (herror ⟨level, hlevel⟩) hlower hupper
    simpa [hpotential, hnext, hcurrent, hlevel,
      show level ≤ depth from by omega] using hincrement
  · exact hdepth

end Copy

/-- **The exclusion step.**  A retained host that avoids every bad
layer-retention event contains no copy of the layered `r`-graph. -/
theorem rGraphOverFin_free_of_exclusion
    {baseSize r depth dimension : ℕ}
    (hr : 2 ≤ r) (hGibbs : TypeEntropyBound r (supG r (27 / 20)) (27 / 20)) (hbase : 2 * r ^ 2 ≤ baseSize) (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) *
      RGenericBridge.potentialIncrement (betaC r) (slackC r) (endpointC r))
    (herror : ∀ layer : Fin depth,
      worCorrectionR r (Fintype.card (RLayer baseSize r layer.val)) (27 / 20) <
        slackC r)
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion : retained ∉
      RGenericSampling.badRLayersRetentionEvent (betaNN r) (slackC r) r
        (fun layer : Fin depth => Fintype.card (RLayer baseSize r layer.val))
        dimension) :
    (rGraphOverFin baseSize r depth).Free
      (retainedHammingHost dimension (radiusC r dimension) retained) := by
  refine (SimpleGraph.free_congr_left (rGraphOverFinIso baseSize r depth)).mp ?_
  refine rGraph_free_of_layer_exclusion hr hGibbs hbase hdimension hdepth
    (RGenericSampling.rHammingRadius_le _ (tauC_nonneg r hr) dimension) retained ?_ herror
  intro side layer hmem
  refine hexclusion (Set.mem_iUnion.mpr ⟨side, Set.mem_iUnion.mpr ⟨layer, ?_⟩⟩)
  rwa [betaNN_coe r hr]

/-! ### The window lower bound and the explicit exponent

`Theorem3a.lowerSeq_le_rsq_width` (Lemma C, discharged by `LemmaB`) gives
`r² · width_r ≥ W(λ)(1 − (1+a²/3)/r) − a⁶/(1920 ln2 (1−a²/4)) · r⁻³`.
At `λ = 27/20` the right-hand side is increasing in `r`, so its value at
`r = 2`, namely `0.0060386…`, is a uniform lower bound. -/

theorem log_two_sq_bounds :
    (0.480453013 : ℝ) ≤ Real.log 2 ^ 2 ∧ Real.log 2 ^ 2 ≤ 0.480453015 := by
  have h1 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hlow : (0.6931471803 : ℝ) * 0.6931471803 ≤ Real.log 2 * Real.log 2 :=
    mul_le_mul h1.le h1.le (by norm_num) (by linarith)
  have hup : Real.log 2 * Real.log 2 ≤ (0.6931471808 : ℝ) * 0.6931471808 :=
    mul_le_mul h2.le h2.le (by linarith) (by norm_num)
  constructor <;> nlinarith [hlow, hup]

theorem log_two_cube_bounds :
    (0.333024651 : ℝ) ≤ Real.log 2 ^ 3 ∧ Real.log 2 ^ 3 ≤ 0.333024653 := by
  have h1 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  obtain ⟨hs1, hs2⟩ := log_two_sq_bounds
  have hlow : (0.480453013 : ℝ) * 0.6931471803 ≤ Real.log 2 ^ 2 * Real.log 2 :=
    mul_le_mul hs1 h1.le (by norm_num) (by nlinarith [hs1])
  have hup : Real.log 2 ^ 2 * Real.log 2 ≤ (0.480453015 : ℝ) * 0.6931471808 :=
    mul_le_mul hs2 h2.le (by linarith) (by norm_num)
  have he : Real.log 2 ^ 3 = Real.log 2 ^ 2 * Real.log 2 := by ring
  constructor <;> rw [he] <;> nlinarith [hlow, hup]

theorem lowerSeq_ge (r : ℕ) (hr : 2 ≤ r) : (0.00603 : ℝ) ≤ lowerSeq (27 / 20) r := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hrpos : (0 : ℝ) < (r : ℝ) := by linarith
  have h1 : (0.6931471803 : ℝ) < Real.log 2 := Real.log_two_gt_d9
  have h2 : Real.log 2 < 0.6931471808 := Real.log_two_lt_d9
  have hL : (0 : ℝ) < Real.log 2 := by linarith
  obtain ⟨hs1, hs2⟩ := log_two_sq_bounds
  obtain ⟨hc1, hc2⟩ := log_two_cube_bounds
  set t : ℝ := 1 / (r : ℝ) with ht
  have ht0 : 0 < t := by rw [ht]; positivity
  have ht2 : t ≤ 1 / 2 := by
    rw [ht, div_le_div_iff₀ hrpos (by norm_num)]; linarith
  have hW : Wconst (27 / 20 : ℝ) = (531441 / 160000 : ℝ) * Real.log 2 ^ 3 / 64 := by
    rw [Wconst]; norm_num
  have hWlow : (0.0172834 : ℝ) ≤ Wconst (27 / 20 : ℝ) := by rw [hW]; linarith [hc1]
  have hWpos : (0 : ℝ) < Wconst (27 / 20 : ℝ) := by linarith
  have hcform : 1 + ((27 / 20 : ℝ) * Real.log 2) ^ 2 / 3
      = 1 + (243 / 400 : ℝ) * Real.log 2 ^ 2 := by ring
  have hcup : 1 + ((27 / 20 : ℝ) * Real.log 2) ^ 2 / 3 ≤ 1.291875208 := by
    rw [hcform]; linarith [hs2]
  have hcpos : (0 : ℝ) < 1 + ((27 / 20 : ℝ) * Real.log 2) ^ 2 / 3 := by positivity
  have hfac : (0.354062396 : ℝ) ≤
      1 - (1 + ((27 / 20 : ℝ) * Real.log 2) ^ 2 / 3) * t := by
    have hmul := mul_le_mul_of_nonneg_left ht2 hcpos.le
    linarith [hcup, hmul]
  have hlead : (0.0061192 : ℝ) ≤
      Wconst (27 / 20 : ℝ) * (1 - (1 + ((27 / 20 : ℝ) * Real.log 2) ^ 2 / 3) * t) := by
    have hprod := mul_le_mul hWlow hfac (by norm_num) hWpos.le
    linarith [hprod]
  have hden : (0 : ℝ) < 1 - ((27 / 20 : ℝ) * Real.log 2) ^ 2 / 4 := by
    have he : ((27 / 20 : ℝ) * Real.log 2) ^ 2 = (729 / 400 : ℝ) * Real.log 2 ^ 2 := by
      ring
    rw [he]; linarith [hs2]
  have hsix : Real.log 2 ^ 6 ≤ 0.1109055 := by
    have h6 : Real.log 2 ^ 6 = (Real.log 2 ^ 3) ^ 2 := by ring
    rw [h6]; nlinarith [hc1, hc2]
  have hK : ((27 / 20 : ℝ) * Real.log 2) ^ 6 /
      (1920 * Real.log 2 * (1 - ((27 / 20 : ℝ) * Real.log 2) ^ 2 / 4)) ≤ 0.000648 := by
    rw [div_le_iff₀ (by positivity)]
    have hnum : ((27 / 20 : ℝ) * Real.log 2) ^ 6
        = (387420489 / 64000000 : ℝ) * Real.log 2 ^ 6 := by ring
    have hrhs : (0.000648 : ℝ) *
          (1920 * Real.log 2 * (1 - ((27 / 20 : ℝ) * Real.log 2) ^ 2 / 4))
        = 1.24416 * Real.log 2 - (1.24416 * 729 / 1600) * Real.log 2 ^ 3 := by ring
    rw [hnum, hrhs]
    linarith [hsix, hc2, h1]
  have hKpos : (0 : ℝ) ≤ ((27 / 20 : ℝ) * Real.log 2) ^ 6 /
      (1920 * Real.log 2 * (1 - ((27 / 20 : ℝ) * Real.log 2) ^ 2 / 4)) := by positivity
  have ht3 : t ^ 3 ≤ 1 / 8 := by
    have h := pow_le_pow_left₀ ht0.le ht2 3
    norm_num at h
    linarith
  have htail : ((27 / 20 : ℝ) * Real.log 2) ^ 6 /
      (1920 * Real.log 2 * (1 - ((27 / 20 : ℝ) * Real.log 2) ^ 2 / 4)) * t ^ 3
        ≤ 0.000081 := by
    nlinarith [hK, hKpos, ht3, pow_nonneg ht0.le 3]
  rw [lowerSeq]
  linarith [hlead, htail]

theorem width_ge (r : ℕ) (hr : 2 ≤ r) :
    (0.00603 : ℝ) / (r : ℝ) ^ 2 ≤ width r (27 / 20) := by
  have hr0 : (2 : ℝ) ≤ (r : ℝ) := by exact_mod_cast hr
  have hB : ∀ r' : ℕ, 2 ≤ r' → supG r' (27 / 20) = Gfun r' (27 / 20) (1 / 2) (1 / 2) :=
    fun r' hr' => LemmaB.supG_eq_center r' (27 / 20) hr' (by norm_num) (by norm_num)
  have hmain := lowerSeq_le_rsq_width (27 / 20) (by norm_num) lam_log_lt hr (hB r hr)
  have hlow := lowerSeq_ge r hr
  rw [div_le_iff₀ (by positivity)]
  nlinarith [hmain, hlow]

/-- **The explicit exponent**, unconditional: `ε_r ≥ 1/(48 r²)` — the
optimized `(θ, η) = (¼, ¼)` ledger of `lib/LedgerSharp.lean`, beating the
midpoint chain (`1/(110 r²)` with the frozen `K₁`, `1/(108 r²)` sharp). -/
theorem epsC_lower (r : ℕ) (hr : 2 ≤ r) : 1 / (48 * (r : ℝ) ^ 2) ≤ epsC r :=
  DegeneracyLedgerSharp.eps_quarter_48 r hr (betaC_lt_one r hr) (width_ge r hr)


/-! ## Block G: the counterexample -/

theorem exists_free_dense_hosts (r : ℕ) (hr : 2 ≤ r)
    (hGibbs : TypeEntropyBound r (supG r (27 / 20)) (27 / 20)) :
    ∃ baseSize depth : ℕ, 2 * r ^ 2 ≤ baseSize ∧ 0 < depth ∧
      ∀ᶠ dimension : ℕ in atTop,
        ∃ retained : Set (Bool × HammingWord dimension),
          (rGraphOverFin baseSize r depth).Free
              (retainedHammingHost dimension (radiusC r dimension) retained) ∧
          threeRetainedVertexCount dimension retained <
            3 * threeRetentionProbability (betaNN r) dimension *
              ((2 ^ dimension : ℕ) : ℝ) ∧
          threeExpectedRetainedEdgeCount (betaNN r) dimension (radiusC r dimension) / 2 ≤
            hammingRetainedEdgeCount dimension (radiusC r dimension) retained := by
  classical
  obtain ⟨Lerr, hLerr⟩ :=
    exists_worCorrection_base r (27 / 20) (slackC r) (slackC_pos r hr)
  obtain ⟨Lcnt, hLcnt⟩ := exists_counting_base r hr (slackC r) (slackC_pos r hr)
  refine ⟨max (2 * r ^ 2) (max Lerr Lcnt), depthC r, le_max_left _ _,
    depthC_pos r, ?_⟩
  set baseSize := max (2 * r ^ 2) (max Lerr Lcnt) with hbaseSize
  have hbase2 : 2 * r ^ 2 ≤ baseSize := le_max_left _ _
  have hb2 : r + 1 ≤ 2 * r ^ 2 := by nlinarith
  have hbase' : r + 1 ≤ baseSize := le_trans hb2 hbase2
  set layerSizes : Fin (depthC r) → ℕ :=
    fun layer => Fintype.card (RLayer baseSize r layer.val) with hlayerSizes
  have hcard_ge : ∀ layer : Fin (depthC r), baseSize ≤ layerSizes layer :=
    fun layer => RGenericBridge.rLayer_card_ge_base (r := r) baseSize layer.val
      (by omega) hbase'
  have hparents : ∀ layer, r ≤ layerSizes layer :=
    fun layer => le_trans (by omega) (hcard_ge layer)
  have hcount : ∀ layer,
      (layerSizes layer : ℝ) +
        ((r : ℝ) + 1) * logTwo (((layerSizes layer).choose r + 1 : ℕ) : ℝ) -
          slackC r * ((layerSizes layer).choose r : ℝ) < -1 := by
    intro layer
    refine hLcnt _ (le_trans ?_ (hcard_ge layer))
    exact le_trans (le_max_right _ _) (le_max_right _ _)
  have herror : ∀ layer : Fin (depthC r),
      worCorrectionR r (layerSizes layer) (27 / 20) < slackC r := by
    intro layer
    refine hLerr _ (le_trans ?_ (hcard_ge layer))
    exact le_trans (le_max_left _ _) (le_max_right _ _)
  filter_upwards [eventually_budget r hr (depthC r), Filter.eventually_gt_atTop 0]
    with dimension hbudget hdimension
  obtain ⟨retained, hout, hvert, hedge⟩ :=
    RGenericSampling.exists_good_retention (betaNN r) (slackC r) (r := r)
      layerSizes (radiusC r dimension) hdimension hparents hcount hbudget
  exact ⟨retained,
    rGraphOverFin_free_of_exclusion hr hGibbs hbase2 hdimension
      (depthC_increment r hr) herror retained hout,
    hvert, hedge⟩

/-- **Theorem 2.**  For every `r ≥ 2` there is a connected bipartite graph
`H` of degeneracy exactly `r` on finitely many vertices and constants
`c, ε > 0` with `c · n^(2 − 1/r + ε) ≤ ex(n, H)` for all large `n`. -/
theorem rDegenerateExtremalCounterexample_of_gibbs (r : ℕ) (hr : 2 ≤ r)
    (hGibbs : TypeEntropyBound r (supG r (27 / 20)) (27 / 20)) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧ H.IsBipartite ∧ IsDegenerate r H ∧ ¬ IsDegenerate (r - 1) H ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + ε) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  obtain ⟨baseSize, depth, hbase, hdepth, hhosts⟩ := exists_free_dense_hosts r hr hGibbs
  have hb : r + 1 ≤ baseSize := by nlinarith
  obtain ⟨q, H, hcon, hbip, hdeg, hnodeg, c, hc0, hbnd⟩ :=
    rDegenerateExtremalCounterexample_of_hosts hr hb hdepth hhosts
  exact ⟨q, H, hcon, hbip, hdeg, hnodeg, c, epsC r, hc0, epsC_pos r hr, hbnd⟩

/-- **Theorem 2 with the explicit exponent** `ε = 1/(48 r²)`, conditional on the
Gibbs bound. -/
theorem rDegenerateExtremalCounterexample_explicit_of_gibbs (r : ℕ) (hr : 2 ≤ r)
    (hGibbs : TypeEntropyBound r (supG r (27 / 20)) (27 / 20)) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧ H.IsBipartite ∧ IsDegenerate r H ∧ ¬ IsDegenerate (r - 1) H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (48 * (r : ℝ) ^ 2)) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  obtain ⟨baseSize, depth, hbase, hdepth, hhosts⟩ := exists_free_dense_hosts r hr hGibbs
  have hb : r + 1 ≤ baseSize := by nlinarith
  obtain ⟨q, H, hcon, hbip, hdeg, hnodeg, c, hc0, hbnd⟩ :=
    rDegenerateExtremalCounterexample_of_hosts hr hb hdepth hhosts
  refine ⟨q, H, hcon, hbip, hdeg, hnodeg, c, hc0, ?_⟩
  filter_upwards [hbnd, Filter.eventually_ge_atTop 1] with n hn hn1
  have hn1' : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn1
  have hmono : (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (48 * (r : ℝ) ^ 2)) ≤
      (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + epsC r) :=
    Real.rpow_le_rpow_of_exponent_le hn1' (by linarith [epsC_lower r hr])
  calc c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (48 * (r : ℝ) ^ 2))
      ≤ c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + epsC r) :=
        mul_le_mul_of_nonneg_left hmono hc0.le
    _ ≤ (SimpleGraph.extremalNumber n H : ℝ) := hn

/-- **Theorem 2 with the explicit exponent**, unconditional. -/
theorem rDegenerateExtremalCounterexample_explicit (r : ℕ) (hr : 2 ≤ r) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧ H.IsBipartite ∧ IsDegenerate r H ∧ ¬ IsDegenerate (r - 1) H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (48 * (r : ℝ) ^ 2)) ≤
            (SimpleGraph.extremalNumber n H : ℝ) :=
  rDegenerateExtremalCounterexample_explicit_of_gibbs r hr (typeEntropyBound_supG r hr)

/-- **Theorem 2**, unconditional: the Gibbs variational bound
`typeEntropyBound_supG` is proved above. -/
theorem rDegenerateExtremalCounterexample (r : ℕ) (hr : 2 ≤ r) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧ H.IsBipartite ∧ IsDegenerate r H ∧ ¬ IsDegenerate (r - 1) H ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + ε) ≤
            (SimpleGraph.extremalNumber n H : ℝ) :=
  rDegenerateExtremalCounterexample_of_gibbs r hr (typeEntropyBound_supG r hr)


end RAssembly

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
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (48 * (r : ℝ) ^ 2)) ≤
            (SimpleGraph.extremalNumber n H : ℝ) :=
  RAssembly.rDegenerateExtremalCounterexample_explicit r hr

-- The same, with the exponent gain pinned to `ε = 1/(48 r²)`.
open Classical in
theorem rDegenerateExtremalCounterexample_explicit (r : ℕ) (hr : 2 ≤ r) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsDegenerate r H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (48 * (r : ℝ) ^ 2)) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  obtain ⟨q, H, hcon, hbip, hdeg, -, hbnd⟩ :=
    RAssembly.rDegenerateExtremalCounterexample_explicit r hr
  exact ⟨q, H, hcon, hbip, hdeg, hbnd⟩

-- Compatibility form at the previous constant `ε = 1/(110 r²)` (weaker
-- exponent, follows from the `1/(48 r²)` statement by monotonicity).
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
  have hexp : 1 / (110 * (r : ℝ) ^ 2) ≤ 1 / (48 * (r : ℝ) ^ 2) := by
    rw [div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [sq_nonneg ((r : ℝ))]
  have hmono : (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (110 * (r : ℝ) ^ 2)) ≤
      (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (48 * (r : ℝ) ^ 2)) :=
    Real.rpow_le_rpow_of_exponent_le hn1' (by linarith)
  calc c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (110 * (r : ℝ) ^ 2))
      ≤ c * (n : ℝ) ^ ((2 : ℝ) - 1 / (r : ℝ) + 1 / (48 * (r : ℝ) ^ 2)) :=
        mul_le_mul_of_nonneg_left hmono hc0.le
    _ ≤ (SimpleGraph.extremalNumber n H : ℝ) := hn

end RDegenerateGraphsTarget
