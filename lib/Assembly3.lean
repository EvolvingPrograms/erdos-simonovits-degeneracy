import Sampling3
import Kernel3
import Bridge3
import ExactDegeneracy

/-!
# The hand-certified `r = 3` assembly

Machinery for Theorem 1; the target statements built on top of it are in
`Theorem1.lean`.  This route is independent of the general `r` pipeline —
this file does not import `lib/AssemblyR.lean` — and certifies the weaker
gain `1/4000`; the sharp `1/160` comes from the general pipeline at `r = 3`.

Brings together

* `Sampling3.lean`  — the counting layer (`ThreeDegenerateProfiles`) and the
  second-moment / retention layer (`ThreeSampling`);
* `Kernel3.lean`    — the entropy ledger (`ThreeDegenerateGraphs`).

The forbidden graph is built here directly on `ThreeDegenerateProfiles.TripleLayer`
(rather than on `LayeredGraph.lean`'s `Layer`): the two are definitionally the
same type, and using the counting layer's copy removes the transport entirely.
-/

namespace ThreeAssembly

open Finset TwoDegenerateGraphs ThreeDegenerateProfiles ThreeSampling
open scoped BigOperators

/-! ## Block A: the forbidden graph -/

/-- A `ParentSystem` with at most three parents per vertex.  Copy of the
published `TwoDegenerateGraphs.ParentSystem` with `parent_card ≤ 2` weakened
to `≤ 3`. -/
structure TripleParentSystem (V : Type*) where
  level : V → ℕ
  parents : V → Finset V
  parent_level : ∀ ⦃v u : V⦄, u ∈ parents v → level u + 1 = level v
  parent_card : ∀ v : V, (parents v).card ≤ 3

namespace TripleParentSystem

def graph {V : Type*} (P : TripleParentSystem V) : SimpleGraph V :=
  SimpleGraph.fromRel (fun v u => u ∈ P.parents v)

theorem graph_adj_iff {V : Type*} (P : TripleParentSystem V) (v u : V) :
    (P.graph).Adj v u ↔ v ≠ u ∧ (u ∈ P.parents v ∨ v ∈ P.parents u) := Iff.rfl

theorem graph_isBipartite {V : Type*} (P : TripleParentSystem V) :
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

theorem graph_isThreeDegenerate {V : Type*} (P : TripleParentSystem V) :
    IsDegenerate 3 P.graph := by
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

end TripleParentSystem

/-! ### The layered triple graph -/

abbrev TripleVertex (baseSize depth : ℕ) :=
  Σ i : Fin (depth + 1), TripleLayer baseSize i.val

def tripleLayerEmbedding (baseSize depth i : ℕ) (hi : i < depth + 1) :
    TripleLayer baseSize i ↪ TripleVertex baseSize depth where
  toFun v := ⟨⟨i, hi⟩, v⟩
  inj' := by intro v w heq; cases heq; rfl

noncomputable def tripleParents (baseSize depth : ℕ) :
    TripleVertex baseSize depth → Finset (TripleVertex baseSize depth)
  | ⟨⟨0, _⟩, _⟩ => ∅
  | ⟨⟨i + 1, hi⟩, v⟩ =>
      v.val.map (tripleLayerEmbedding baseSize depth i (by omega))

noncomputable def tripleParentSystem (baseSize depth : ℕ) :
    TripleParentSystem (TripleVertex baseSize depth) where
  level v := v.1.val
  parents := tripleParents baseSize depth
  parent_level := by
    classical
    rintro ⟨⟨i, hi⟩, v⟩ ⟨⟨j, hj⟩, u⟩ hparent
    cases i with
    | zero => simp [tripleParents] at hparent
    | succ i =>
        change {parents : Finset (TripleLayer baseSize i) // parents.card = 3} at v
        simp only [tripleParents, Finset.mem_map] at hparent
        obtain ⟨w, _, hw⟩ := hparent
        have hlevels := congrArg
          (fun z : TripleVertex baseSize depth => z.1.val) hw
        change i = j at hlevels
        change j + 1 = i + 1
        omega
  parent_card := by
    classical
    rintro ⟨⟨i, hi⟩, v⟩
    cases i with
    | zero => simp [tripleParents]
    | succ i =>
        change {parents : Finset (TripleLayer baseSize i) // parents.card = 3} at v
        simp [tripleParents, v.property]

def tripleBaseVertex (baseSize depth : ℕ) (a : Fin baseSize) :
    TripleVertex baseSize depth :=
  tripleLayerEmbedding baseSize depth 0 (by omega) a

theorem tripleLayer_reaches_base (baseSize depth : ℕ) :
    ∀ (i : ℕ) (hi : i < depth + 1) (v : TripleLayer baseSize i),
      ∃ a : Fin baseSize,
        (tripleParentSystem baseSize depth).graph.Reachable
          (tripleLayerEmbedding baseSize depth i hi v)
          (tripleBaseVertex baseSize depth a) := by
  intro i
  induction i with
  | zero => intro hi v; exact ⟨v, SimpleGraph.Reachable.rfl⟩
  | succ i ih =>
      intro hi v
      change {parents : Finset (TripleLayer baseSize i) // parents.card = 3} at v
      have hnonempty : v.val.Nonempty := by
        apply Finset.card_pos.mp; omega
      obtain ⟨parent, hparent⟩ := hnonempty
      let lower := tripleLayerEmbedding baseSize depth i (by omega) parent
      let upper := tripleLayerEmbedding baseSize depth (i + 1) hi v
      have hedge : (tripleParentSystem baseSize depth).graph.Adj upper lower := by
        apply (TripleParentSystem.graph_adj_iff _ upper lower).mpr
        constructor
        · intro heq
          have hlevels := congrArg
            (fun x : TripleVertex baseSize depth => x.1.val) heq
          change i + 1 = i at hlevels
          omega
        · left
          change lower ∈ tripleParents baseSize depth upper
          change lower ∈
            v.val.map (tripleLayerEmbedding baseSize depth i (by omega))
          exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
      obtain ⟨a, ha⟩ := ih (by omega) parent
      exact ⟨a, hedge.reachable.trans ha⟩

theorem tripleBaseVertices_reachable (baseSize depth : ℕ)
    (hbase : 3 ≤ baseSize) (hdepth : 0 < depth) (a b : Fin baseSize) :
    (tripleParentSystem baseSize depth).graph.Reachable
      (tripleBaseVertex baseSize depth a)
      (tripleBaseVertex baseSize depth b) := by
  classical
  letI : DecidableEq (TripleLayer baseSize 0) := Classical.decEq _
  -- pick a 3-element subset of the base layer containing `a` and `b`
  let a' : TripleLayer baseSize 0 := a
  let b' : TripleLayer baseSize 0 := b
  let s : Finset (TripleLayer baseSize 0) := {a', b'}
  have hcard : s.card ≤ 3 :=
    (Finset.card_insert_le _ _).trans (by rw [Finset.card_singleton]; omega)
  have huniv : (3 : ℕ) ≤ (Finset.univ : Finset (TripleLayer baseSize 0)).card := by
    have : Fintype.card (TripleLayer baseSize 0) = baseSize :=
      tripleLayer_card_zero baseSize
    simpa [Finset.card_univ, this] using hbase
  obtain ⟨c, hsub, -, hc3⟩ :=
    Finset.exists_subsuperset_card_eq (Finset.subset_univ s) hcard huniv
  have ha : a' ∈ c := hsub (Finset.mem_insert_self _ _)
  have hb : b' ∈ c := hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
  let triple : TripleLayer baseSize 1 := ⟨c, hc3⟩
  let bridge := tripleLayerEmbedding baseSize depth 1 (by omega) triple
  have hadj (x : TripleLayer baseSize 0) (hx : x ∈ c) :
      (tripleParentSystem baseSize depth).graph.Adj
        bridge (tripleBaseVertex baseSize depth x) := by
    apply (TripleParentSystem.graph_adj_iff _ bridge _).mpr
    constructor
    · intro heq
      have hlevels := congrArg
        (fun z : TripleVertex baseSize depth => z.1.val) heq
      change 1 = 0 at hlevels
      omega
    · left
      change tripleBaseVertex baseSize depth x ∈ tripleParents baseSize depth bridge
      change tripleLayerEmbedding baseSize depth 0 (by omega) x ∈
        c.map (tripleLayerEmbedding baseSize depth 0 (by omega))
      exact Finset.mem_map.mpr ⟨x, hx, rfl⟩
  exact (hadj a ha).symm.reachable.trans (hadj b hb).reachable

theorem tripleGraph_connected (baseSize depth : ℕ)
    (hbase : 3 ≤ baseSize) (hdepth : 0 < depth) :
    (tripleParentSystem baseSize depth).graph.Connected := by
  have hpos : 0 < baseSize := by omega
  let root : Fin baseSize := ⟨0, hpos⟩
  apply (SimpleGraph.connected_iff_exists_forall_reachable _).mpr
  refine ⟨tripleBaseVertex baseSize depth root, ?_⟩
  rintro ⟨⟨i, hi⟩, v⟩
  obtain ⟨a, ha⟩ := tripleLayer_reaches_base baseSize depth i hi v
  exact (tripleBaseVertices_reachable baseSize depth hbase hdepth root a).trans ha.symm

theorem tripleGraph_isBipartite (baseSize depth : ℕ) :
    (tripleParentSystem baseSize depth).graph.IsBipartite :=
  TripleParentSystem.graph_isBipartite _

theorem tripleGraph_isThreeDegenerate (baseSize depth : ℕ) :
    IsDegenerate 3 (tripleParentSystem baseSize depth).graph :=
  TripleParentSystem.graph_isThreeDegenerate _

noncomputable instance tripleVertexFintype (baseSize depth : ℕ) :
    Fintype (TripleVertex baseSize depth) := by
  classical infer_instance

noncomputable def tripleGraphOverFin (baseSize depth : ℕ) :
    SimpleGraph (Fin (Fintype.card (TripleVertex baseSize depth))) :=
  (tripleParentSystem baseSize depth).graph.overFin rfl

noncomputable def tripleGraphOverFinIso (baseSize depth : ℕ) :
    (tripleParentSystem baseSize depth).graph ≃g tripleGraphOverFin baseSize depth :=
  (tripleParentSystem baseSize depth).graph.overFinIso rfl

theorem isThreeDegenerate_of_iso {V W : Type*}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : IsDegenerate 3 G) : IsDegenerate 3 H := by
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

theorem tripleGraphOverFin_connected (baseSize depth : ℕ)
    (hbase : 3 ≤ baseSize) (hdepth : 0 < depth) :
    (tripleGraphOverFin baseSize depth).Connected :=
  (tripleGraphOverFinIso baseSize depth).connected_iff.mp
    (tripleGraph_connected baseSize depth hbase hdepth)

theorem tripleGraphOverFin_isBipartite (baseSize depth : ℕ) :
    (tripleGraphOverFin baseSize depth).IsBipartite :=
  isBipartite_of_iso (tripleGraphOverFinIso baseSize depth)
    (tripleGraph_isBipartite baseSize depth)

theorem tripleGraphOverFin_isThreeDegenerate (baseSize depth : ℕ) :
    IsDegenerate 3 (tripleGraphOverFin baseSize depth) :=
  isThreeDegenerate_of_iso (tripleGraphOverFinIso baseSize depth)
    (tripleGraph_isThreeDegenerate baseSize depth)

/-! ### Exact degeneracy: the lower bound

For `baseSize ≥ 4` the triple graph is not 2-degenerate, by the generic
two-layer witness `ExactDegeneracy.not_isDegenerate_of_layer_witness`
applied to layers 0 and 1. -/

theorem tripleGraph_not_isTwoDegenerate (baseSize depth : ℕ)
    (hbase : 4 ≤ baseSize) (hdepth : 0 < depth) :
    ¬ IsDegenerate 2 (tripleParentSystem baseSize depth).graph := by
  classical
  have h0 : (0 : ℕ) < depth + 1 := by omega
  have h1 : (1 : ℕ) < depth + 1 := by omega
  set emb0 := tripleLayerEmbedding baseSize depth 0 h0 with hemb0
  set emb1 := tripleLayerEmbedding baseSize depth 1 h1 with hemb1
  -- layer-0 and layer-1 vertices sit at different levels, so never coincide
  have hne01 : ∀ (a : TripleLayer baseSize 0) (c : TripleLayer baseSize 1),
      emb0 a ≠ emb1 c := by
    intro a c heq
    have := congrArg (fun z : TripleVertex baseSize depth => z.1.val) heq
    simp [hemb0, hemb1, tripleLayerEmbedding] at this
  -- adjacency between a root and a layer-1 child containing it
  have hadj : ∀ (a : TripleLayer baseSize 0)
      (c : {parents : Finset (TripleLayer baseSize 0) // parents.card = 3}),
      a ∈ c.val →
        (tripleParentSystem baseSize depth).graph.Adj (emb0 a) (emb1 c) := by
    intro a c hac
    refine ((tripleParentSystem baseSize depth).graph_adj_iff _ _).mpr
      ⟨hne01 a c, Or.inr ?_⟩
    show emb0 a ∈ tripleParents baseSize depth (emb1 c)
    exact Finset.mem_map_of_mem emb0 hac
  have h := ExactDegeneracy.not_isDegenerate_of_layer_witness (r := 3)
    (by norm_num) (by rw [tripleLayer_card_zero]; omega) emb0 emb1 hadj
  simpa using h

/-- Exact degeneracy transported to the `Fin q` form. -/
theorem tripleGraphOverFin_not_isTwoDegenerate (baseSize depth : ℕ)
    (hbase : 4 ≤ baseSize) (hdepth : 0 < depth) :
    ¬ IsDegenerate 2 (tripleGraphOverFin baseSize depth) := by
  intro h
  exact tripleGraph_not_isTwoDegenerate baseSize depth hbase hdepth
    (ExactDegeneracy.isDegenerate_of_iso
      (tripleGraphOverFinIso baseSize depth).symm h)

/-! ### Layer equivalences and parent/child adjacency -/

noncomputable def tripleLayerFinEquiv (baseSize layer : ℕ) :
    TripleLayer baseSize layer ≃
      Fin (Fintype.card (TripleLayer baseSize layer)) :=
  Fintype.equivFin (TripleLayer baseSize layer)

noncomputable def tripleLayerTripleEquiv (baseSize layer : ℕ) :
    TripleLayer (Fintype.card (TripleLayer baseSize layer)) 1 ≃
      TripleLayer baseSize (layer + 1) := by
  classical
  change
    {parents : Finset (Fin (Fintype.card (TripleLayer baseSize layer))) //
        parents.card = 3} ≃
      {parents : Finset (TripleLayer baseSize layer) // parents.card = 3}
  exact
    (tripleLayerFinEquiv baseSize layer).symm.finsetCongr.subtypeEquiv
      (fun parents => by simp [Equiv.finsetCongr_apply])

theorem tripleLayerTriple_nonempty {parentCount : ℕ} (hparents : 3 ≤ parentCount) :
    Nonempty (TripleLayer parentCount 1) := by
  apply Fintype.card_pos_iff.mp
  rw [tripleLayer_card_succ parentCount 0, tripleLayer_card_zero]
  exact Nat.choose_pos hparents

theorem tripleGraph_parent_child_adj
    (baseSize depth layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (child : TripleLayer baseSize (layer + 1))
    (parent : TripleLayer baseSize layer)
    (hparent : parent ∈ child.val) :
    (tripleParentSystem baseSize depth).graph.Adj
      (tripleLayerEmbedding baseSize depth (layer + 1) hlayer child)
      (tripleLayerEmbedding baseSize depth layer (by omega) parent) := by
  apply (TripleParentSystem.graph_adj_iff _ _ _).mpr
  constructor
  · intro hequal
    have hlevels := congrArg
      (fun vertex : TripleVertex baseSize depth => vertex.1.val) hequal
    change layer + 1 = layer at hlevels
    omega
  · left
    change tripleLayerEmbedding baseSize depth layer (by omega) parent ∈
      tripleParents baseSize depth
        (tripleLayerEmbedding baseSize depth (layer + 1) hlayer child)
    change tripleLayerEmbedding baseSize depth layer (by omega) parent ∈
      child.val.map (tripleLayerEmbedding baseSize depth layer (by omega))
    exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩

/-! ## Block D: the asymptotic endgame

Constants.  `β = 0.9126` is the top of the window `(0.9125, 0.9128517834)`
left open by `results_H_lean_entropy.md` (`A₀ = 17/80`, so
`A = 17/80 + (7/4)·(2/5) = 0.9125`), and `ε = 1/4000` is the exponent gain
certified by `ThreeSampling.threeExponent_product_gt`. -/

open Filter Topology

noncomputable def betaThree : NNReal := 9126 / 10000

theorem betaThree_le : ((betaThree : NNReal) : ℝ) ≤ 9126 / 10000 := by
  unfold betaThree; norm_num

theorem betaThree_lt_one : ((betaThree : NNReal) : ℝ) < 1 := by
  unfold betaThree; norm_num

theorem betaThree_pos : (0 : ℝ) < ((betaThree : NNReal) : ℝ) := by
  unfold betaThree; norm_num

noncomputable def epsThree : ℝ := 1 / 4000

theorem epsThree_pos : 0 < epsThree := by unfold epsThree; norm_num

/-- The extremal exponent `5/3 + ε`. -/
noncomputable def threeExtremalPower : ℝ := 5 / 3 + epsThree

theorem threeExtremalPower_pos : 0 < threeExtremalPower := by
  unfold threeExtremalPower epsThree; norm_num

/-- Half the slack in the exponent inequality. -/
noncomputable def threeEntropyGap : ℝ :=
  (sampledThreeEdgeEntropyRate betaThree -
    (1 - ((betaThree : NNReal) : ℝ)) * threeExtremalPower * Real.log 2) / 2

theorem threeEntropyGap_pos : 0 < threeEntropyGap := by
  have h := sampledThreeEdgeEntropyRate_gt betaThree epsThree betaThree_le
    (by unfold epsThree; norm_num) epsThree_pos
  unfold threeEntropyGap threeExtremalPower
  linarith

theorem sampledThreeEdgeEntropyRate_eq_power :
    sampledThreeEdgeEntropyRate betaThree =
      (1 - ((betaThree : NNReal) : ℝ)) * threeExtremalPower * Real.log 2 +
        2 * threeEntropyGap := by
  unfold threeEntropyGap; ring

/-! ### The expected retained edge count grows like `exp(m · rate)` -/

theorem eventually_threeExpectedRetainedEdge_entropy_lower
    (loss : ℝ) (hloss : 0 < loss) :
    ∀ᶠ dimension : ℕ in atTop,
      Real.exp ((dimension : ℝ) *
          (sampledThreeEdgeEntropyRate betaThree - loss)) /
          ((dimension + 1 : ℕ) : ℝ) ≤
        threeExpectedRetainedEdgeCount betaThree dimension
          (threeHammingRadius dimension) := by
  filter_upwards [eventually_threeHammingRadius_binEntropy_ge loss hloss]
    with dimension hentropy
  have hdegree :
      Real.exp ((dimension : ℝ) *
          Real.binEntropy
            ((threeHammingRadius dimension : ℝ) / (dimension : ℝ))) /
          ((dimension + 1 : ℕ) : ℝ) ≤
        ((∑ distance ∈ Finset.range (threeHammingRadius dimension + 1),
          dimension.choose distance : ℕ) : ℝ) := by
    have hball := threeHammingBall_card_entropy_lower dimension
      (fun _ : Fin dimension => false)
    rw [hammingBall_card] at hball
    exact hball
  calc
    Real.exp ((dimension : ℝ) *
        (sampledThreeEdgeEntropyRate betaThree - loss)) /
        ((dimension + 1 : ℕ) : ℝ) =
      (threeRetentionProbability betaThree dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        (Real.exp ((dimension : ℝ) * (Real.binEntropy tauThree - loss)) /
          ((dimension + 1 : ℕ) : ℝ)) := by
        rw [threeRetentionProbability_sq_mul_wordCount_eq_exp,
          ← mul_div_assoc, ← Real.exp_add]
        congr 1
        unfold sampledThreeEdgeEntropyRate
        ring_nf
    _ ≤ (threeRetentionProbability betaThree dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        (Real.exp ((dimension : ℝ) *
            Real.binEntropy
              ((threeHammingRadius dimension : ℝ) / (dimension : ℝ))) /
          ((dimension + 1 : ℕ) : ℝ)) := by
        gcongr
    _ ≤ (threeRetentionProbability betaThree dimension ^ 2 *
        ((2 ^ dimension : ℕ) : ℝ)) *
        ((∑ distance ∈ Finset.range (threeHammingRadius dimension + 1),
          dimension.choose distance : ℕ) : ℝ) := by
        gcongr
    _ = threeExpectedRetainedEdgeCount betaThree dimension
        (threeHammingRadius dimension) := by
      rw [threeExpectedRetainedEdgeCount_eq]

theorem threeExpectedRetainedEdgeCount_tendsto_atTop :
    Tendsto
      (fun dimension : ℕ =>
        threeExpectedRetainedEdgeCount betaThree dimension
          (threeHammingRadius dimension))
      atTop atTop := by
  have hrate := sampledThreeEdgeEntropyRate_pos betaThree betaThree_le
  have hloss : 0 < sampledThreeEdgeEntropyRate betaThree / 2 := by positivity
  have hlower := eventually_threeExpectedRetainedEdge_entropy_lower
    (sampledThreeEdgeEntropyRate betaThree / 2) hloss
  have hgrowth := exp_mul_div_nat_succ_tendsto_atTop
    (sampledThreeEdgeEntropyRate betaThree / 2) hloss
  have hhalf :
      sampledThreeEdgeEntropyRate betaThree -
          sampledThreeEdgeEntropyRate betaThree / 2 =
        sampledThreeEdgeEntropyRate betaThree / 2 := by ring
  apply tendsto_atTop_mono' atTop _ hgrowth
  filter_upwards [hlower] with dimension hdimension
  simpa only [hhalf, mul_comm] using hdimension

theorem threeExpectedRetainedEdgeCount_inv_tendsto_zero :
    Tendsto
      (fun dimension : ℕ =>
        1 / threeExpectedRetainedEdgeCount betaThree dimension
          (threeHammingRadius dimension))
      atTop (𝓝 0) := by
  have htendsto := tendsto_inv_atTop_zero.comp
    threeExpectedRetainedEdgeCount_tendsto_atTop
  refine htendsto.congr' ?_
  filter_upwards [] with dimension
  simp only [Function.comp_apply, one_div]

/-! ### The host vertex count -/

noncomputable def threeVertexCount (dimension : ℕ) : ℕ :=
  ⌈3 * threeRetentionProbability betaThree dimension *
    ((2 ^ dimension : ℕ) : ℝ)⌉₊

open Classical in
theorem retainedVertex_card_le_threeVertexCount
    (dimension : ℕ) (retained : Set (Bool × HammingWord dimension))
    (hvertices :
      threeRetainedVertexCount dimension retained <
        3 * threeRetentionProbability betaThree dimension *
          ((2 ^ dimension : ℕ) : ℝ)) :
    Fintype.card retained ≤ threeVertexCount dimension := by
  have hreal :
      (Fintype.card retained : ℝ) ≤ (threeVertexCount dimension : ℝ) := by
    calc
      (Fintype.card retained : ℝ) =
          threeRetainedVertexCount dimension retained :=
        (threeRetainedVertexCount_eq_card dimension retained).symm
      _ ≤ 3 * threeRetentionProbability betaThree dimension *
            ((2 ^ dimension : ℕ) : ℝ) := hvertices.le
      _ ≤ (threeVertexCount dimension : ℝ) := Nat.le_ceil _
  exact_mod_cast hreal

theorem threeVertexCount_le_four_wordMean (dimension : ℕ)
    (hmean : 1 ≤ threeRetentionProbability betaThree dimension *
      ((2 ^ dimension : ℕ) : ℝ)) :
    (threeVertexCount dimension : ℝ) ≤
      4 * (threeRetentionProbability betaThree dimension *
        ((2 ^ dimension : ℕ) : ℝ)) := by
  have hpos := threeRetentionProbability_pos betaThree dimension
  have hargument :
      0 ≤ 3 * threeRetentionProbability betaThree dimension *
        ((2 ^ dimension : ℕ) : ℝ) := by positivity
  have hceiling :
      (threeVertexCount dimension : ℝ) <
        3 * threeRetentionProbability betaThree dimension *
          ((2 ^ dimension : ℕ) : ℝ) + 1 := by
    unfold threeVertexCount
    exact Nat.ceil_lt_add_one hargument
  nlinarith

theorem eventually_threeVertexCount_le_four_wordMean :
    ∀ᶠ dimension : ℕ in atTop,
      (threeVertexCount dimension : ℝ) ≤
        4 * (threeRetentionProbability betaThree dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
  have hlarge := Filter.tendsto_atTop.1
    (threeRetentionProbability_mul_wordCount_tendsto_atTop betaThree
      betaThree_lt_one) (1 : ℝ)
  filter_upwards [hlarge] with dimension hdimension
  exact threeVertexCount_le_four_wordMean dimension hdimension

theorem eventually_threeEntropyGap_dominates_power_constant :
    ∀ᶠ dimension : ℕ in atTop,
      2 * (4 : ℝ) ^ threeExtremalPower ≤
        Real.exp (threeEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ) :=
  Filter.tendsto_atTop.1
    (exp_mul_div_nat_succ_tendsto_atTop threeEntropyGap threeEntropyGap_pos)
    (2 * (4 : ℝ) ^ threeExtremalPower)

theorem eventually_threeVertexCount_power_le_expectedRetainedEdge :
    ∀ᶠ dimension : ℕ in atTop,
      (threeVertexCount dimension : ℝ) ^ threeExtremalPower ≤
        threeExpectedRetainedEdgeCount betaThree dimension
          (threeHammingRadius dimension) / 2 := by
  have hlower := eventually_threeExpectedRetainedEdge_entropy_lower
    threeEntropyGap threeEntropyGap_pos
  filter_upwards [hlower, eventually_threeVertexCount_le_four_wordMean,
    eventually_threeEntropyGap_dominates_power_constant] with dimension
    hedge_lower hvertex_bound hconstant_bound
  have hconstant_half :
      (4 : ℝ) ^ threeExtremalPower ≤
        (Real.exp (threeEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by linarith
  have hexponent :
      ((1 - ((betaThree : NNReal) : ℝ)) * (dimension : ℝ) * Real.log 2) *
            threeExtremalPower + threeEntropyGap * (dimension : ℝ) =
        (dimension : ℝ) *
          (sampledThreeEdgeEntropyRate betaThree - threeEntropyGap) := by
    rw [sampledThreeEdgeEntropyRate_eq_power]; ring
  have hppos := threeRetentionProbability_pos betaThree dimension
  calc
    (threeVertexCount dimension : ℝ) ^ threeExtremalPower ≤
      (4 * (threeRetentionProbability betaThree dimension *
        ((2 ^ dimension : ℕ) : ℝ))) ^ threeExtremalPower := by
        apply Real.rpow_le_rpow (by positivity) hvertex_bound
          threeExtremalPower_pos.le
    _ = (4 : ℝ) ^ threeExtremalPower *
        Real.exp (((1 - ((betaThree : NNReal) : ℝ)) * (dimension : ℝ) *
          Real.log 2) * threeExtremalPower) := by
      rw [threeRetentionProbability_mul_wordCount_eq_exp,
        Real.mul_rpow (by norm_num) (Real.exp_pos _).le, ← Real.exp_mul]
    _ ≤ Real.exp (((1 - ((betaThree : NNReal) : ℝ)) * (dimension : ℝ) *
            Real.log 2) * threeExtremalPower) *
        ((Real.exp (threeEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2) := by
      rw [mul_comm ((4 : ℝ) ^ threeExtremalPower)]
      exact mul_le_mul_of_nonneg_left hconstant_half (Real.exp_pos _).le
    _ = (Real.exp (((1 - ((betaThree : NNReal) : ℝ)) * (dimension : ℝ) *
            Real.log 2) * threeExtremalPower +
          threeEntropyGap * (dimension : ℝ)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by
      rw [Real.exp_add]; ring
    _ = (Real.exp ((dimension : ℝ) *
          (sampledThreeEdgeEntropyRate betaThree - threeEntropyGap)) /
          ((dimension + 1 : ℕ) : ℝ)) / 2 := by rw [hexponent]
    _ ≤ threeExpectedRetainedEdgeCount betaThree dimension
          (threeHammingRadius dimension) / 2 := by gcongr

theorem threeVertexCount_tendsto_atTop :
    Tendsto threeVertexCount atTop atTop := by
  have hscaled :
      Tendsto (fun dimension : ℕ =>
          3 * (threeRetentionProbability betaThree dimension *
            ((2 ^ dimension : ℕ) : ℝ))) atTop atTop :=
    (threeRetentionProbability_mul_wordCount_tendsto_atTop betaThree
      betaThree_lt_one).const_mul_atTop (by norm_num)
  have hceiling := tendsto_nat_ceil_atTop.comp hscaled
  apply hceiling.congr'
  filter_upwards [] with dimension
  change ⌈3 * (threeRetentionProbability betaThree dimension *
    ((2 ^ dimension : ℕ) : ℝ))⌉₊ = threeVertexCount dimension
  unfold threeVertexCount
  congr 1
  ring

theorem threeVertexCount_succ_le_two_mul (dimension : ℕ) :
    threeVertexCount (dimension + 1) ≤ 2 * threeVertexCount dimension := by
  have hfactor :
      Real.exp ((1 - ((betaThree : NNReal) : ℝ)) * Real.log 2) ≤ (2 : ℝ) := by
    calc
      Real.exp ((1 - ((betaThree : NNReal) : ℝ)) * Real.log 2) ≤
          Real.exp (Real.log 2) := by
        apply Real.exp_le_exp.mpr
        nlinarith [mul_pos betaThree_pos log_two_pos]
      _ = 2 := Real.exp_log (by norm_num)
  have hrecurrence :
      threeRetentionProbability betaThree (dimension + 1) *
          ((2 ^ (dimension + 1) : ℕ) : ℝ) =
        Real.exp ((1 - ((betaThree : NNReal) : ℝ)) * Real.log 2) *
          (threeRetentionProbability betaThree dimension *
            ((2 ^ dimension : ℕ) : ℝ)) := by
    rw [threeRetentionProbability_mul_wordCount_eq_exp,
      threeRetentionProbability_mul_wordCount_eq_exp, ← Real.exp_add]
    congr 1
    push_cast
    ring
  have hppos := threeRetentionProbability_pos betaThree dimension
  unfold threeVertexCount
  apply Nat.ceil_le.mpr
  norm_num only [Nat.cast_mul, Nat.cast_ofNat]
  calc
    3 * threeRetentionProbability betaThree (dimension + 1) *
        ((2 ^ (dimension + 1) : ℕ) : ℝ) =
      Real.exp ((1 - ((betaThree : NNReal) : ℝ)) * Real.log 2) *
        (3 * threeRetentionProbability betaThree dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
        rw [show 3 * threeRetentionProbability betaThree (dimension + 1) *
              ((2 ^ (dimension + 1) : ℕ) : ℝ) =
            3 * (threeRetentionProbability betaThree (dimension + 1) *
              ((2 ^ (dimension + 1) : ℕ) : ℝ)) by ring, hrecurrence]
        ring
    _ ≤ 2 * (3 * threeRetentionProbability betaThree dimension *
          ((2 ^ dimension : ℕ) : ℝ)) := by
        exact mul_le_mul_of_nonneg_right hfactor (by positivity)
    _ ≤ 2 * (⌈3 * threeRetentionProbability betaThree dimension *
            ((2 ^ dimension : ℕ) : ℝ)⌉₊ : ℝ) := by
        gcongr
        exact Nat.le_ceil _

theorem exists_threeVertexCount_bracket (minimum n : ℕ)
    (hminimum : threeVertexCount minimum ≤ n) :
    ∃ dimension : ℕ, minimum ≤ dimension ∧
      threeVertexCount dimension ≤ n ∧ n < threeVertexCount (dimension + 1) := by
  have hlarge : ∀ᶠ dimension : ℕ in atTop, n < threeVertexCount dimension := by
    have hevent := Filter.tendsto_atTop.1 threeVertexCount_tendsto_atTop (n + 1)
    filter_upwards [hevent] with dimension hdimension
    omega
  obtain ⟨dimension, hdimension, hafter⟩ :=
    (hlarge.and (Filter.eventually_ge_atTop minimum)).exists
  have hexists : ∃ offset : ℕ, n < threeVertexCount (minimum + offset) := by
    refine ⟨dimension - minimum, ?_⟩
    rw [Nat.add_sub_of_le hafter]
    exact hdimension
  let offset : ℕ := Nat.find hexists
  have hnext : n < threeVertexCount (minimum + offset) := Nat.find_spec hexists
  have hoffset : 0 < offset := by
    by_contra hnot
    have hzero : offset = 0 := Nat.eq_zero_of_not_pos hnot
    simp only [hzero, Nat.add_zero] at hnext
    omega
  refine ⟨minimum + (offset - 1), by omega, ?_, ?_⟩
  · exact Nat.le_of_not_gt (Nat.find_min hexists (by omega))
  · rw [show minimum + (offset - 1) + 1 = minimum + offset by omega]
    exact hnext

/-! ## Block E: the exclusion parameters

`slackThree = δ`, `baseSizeThree = L₀`, `depthThree = s`.  The window budget is

    β − A = 0.9126 − 0.9125 = 10⁻⁴,   A = A₀ + λτ = 17/80 + (7/4)(2/5),

and the exclusion needs `β − 2δ − A > 0`, hence `δ < 5·10⁻⁵`; we take
`δ = 2·10⁻⁵`, leaving a per-layer potential increment of
`2(β − 2δ − A) = 1.2·10⁻⁴`, so `s > 1/1.2·10⁻⁴ ≈ 8334`. -/

noncomputable def slackThree : ℝ := 1 / 50000

theorem slackThree_pos : 0 < slackThree := by unfold slackThree; norm_num

/-- `A = A₀ + λ τ = 17/80 + (7/4)·(2/5) = 0.9125`, the ledger constant in bits. -/
noncomputable def entropyLowerEndpointThree : ℝ := 17 / 80 + (7 / 4) * (2 / 5)

/-- The per-layer potential increment forced by the exclusion. -/
noncomputable def potentialIncrementThree : ℝ :=
  2 * (((betaThree : NNReal) : ℝ) - 2 * slackThree - entropyLowerEndpointThree)

theorem potentialIncrementThree_pos : 0 < potentialIncrementThree := by
  unfold potentialIncrementThree entropyLowerEndpointThree slackThree betaThree
  norm_num

def baseSizeThree : ℕ := 10 ^ 7

def depthThree : ℕ := 10000

theorem depthThree_increment : 1 < (depthThree : ℝ) * potentialIncrementThree := by
  unfold depthThree potentialIncrementThree entropyLowerEndpointThree slackThree betaThree
  norm_num

/-! ### The generic potential induction -/

theorem potential_layers_impossible (depth : ℕ) (potential : ℕ → ℝ) (gap : ℝ)
    (hrange : ∀ i ≤ depth, 0 ≤ potential i ∧ potential i ≤ 1)
    (hincrement : ∀ i < depth, gap < potential (i + 1) - potential i)
    (hdepth : 1 < (depth : ℝ) * gap) : False := by
  have htotal : ∀ i ≤ depth, (i : ℝ) * gap ≤ potential i - potential 0 := by
    intro i hi
    induction i with
    | zero => simp
    | succ i ih =>
        have hprevious := ih (by omega)
        have hnext := (hincrement i (by omega)).le
        push_cast
        linarith
  have hstart := (hrange 0 (by omega)).1
  have hfinish := (hrange depth le_rfl).2
  have hsum := htotal depth le_rfl
  linarith

/-- One layer of the exclusion ledger. -/
theorem potential_increment_three
    (potentialBefore potentialAfter conditionalEntropy error : ℝ)
    (herror : error < slackThree)
    (hlower : ((betaThree : NNReal) : ℝ) - slackThree < conditionalEntropy)
    (hupper : conditionalEntropy ≤
      entropyLowerEndpointThree + (potentialAfter - potentialBefore) / 2 + error) :
    potentialIncrementThree < potentialAfter - potentialBefore := by
  unfold potentialIncrementThree
  linarith

/-! ### Layer sizes -/

theorem le_choose_three_of_four {size : ℕ} (hsize : 4 ≤ size) :
    size ≤ size.choose 3 := by
  induction size, hsize using Nat.le_induction with
  | base => decide
  | succ n hn ih =>
      have hstep : (n + 1).choose 3 = n.choose 2 + n.choose 3 :=
        Nat.choose_succ_succ' n 2
      have hn2 : 1 ≤ n.choose 2 := Nat.choose_pos (by omega)
      omega

theorem tripleLayer_card_ge_base (baseSize i : ℕ) (hbase : 4 ≤ baseSize) :
    baseSize ≤ Fintype.card (TripleLayer baseSize i) := by
  induction i with
  | zero => rw [tripleLayer_card_zero]
  | succ i ih =>
      rw [tripleLayer_card_succ]
      exact ih.trans (le_choose_three_of_four (hbase.trans ih))

/-! ### The counting hypothesis `L + 4 log₂(C(L,3)+1) − δ·C(L,3) < −1` -/

theorem logTwo_tripleLayer_card_add_one_le (L : ℕ) (hL : 4 ≤ L) :
    logTwo ((L.choose 3 + 1 : ℕ) : ℝ) ≤ 3 * (L : ℝ) / Real.log 2 := by
  have hLreal : (4 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
  set x : ℝ := ((L.choose 3 + 1 : ℕ) : ℝ) with hx
  have hxpos : 0 < x := by rw [hx]; positivity
  have hchoose : (L.choose 3 : ℝ) ≤ (L : ℝ) ^ 3 / 6 := by
    have h := Nat.choose_le_pow_div (α := ℝ) 3 L
    simpa [Nat.factorial] using h
  have hxle : x ≤ (L : ℝ) ^ 3 := by
    have hcube : (64 : ℝ) ≤ (L : ℝ) ^ 3 := by
      nlinarith [hLreal, sq_nonneg ((L : ℝ) - 4), sq_nonneg ((L : ℝ) + 4)]
    rw [hx]; push_cast; linarith
  have hlogx : Real.log x ≤ 3 * Real.log L := by
    calc Real.log x ≤ Real.log ((L : ℝ) ^ 3) := Real.log_le_log hxpos hxle
      _ = 3 * Real.log L := by rw [Real.log_pow]; push_cast; ring
  have hlogL : Real.log L ≤ (L : ℝ) := by
    have := Real.log_le_sub_one_of_pos (show (0:ℝ) < (L:ℝ) by linarith)
    linarith
  rw [hx] at *
  change Real.log _ / Real.log 2 ≤ 3 * (L : ℝ) / Real.log 2
  apply (div_le_div_iff_of_pos_right log_two_pos).mpr
  linarith

theorem counting_hypothesis_of_large (L : ℕ) (hL : baseSizeThree ≤ L) :
    (L : ℝ) + 4 * logTwo ((L.choose 3 + 1 : ℕ) : ℝ) -
      slackThree * (L.choose 3 : ℝ) < -1 := by
  have hL4 : 4 ≤ L := by unfold baseSizeThree at hL; omega
  have hLreal : (10 ^ 7 : ℝ) ≤ (L : ℝ) := by
    have : (baseSizeThree : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    unfold baseSizeThree at this; push_cast at this; linarith
  have hlog := logTwo_tripleLayer_card_add_one_le L hL4
  have hlog2 : (2 : ℝ) / 3 ≤ Real.log 2 := by
    have := Real.log_two_gt_d9; linarith
  have hlogbound : 4 * logTwo ((L.choose 3 + 1 : ℕ) : ℝ) ≤ 18 * (L : ℝ) := by
    have h1 : 3 * (L : ℝ) / Real.log 2 ≤ 3 * (L : ℝ) / (2 / 3) := by
      apply div_le_div_of_nonneg_left (by linarith) (by norm_num) hlog2
    have : logTwo ((L.choose 3 + 1 : ℕ) : ℝ) ≤ 4.5 * (L : ℝ) := by
      calc logTwo ((L.choose 3 + 1 : ℕ) : ℝ) ≤ 3 * (L : ℝ) / Real.log 2 := hlog
        _ ≤ 3 * (L : ℝ) / (2 / 3) := h1
        _ = 4.5 * (L : ℝ) := by ring
    linarith
  -- lower bound on `C(L,3)`
  have hchoose : (((L + 1 - 3 : ℕ) : ℝ) ^ 3) / 6 ≤ (L.choose 3 : ℝ) := by
    have h := Nat.pow_le_choose (α := ℝ) 3 L
    simpa [Nat.factorial] using h
  have hsub : ((L + 1 - 3 : ℕ) : ℝ) = (L : ℝ) - 2 := by
    have : L + 1 - 3 = L - 2 := by omega
    rw [this]
    have : (2 : ℕ) ≤ L := by omega
    push_cast [Nat.cast_sub this]
    ring
  rw [hsub] at hchoose
  have hlow : ((L : ℝ) - 2) ^ 3 / 6 ≤ (L.choose 3 : ℝ) := hchoose
  unfold slackThree
  nlinarith [hlow, hLreal, hlogbound, sq_nonneg ((L : ℝ) - 2)]

/-! ### The sampling budget holds eventually -/

theorem eventually_budget (depth : ℕ) :
    ∀ᶠ dimension : ℕ in atTop,
      ((2 * depth : ℕ) : ℝ) * Real.exp (-(dimension : ℝ) * Real.log 2) +
        4 / threeExpectedRetainedVertexCount betaThree dimension +
        (4 / threeExpectedRetainedEdgeCount betaThree dimension
            (threeHammingRadius dimension) +
          8 / (threeRetentionProbability betaThree dimension *
            ((2 ^ dimension : ℕ) : ℝ))) < 1 := by
  have h1 : Tendsto (fun dimension : ℕ =>
      ((2 * depth : ℕ) : ℝ) * Real.exp (-(dimension : ℝ) * Real.log 2))
      atTop (𝓝 0) := pairLayerExclusionProbability_tendsto_zero depth
  have h2 : Tendsto (fun dimension : ℕ =>
      4 / threeExpectedRetainedVertexCount betaThree dimension) atTop (𝓝 0) := by
    have h := (threeExpectedRetainedVertexCount_inv_tendsto_zero betaThree
      betaThree_lt_one).const_mul (4 : ℝ)
    rw [mul_zero] at h
    exact Filter.Tendsto.congr (fun x => mul_one_div 4 _) h
  have h3 : Tendsto (fun dimension : ℕ =>
      4 / threeExpectedRetainedEdgeCount betaThree dimension
        (threeHammingRadius dimension)) atTop (𝓝 0) := by
    have h := threeExpectedRetainedEdgeCount_inv_tendsto_zero.const_mul (4 : ℝ)
    rw [mul_zero] at h
    exact Filter.Tendsto.congr (fun x => mul_one_div 4 _) h
  have h4 : Tendsto (fun dimension : ℕ =>
      8 / (threeRetentionProbability betaThree dimension *
        ((2 ^ dimension : ℕ) : ℝ))) atTop (𝓝 0) := by
    have h := (threeRetentionProbability_mul_wordCount_inv_tendsto_zero betaThree
      betaThree_lt_one).const_mul (8 : ℝ)
    rw [mul_zero] at h
    exact Filter.Tendsto.congr (fun x => mul_one_div 8 _) h
  have hsum := ((h1.add h2).add (h3.add h4))
  simpa using (tendsto_order.1 hsum).2 1 (by norm_num)

/-! ### No isolated vertices -/

theorem baseSize_le_tripleVertex_card (baseSize depth : ℕ) :
    baseSize ≤ Fintype.card (TripleVertex baseSize depth) := by
  calc
    baseSize = Fintype.card (TripleLayer baseSize 0) :=
      (tripleLayer_card_zero baseSize).symm
    _ ≤ Fintype.card (TripleVertex baseSize depth) :=
      Fintype.card_le_of_embedding (tripleLayerEmbedding baseSize depth 0 (by omega))

theorem tripleGraphOverFin_forall_exists_adj (baseSize depth : ℕ)
    (hbase : 4 ≤ baseSize) (hdepth : 0 < depth) :
    ∀ vertex : Fin (Fintype.card (TripleVertex baseSize depth)),
      ∃ neighbor, (tripleGraphOverFin baseSize depth).Adj vertex neighbor := by
  have hcard : 2 ≤ Fintype.card (TripleVertex baseSize depth) := by
    have := baseSize_le_tripleVertex_card baseSize depth
    omega
  letI : Nontrivial (Fin (Fintype.card (TripleVertex baseSize depth))) :=
    Fin.nontrivial_iff_two_le.mpr hcard
  intro vertex
  exact (tripleGraphOverFin_connected baseSize depth (by omega) hdepth).preconnected
    |>.exists_adj_of_nontrivial vertex

/-! ### From a free dense host to the extremal number -/

open Classical in
theorem eventually_expectedRetainedEdge_le_extremalNumber
    {baseSize depth : ℕ} (hbase : 4 ≤ baseSize) (hdepth : 0 < depth)
    (hhosts : ∀ᶠ dimension : ℕ in atTop,
      ∃ retained : Set (Bool × HammingWord dimension),
        (tripleGraphOverFin baseSize depth).Free
            (retainedHammingHost dimension (threeHammingRadius dimension) retained) ∧
        threeRetainedVertexCount dimension retained <
          3 * threeRetentionProbability betaThree dimension *
            ((2 ^ dimension : ℕ) : ℝ) ∧
        threeExpectedRetainedEdgeCount betaThree dimension
            (threeHammingRadius dimension) / 2 ≤
          hammingRetainedEdgeCount dimension (threeHammingRadius dimension) retained) :
    ∀ᶠ dimension : ℕ in atTop,
      threeExpectedRetainedEdgeCount betaThree dimension
          (threeHammingRadius dimension) / 2 ≤
        (SimpleGraph.extremalNumber (threeVertexCount dimension)
          (tripleGraphOverFin baseSize depth) : ℝ) := by
  filter_upwards [hhosts] with dimension hhost
  obtain ⟨retained, hfree, hvertices, hedges⟩ := hhost
  have hcard := retainedVertex_card_le_threeVertexCount dimension retained hvertices
  have hembedding : Nonempty (retained ↪ Fin (threeVertexCount dimension)) := by
    apply Function.Embedding.nonempty_of_card_le
    simpa using hcard
  obtain ⟨embedding⟩ := hembedding
  let paddedHost : SimpleGraph (Fin (threeVertexCount dimension)) :=
    (retainedHammingHost dimension (threeHammingRadius dimension) retained).map embedding
  have hpadded_free : (tripleGraphOverFin baseSize depth).Free paddedHost :=
    CompactnessConjecture.free_map_of_no_isolated
      (tripleGraphOverFin baseSize depth)
      (tripleGraphOverFin_forall_exists_adj baseSize depth hbase hdepth)
      embedding hfree
  have hpadded_edges :
      paddedHost.edgeFinset.card ≤
        SimpleGraph.extremalNumber (threeVertexCount dimension)
          (tripleGraphOverFin baseSize depth) := by
    simpa using (SimpleGraph.card_edgeFinset_le_extremalNumber hpadded_free)
  calc
    threeExpectedRetainedEdgeCount betaThree dimension
        (threeHammingRadius dimension) / 2 ≤
      hammingRetainedEdgeCount dimension (threeHammingRadius dimension) retained :=
        hedges
    _ = ((retainedHammingHost dimension (threeHammingRadius dimension)
        retained).edgeFinset.card : ℝ) :=
      hammingRetainedEdgeCount_eq_edgeFinset_card dimension
        (threeHammingRadius dimension) retained
    _ = (paddedHost.edgeFinset.card : ℝ) := by
      congr 1
      exact (SimpleGraph.card_edgeFinset_map embedding
        (retainedHammingHost dimension (threeHammingRadius dimension) retained)).symm
    _ ≤ (SimpleGraph.extremalNumber (threeVertexCount dimension)
        (tripleGraphOverFin baseSize depth) : ℝ) := by exact_mod_cast hpadded_edges

-- The final assembly, modulo the existence of a free dense retained host,
-- with the exponent gain explicit: `ε = epsThree = 1/4000`.
open Classical in
theorem threeDegenerateExtremalCounterexample_explicit_of_hosts
    {baseSize depth : ℕ} (hbase : 4 ≤ baseSize) (hdepth : 0 < depth)
    (hhosts : ∀ᶠ dimension : ℕ in atTop,
      ∃ retained : Set (Bool × HammingWord dimension),
        (tripleGraphOverFin baseSize depth).Free
            (retainedHammingHost dimension (threeHammingRadius dimension) retained) ∧
        threeRetainedVertexCount dimension retained <
          3 * threeRetentionProbability betaThree dimension *
            ((2 ^ dimension : ℕ) : ℝ) ∧
        threeExpectedRetainedEdgeCount betaThree dimension
            (threeHammingRadius dimension) / 2 ≤
          hammingRetainedEdgeCount dimension (threeHammingRadius dimension) retained) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧ H.IsBipartite ∧ IsDegenerate 3 H ∧ ¬ IsDegenerate 2 H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((5 : ℝ) / 3 + epsThree) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  classical
  set forbidden := tripleGraphOverFin baseSize depth with hforbidden
  have hnoisolated :
      ∀ vertex : Fin (Fintype.card (TripleVertex baseSize depth)),
        ∃ neighbor, forbidden.Adj vertex neighbor :=
    tripleGraphOverFin_forall_exists_adj baseSize depth hbase hdepth
  have hsubsequence :
      ∀ᶠ dimension : ℕ in atTop,
        (threeVertexCount dimension : ℝ) ^ threeExtremalPower ≤
          (SimpleGraph.extremalNumber (threeVertexCount dimension) forbidden : ℝ) := by
    filter_upwards [eventually_threeVertexCount_power_le_expectedRetainedEdge,
      eventually_expectedRetainedEdge_le_extremalNumber hbase hdepth hhosts]
      with dimension hpower hbound
    exact hpower.trans hbound
  refine ⟨Fintype.card (TripleVertex baseSize depth), forbidden,
    tripleGraphOverFin_connected baseSize depth (by omega) hdepth,
    tripleGraphOverFin_isBipartite baseSize depth,
    tripleGraphOverFin_isThreeDegenerate baseSize depth,
    tripleGraphOverFin_not_isTwoDegenerate baseSize depth hbase hdepth,
    1 / (2 : ℝ) ^ threeExtremalPower,
    one_div_pos.mpr (Real.rpow_pos_of_pos (by norm_num) threeExtremalPower),
    ?_⟩
  obtain ⟨minimum, hminimum⟩ := Filter.eventually_atTop.1 hsubsequence
  apply Filter.eventually_atTop.2
  refine ⟨threeVertexCount minimum, ?_⟩
  intro n hn
  obtain ⟨dimension, hdimension, hbelow, habove⟩ :=
    exists_threeVertexCount_bracket minimum n hn
  have hdouble := threeVertexCount_succ_le_two_mul dimension
  have hn_bound : n ≤ 2 * threeVertexCount dimension := by omega
  have hn_real : (n : ℝ) ≤ 2 * (threeVertexCount dimension : ℝ) := by
    exact_mod_cast hn_bound
  have hsubseq := hminimum dimension hdimension
  have hmonotone :
      SimpleGraph.extremalNumber (threeVertexCount dimension) forbidden ≤
        SimpleGraph.extremalNumber n forbidden :=
    CompactnessConjecture.extremalNumber_monotone_of_no_isolated
      forbidden hnoisolated hbelow
  have hpower_eq : (5 : ℝ) / 3 + epsThree = threeExtremalPower := rfl
  rw [hpower_eq]
  calc
    (1 / (2 : ℝ) ^ threeExtremalPower) * (n : ℝ) ^ threeExtremalPower ≤
      (1 / (2 : ℝ) ^ threeExtremalPower) *
        (2 * (threeVertexCount dimension : ℝ)) ^ threeExtremalPower := by
        apply mul_le_mul_of_nonneg_left
        · exact Real.rpow_le_rpow (Nat.cast_nonneg n) hn_real
            threeExtremalPower_pos.le
        · positivity
    _ = (threeVertexCount dimension : ℝ) ^ threeExtremalPower := by
        rw [Real.mul_rpow (by norm_num) (Nat.cast_nonneg (threeVertexCount dimension))]
        have htwo : (2 : ℝ) ^ threeExtremalPower ≠ 0 :=
          (Real.rpow_pos_of_pos (by norm_num) threeExtremalPower).ne'
        field_simp
    _ ≤ (SimpleGraph.extremalNumber (threeVertexCount dimension) forbidden : ℝ) :=
        hsubseq
    _ ≤ (SimpleGraph.extremalNumber n forbidden : ℝ) := by exact_mod_cast hmonotone

-- The existential-`ε` form, derived from the explicit one.
open Classical in
theorem threeDegenerateExtremalCounterexample_of_hosts
    {baseSize depth : ℕ} (hbase : 4 ≤ baseSize) (hdepth : 0 < depth)
    (hhosts : ∀ᶠ dimension : ℕ in atTop,
      ∃ retained : Set (Bool × HammingWord dimension),
        (tripleGraphOverFin baseSize depth).Free
            (retainedHammingHost dimension (threeHammingRadius dimension) retained) ∧
        threeRetainedVertexCount dimension retained <
          3 * threeRetentionProbability betaThree dimension *
            ((2 ^ dimension : ℕ) : ℝ) ∧
        threeExpectedRetainedEdgeCount betaThree dimension
            (threeHammingRadius dimension) / 2 ≤
          hammingRetainedEdgeCount dimension (threeHammingRadius dimension) retained) :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧ H.IsBipartite ∧ IsDegenerate 3 H ∧ ¬ IsDegenerate 2 H ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((5 : ℝ) / 3 + ε) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  obtain ⟨q, H, hcon, hbip, hdeg, hnodeg, c, hc0, hbnd⟩ :=
    threeDegenerateExtremalCounterexample_explicit_of_hosts hbase hdepth hhosts
  exact ⟨q, H, hcon, hbip, hdeg, hnodeg, c, epsThree, hc0, epsThree_pos, hbnd⟩

/-! ## Block F: the remaining seam — layer exclusion

Everything below `tripleGraphOverFin_free_of_exclusion` is proved.  That single
theorem is the unported part of the development: it is the `r = 3` analogue of
`TwoDegenerateGraphs.pairGraphOverFin_free_of_layer_exclusion`
(`CompactnessAndDegeneracy.lean` lines 16837–17590) together with the empirical
kernel bridge (`pairCoordinateKernel` and the `empirical*_error` family, lines
13318–14330).  See `research/results_M_lean_assembly.md`. -/

/-- The `worCorrection` error term tends to `0`. -/
theorem worCorrection_tendsto_zero :
    Tendsto (fun L : ℕ => ThreeDegenerateGraphs.worCorrection L) atTop (𝓝 0) := by
  have hinv : Tendsto (fun L : ℕ => 4 / (L : ℝ)) atTop (𝓝 0) := by
    have h := tendsto_one_div_atTop_nhds_zero_nat.const_mul (4 : ℝ)
    rw [mul_zero] at h
    exact Filter.Tendsto.congr (fun x => mul_one_div 4 _) h
  have hent : Tendsto (fun L : ℕ => binaryEntropy (4 / (L : ℝ))) atTop (𝓝 0) := by
    have hcont : Tendsto binaryEntropy (𝓝 (0 : ℝ)) (𝓝 (binaryEntropy 0)) :=
      binaryEntropy_continuous.continuousAt.tendsto
    have hzero : binaryEntropy (0 : ℝ) = 0 := by
      unfold binaryEntropy; simp
    rw [hzero] at hcont
    exact hcont.comp hinv
  have := ((hinv.add (hent.const_mul (0 : ℝ))))
  have hsum := (hinv.add (hinv.const_mul (7 / 4 : ℝ))).add (hent.div_const 2)
  simp only [mul_zero, zero_div, add_zero] at hsum
  exact hsum

theorem exists_worCorrection_base :
    ∃ L₀ : ℕ, ∀ L : ℕ, L₀ ≤ L → ThreeDegenerateGraphs.worCorrection L < slackThree :=
  Filter.eventually_atTop.1
    ((tendsto_order.1 worCorrection_tendsto_zero).2 slackThree slackThree_pos)

/-! ### The layered copy machinery -/

section Copy

variable {baseSize depth dimension radius : ℕ}

theorem tripleGraphCopy_layer_side_eq
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (tripleParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (hbase : 4 ≤ baseSize)
    (layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (first second : TripleLayer baseSize layer) :
    (copy (tripleLayerEmbedding baseSize depth layer (by omega) first)).val.1 =
    (copy (tripleLayerEmbedding baseSize depth layer (by omega) second)).val.1 := by
  classical
  by_cases hequal : first = second
  · subst second; rfl
  · -- choose a third element to complete `{first, second}` to a triple
    letI : DecidableEq (TripleLayer baseSize layer) := Classical.decEq _
    have hcard : ({first, second} : Finset (TripleLayer baseSize layer)).card ≤ 3 := by
      rw [Finset.card_pair hequal]; omega
    have huniv : (3 : ℕ) ≤
        (Finset.univ : Finset (TripleLayer baseSize layer)).card := by
      have hge := tripleLayer_card_ge_base baseSize layer hbase
      rw [Finset.card_univ]
      omega
    obtain ⟨c, hsub, -, hc3⟩ :=
      Finset.exists_subsuperset_card_eq (Finset.subset_univ
        ({first, second} : Finset (TripleLayer baseSize layer))) hcard huniv
    have hfirst_mem : first ∈ c := hsub (Finset.mem_insert_self _ _)
    have hsecond_mem : second ∈ c :=
      hsub (Finset.mem_insert_of_mem (Finset.mem_singleton_self _))
    let bridge : TripleLayer baseSize (layer + 1) := ⟨c, hc3⟩
    have hfirst_source := tripleGraph_parent_child_adj baseSize depth layer
      hlayer bridge first hfirst_mem
    have hsecond_source := tripleGraph_parent_child_adj baseSize depth layer
      hlayer bridge second hsecond_mem
    have hfirst_edge := copy.toHom.map_rel hfirst_source
    have hsecond_edge := copy.toHom.map_rel hsecond_source
    change (hammingHost dimension radius).Adj
      (copy (tripleLayerEmbedding baseSize depth (layer + 1) hlayer bridge)).val
      (copy (tripleLayerEmbedding baseSize depth layer (by omega) first)).val
      at hfirst_edge
    change (hammingHost dimension radius).Adj
      (copy (tripleLayerEmbedding baseSize depth (layer + 1) hlayer bridge)).val
      (copy (tripleLayerEmbedding baseSize depth layer (by omega) second)).val
      at hsecond_edge
    have hfirst_side := (hammingHost_adj_iff dimension radius _ _).mp hfirst_edge
    have hsecond_side := (hammingHost_adj_iff dimension radius _ _).mp hsecond_edge
    cases hbridge :
      (copy (tripleLayerEmbedding baseSize depth (layer + 1)
        hlayer bridge)).val.1 <;>
      cases hf :
        (copy (tripleLayerEmbedding baseSize depth layer (by omega) first)).val.1 <;>
      cases hs :
        (copy (tripleLayerEmbedding baseSize depth layer (by omega) second)).val.1 <;>
      simp_all

theorem tripleGraphCopy_child_layer_side_eq
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (tripleParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (hbase : 4 ≤ baseSize)
    (layer : ℕ)
    (hlayer : layer + 1 < depth + 1)
    (first second : TripleLayer baseSize (layer + 1)) :
    (copy (tripleLayerEmbedding baseSize depth (layer + 1) hlayer first)).val.1 =
    (copy (tripleLayerEmbedding baseSize depth (layer + 1) hlayer second)).val.1 := by
  classical
  have hfirst_nonempty : first.val.Nonempty := by
    apply Finset.card_pos.mp; rw [first.property]; norm_num
  have hsecond_nonempty : second.val.Nonempty := by
    apply Finset.card_pos.mp; rw [second.property]; norm_num
  obtain ⟨firstParent, hfirstParent⟩ := hfirst_nonempty
  obtain ⟨secondParent, hsecondParent⟩ := hsecond_nonempty
  have hparent_side := tripleGraphCopy_layer_side_eq retained copy hbase layer
    hlayer firstParent secondParent
  have hfirst_edge := copy.toHom.map_rel
    (tripleGraph_parent_child_adj baseSize depth layer hlayer first
      firstParent hfirstParent)
  have hsecond_edge := copy.toHom.map_rel
    (tripleGraph_parent_child_adj baseSize depth layer hlayer second
      secondParent hsecondParent)
  change (hammingHost dimension radius).Adj
    (copy (tripleLayerEmbedding baseSize depth (layer + 1) hlayer first)).val
    (copy (tripleLayerEmbedding baseSize depth layer (by omega) firstParent)).val
    at hfirst_edge
  change (hammingHost dimension radius).Adj
    (copy (tripleLayerEmbedding baseSize depth (layer + 1) hlayer second)).val
    (copy (tripleLayerEmbedding baseSize depth layer (by omega) secondParent)).val
    at hsecond_edge
  have hfirst_side := (hammingHost_adj_iff dimension radius _ _).mp hfirst_edge
  have hsecond_side := (hammingHost_adj_iff dimension radius _ _).mp hsecond_edge
  cases hf :
    (copy (tripleLayerEmbedding baseSize depth (layer + 1) hlayer first)).val.1 <;>
    cases hs :
      (copy (tripleLayerEmbedding baseSize depth (layer + 1) hlayer second)).val.1 <;>
    cases hfp :
      (copy (tripleLayerEmbedding baseSize depth layer
        (by omega) firstParent)).val.1 <;>
    cases hsp :
      (copy (tripleLayerEmbedding baseSize depth layer
        (by omega) secondParent)).val.1 <;>
    simp_all

noncomputable def tripleGraphCopyParentWords
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (tripleParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    Fin (Fintype.card (TripleLayer baseSize layer.val)) →
      HammingWord dimension :=
  fun parent =>
    (copy (tripleLayerEmbedding baseSize depth layer.val (by omega)
      ((tripleLayerFinEquiv baseSize layer.val).symm parent))).val.2

noncomputable def tripleGraphCopyChildWords
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (tripleParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    TripleLayer (Fintype.card (TripleLayer baseSize layer.val)) 1 →
      HammingWord dimension :=
  fun triple =>
    (copy (tripleLayerEmbedding baseSize depth (layer.val + 1) (by omega)
      ((tripleLayerTripleEquiv baseSize layer.val) triple))).val.2

noncomputable def tripleGraphCopyChildSide
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (tripleParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (reference :
      TripleLayer (Fintype.card (TripleLayer baseSize layer.val)) 1) : Bool :=
  (copy (tripleLayerEmbedding baseSize depth (layer.val + 1) (by omega)
    ((tripleLayerTripleEquiv baseSize layer.val) reference))).val.1

noncomputable def tripleGraphCopyLayerPotential
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (tripleParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin (depth + 1)) : ℝ :=
  (∑ coordinate : Fin dimension,
    binaryEntropy
      (((booleanWordOnes
        (fun vertex : TripleLayer baseSize layer.val =>
          (copy (tripleLayerEmbedding baseSize depth layer.val layer.isLt
            vertex)).val.2 coordinate)).card : ℝ) /
        (Fintype.card (TripleLayer baseSize layer.val) : ℝ))) /
    (dimension : ℝ)

theorem tripleGraphCopy_parentPotential_eq
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (tripleParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    ThreeBridge.tripleParentArrayEntropyPotential
        (tripleGraphCopyParentWords retained copy layer) =
      tripleGraphCopyLayerPotential retained copy ⟨layer.val, by omega⟩ := by
  unfold ThreeBridge.tripleParentArrayEntropyPotential
    tripleGraphCopyLayerPotential
  apply congrArg (fun numerator : ℝ => numerator / (dimension : ℝ))
  apply Finset.sum_congr rfl
  intro coordinate _
  unfold pairParentCoordinateOneCount tripleGraphCopyParentWords
  rw [booleanWordOnes_card_equiv
    (tripleLayerFinEquiv baseSize layer.val).symm
    (fun vertex : TripleLayer baseSize layer.val =>
      (copy (tripleLayerEmbedding baseSize depth layer.val (by omega)
        vertex)).val.2 coordinate)]

theorem tripleGraphCopy_childPotential_eq
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (tripleParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    ThreeBridge.tripleChildArrayEntropyPotential
        (tripleGraphCopyChildWords retained copy layer) =
      tripleGraphCopyLayerPotential retained copy ⟨layer.val + 1, by omega⟩ := by
  unfold ThreeBridge.tripleChildArrayEntropyPotential
    tripleGraphCopyLayerPotential
  apply congrArg (fun numerator : ℝ => numerator / (dimension : ℝ))
  apply Finset.sum_congr rfl
  intro coordinate _
  unfold ThreeBridge.tripleChildCoordinateOneCount tripleGraphCopyChildWords
  rw [booleanWordOnes_card_equiv
    (tripleLayerTripleEquiv baseSize layer.val)
    (fun vertex : TripleLayer baseSize (layer.val + 1) =>
      (copy (tripleLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        vertex)).val.2 coordinate)]
  rw [tripleLayer_card_succ]

theorem tripleGraphCopyLayerPotential_mem_Icc
    (hbase : 4 ≤ baseSize) (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (tripleParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin (depth + 1)) :
    0 ≤ tripleGraphCopyLayerPotential retained copy layer ∧
      tripleGraphCopyLayerPotential retained copy layer ≤ 1 := by
  classical
  have hlayer : 0 < Fintype.card (TripleLayer baseSize layer.val) := by
    have hcard := tripleLayer_card_ge_base baseSize layer.val hbase
    omega
  have hlayer_real : (0 : ℝ) < (Fintype.card (TripleLayer baseSize layer.val) : ℝ) := by
    exact_mod_cast hlayer
  have hdimension_real : (0 : ℝ) < (dimension : ℝ) := by exact_mod_cast hdimension
  have hterm (coordinate : Fin dimension) :
      0 ≤ binaryEntropy
          (((booleanWordOnes
            (fun vertex : TripleLayer baseSize layer.val =>
              (copy (tripleLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val.2 coordinate)).card : ℝ) /
            (Fintype.card (TripleLayer baseSize layer.val) : ℝ)) ∧
      binaryEntropy
          (((booleanWordOnes
            (fun vertex : TripleLayer baseSize layer.val =>
              (copy (tripleLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val.2 coordinate)).card : ℝ) /
            (Fintype.card (TripleLayer baseSize layer.val) : ℝ)) ≤ 1 := by
    have hcount :
        (booleanWordOnes
          (fun vertex : TripleLayer baseSize layer.val =>
            (copy (tripleLayerEmbedding baseSize depth layer.val layer.isLt
              vertex)).val.2 coordinate)).card ≤
          Fintype.card (TripleLayer baseSize layer.val) := by
      unfold booleanWordOnes
      simpa using
        (Finset.card_filter_le
          (Finset.univ : Finset (TripleLayer baseSize layer.val))
          (fun vertex =>
            (copy (tripleLayerEmbedding baseSize depth layer.val layer.isLt
              vertex)).val.2 coordinate = true))
    have hzero : 0 ≤
        ((booleanWordOnes
          (fun vertex : TripleLayer baseSize layer.val =>
            (copy (tripleLayerEmbedding baseSize depth layer.val layer.isLt
              vertex)).val.2 coordinate)).card : ℝ) /
          (Fintype.card (TripleLayer baseSize layer.val) : ℝ) := by positivity
    have hone :
        ((booleanWordOnes
          (fun vertex : TripleLayer baseSize layer.val =>
            (copy (tripleLayerEmbedding baseSize depth layer.val layer.isLt
              vertex)).val.2 coordinate)).card : ℝ) /
          (Fintype.card (TripleLayer baseSize layer.val) : ℝ) ≤ 1 := by
      apply (div_le_one hlayer_real).mpr
      exact_mod_cast hcount
    exact ⟨binaryEntropy_nonneg hzero hone, binaryEntropy_le_one _⟩
  unfold tripleGraphCopyLayerPotential
  constructor
  · exact div_nonneg (Finset.sum_nonneg fun coordinate _ => (hterm coordinate).1)
      hdimension_real.le
  · apply (div_le_one hdimension_real).mpr
    calc (∑ coordinate : Fin dimension,
        binaryEntropy
          (((booleanWordOnes
            (fun vertex : TripleLayer baseSize layer.val =>
              (copy (tripleLayerEmbedding baseSize depth layer.val layer.isLt
                vertex)).val.2 coordinate)).card : ℝ) /
            (Fintype.card (TripleLayer baseSize layer.val) : ℝ))) ≤
        ∑ _coordinate : Fin dimension, (1 : ℝ) :=
          Finset.sum_le_sum fun coordinate _ => (hterm coordinate).2
      _ = (dimension : ℝ) := by simp

theorem tripleGraphCopyChildWords_injective
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (tripleParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (hbase : 4 ≤ baseSize)
    (layer : Fin depth) :
    Function.Injective (tripleGraphCopyChildWords retained copy layer) := by
  intro first second hwords
  have hside := tripleGraphCopy_child_layer_side_eq retained copy hbase
    layer.val (by omega)
    ((tripleLayerTripleEquiv baseSize layer.val) first)
    ((tripleLayerTripleEquiv baseSize layer.val) second)
  have hvertices :
      (copy (tripleLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        ((tripleLayerTripleEquiv baseSize layer.val) first))).val =
      (copy (tripleLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        ((tripleLayerTripleEquiv baseSize layer.val) second))).val :=
    Prod.ext hside hwords
  have himages :
      copy (tripleLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        ((tripleLayerTripleEquiv baseSize layer.val) first)) =
      copy (tripleLayerEmbedding baseSize depth (layer.val + 1) (by omega)
        ((tripleLayerTripleEquiv baseSize layer.val) second)) :=
    Subtype.ext hvertices
  have hsources := copy.injective himages
  have htriples :=
    (tripleLayerEmbedding baseSize depth (layer.val + 1) (by omega)).injective
      hsources
  exact (tripleLayerTripleEquiv baseSize layer.val).injective htriples

theorem tripleGraphCopyChildWords_retained
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (tripleParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (hbase : 4 ≤ baseSize)
    (layer : Fin depth)
    (reference :
      TripleLayer (Fintype.card (TripleLayer baseSize layer.val)) 1) :
    retained ∈
      tripleChildRetentionEvent
        (tripleGraphCopyChildSide retained copy layer reference)
        (tripleGraphCopyChildWords retained copy layer) := by
  intro triple
  have hside := tripleGraphCopy_child_layer_side_eq retained copy hbase
    layer.val (by omega)
    ((tripleLayerTripleEquiv baseSize layer.val) reference)
    ((tripleLayerTripleEquiv baseSize layer.val) triple)
  have hretained :=
    (copy (tripleLayerEmbedding baseSize depth (layer.val + 1) (by omega)
      ((tripleLayerTripleEquiv baseSize layer.val) triple))).property
  change
    (tripleGraphCopyChildSide retained copy layer reference,
      tripleGraphCopyChildWords retained copy layer triple) ∈ retained
  unfold tripleGraphCopyChildSide tripleGraphCopyChildWords
  rw [hside]
  exact hretained

theorem tripleGraphCopy_parent_child_hammingDist_le
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (tripleParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (triple : TripleLayer (Fintype.card (TripleLayer baseSize layer.val)) 1)
    (parent : TripleLayer (Fintype.card (TripleLayer baseSize layer.val)) 0)
    (hparent : parent ∈ triple.val) :
    hammingDist
      (tripleGraphCopyParentWords retained copy layer parent)
      (tripleGraphCopyChildWords retained copy layer triple) ≤ radius := by
  have hactualParent :
      (tripleLayerFinEquiv baseSize layer.val).symm parent ∈
        ((tripleLayerTripleEquiv baseSize layer.val) triple).val := by
    change (tripleLayerFinEquiv baseSize layer.val).symm parent ∈
      triple.val.map (tripleLayerFinEquiv baseSize layer.val).symm.toEmbedding
    exact Finset.mem_map.mpr ⟨parent, hparent, rfl⟩
  have hsource := tripleGraph_parent_child_adj baseSize depth layer.val
    (by omega) ((tripleLayerTripleEquiv baseSize layer.val) triple)
    ((tripleLayerFinEquiv baseSize layer.val).symm parent) hactualParent
  have hedge := copy.toHom.map_rel hsource
  change (hammingHost dimension radius).Adj
    (copy (tripleLayerEmbedding baseSize depth (layer.val + 1) (by omega)
      ((tripleLayerTripleEquiv baseSize layer.val) triple))).val
    (copy (tripleLayerEmbedding baseSize depth layer.val (by omega)
      ((tripleLayerFinEquiv baseSize layer.val).symm parent))).val at hedge
  have hdist := ((hammingHost_adj_iff dimension radius _ _).mp hedge).2
  simpa [tripleGraphCopyParentWords, tripleGraphCopyChildWords,
    hammingDist_comm] using hdist

theorem tripleGraphCopy_averageDisagreement_le_tau
    (hbase : 4 ≤ baseSize) (hdimension : 0 < dimension)
    (hradius : (radius : ℝ) ≤ tauThree * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (tripleParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth) :
    ThreeBridge.tripleChildArrayAverageDisagreement
      (tripleGraphCopyParentWords retained copy layer)
      (tripleGraphCopyChildWords retained copy layer) ≤ tauThree := by
  have hdimension_real : (0 : ℝ) < (dimension : ℝ) := by exact_mod_cast hdimension
  have hparents : 3 ≤ Fintype.card (TripleLayer baseSize layer.val) := by
    have := tripleLayer_card_ge_base baseSize layer.val hbase
    omega
  refine le_trans
    (ThreeBridge.tripleChildArrayAverageDisagreement_le_radius hparents
      hdimension _ _ radius
      (fun triple parent hparent =>
        tripleGraphCopy_parent_child_hammingDist_le retained copy layer
          triple parent hparent))
    ((div_le_iff₀ hdimension_real).mpr hradius)

theorem tripleGraphCopy_entropy_lower_of_exclusion
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (tripleParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (hbase : 4 ≤ baseSize)
    (layer : Fin depth)
    (reference :
      TripleLayer (Fintype.card (TripleLayer baseSize layer.val)) 1)
    (threshold : ℝ)
    (hexclusion :
      retained ∉
        badTripleLayerRetentionEvent
          (Fintype.card (TripleLayer baseSize layer.val)) dimension
          (tripleGraphCopyChildSide retained copy layer reference)
          threshold) :
    threshold <
      tripleChildArrayEntropy
        (tripleGraphCopyParentWords retained copy layer)
        (tripleGraphCopyChildWords retained copy layer) := by
  classical
  by_contra hnot
  have hbad_entropy :
      tripleChildArrayEntropy
        (tripleGraphCopyParentWords retained copy layer)
        (tripleGraphCopyChildWords retained copy layer) ≤ threshold :=
    le_of_not_gt hnot
  have hbad_array :
      tripleGraphCopyChildWords retained copy layer ∈
        badTripleChildArrays
          (tripleGraphCopyParentWords retained copy layer) threshold := by
    unfold badTripleChildArrays
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _, hbad_entropy⟩
  have hinjective :
      tripleGraphCopyChildWords retained copy layer ∈
        (badTripleChildArrays
          (tripleGraphCopyParentWords retained copy layer) threshold).filter
            Function.Injective :=
    Finset.mem_filter.mpr
      ⟨hbad_array, tripleGraphCopyChildWords_injective retained copy hbase layer⟩
  apply hexclusion
  change retained ∈
    ⋃ parents :
        Fin (Fintype.card (TripleLayer baseSize layer.val)) →
          HammingWord dimension,
      badTripleChildRetentionEvent parents
        (tripleGraphCopyChildSide retained copy layer reference) threshold
  apply Set.mem_iUnion.mpr
  refine ⟨tripleGraphCopyParentWords retained copy layer, ?_⟩
  change retained ∈
    ⋃ children ∈
        (badTripleChildArrays
          (tripleGraphCopyParentWords retained copy layer) threshold).filter
            Function.Injective,
      tripleChildRetentionEvent
        (tripleGraphCopyChildSide retained copy layer reference) children
  exact Set.mem_iUnion.mpr
    ⟨tripleGraphCopyChildWords retained copy layer,
      Set.mem_iUnion.mpr
        ⟨hinjective,
          tripleGraphCopyChildWords_retained retained copy hbase layer reference⟩⟩

theorem tripleGraphCopy_layer_entropy_upper
    (hbase : 10 ≤ baseSize) (hdimension : 0 < dimension)
    (retained : Set (Bool × HammingWord dimension))
    (copy : SimpleGraph.Copy
      (tripleParentSystem baseSize depth).graph
      (retainedHammingHost dimension radius retained))
    (layer : Fin depth)
    (hdis : ThreeBridge.tripleChildArrayAverageDisagreement
        (tripleGraphCopyParentWords retained copy layer)
        (tripleGraphCopyChildWords retained copy layer) ≤ tauThree) :
    tripleChildArrayEntropy
        (tripleGraphCopyParentWords retained copy layer)
        (tripleGraphCopyChildWords retained copy layer) ≤
      entropyLowerEndpointThree +
        (tripleGraphCopyLayerPotential retained copy ⟨layer.val + 1, by omega⟩ -
          tripleGraphCopyLayerPotential retained copy ⟨layer.val, by omega⟩) / 2 +
        ThreeDegenerateGraphs.worCorrection
          (Fintype.card (TripleLayer baseSize layer.val)) := by
  have hcard : 10 ≤ Fintype.card (TripleLayer baseSize layer.val) := by
    have hge := tripleLayer_card_ge_base baseSize layer.val (by omega)
    omega
  have hbound := ThreeBridge.tripleChildArrayEntropy_empirical_bound hcard
    hdimension
    (tripleGraphCopyParentWords retained copy layer)
    (tripleGraphCopyChildWords retained copy layer)
  rw [tripleGraphCopy_childPotential_eq retained copy layer,
    tripleGraphCopy_parentPotential_eq retained copy layer] at hbound
  unfold entropyLowerEndpointThree
  unfold tauThree at hdis
  linarith

theorem tripleGraph_free_of_layer_exclusion
    (hbase : 10 ≤ baseSize) (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * potentialIncrementThree)
    (hradius : (radius : ℝ) ≤ tauThree * (dimension : ℝ))
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion : ∀ (side : Bool) (layer : Fin depth),
      retained ∉ badTripleLayerRetentionEvent
        (Fintype.card (TripleLayer baseSize layer.val)) dimension side
        (((betaThree : NNReal) : ℝ) - slackThree))
    (herror : ∀ layer : Fin depth,
      ThreeDegenerateGraphs.worCorrection
        (Fintype.card (TripleLayer baseSize layer.val)) < slackThree) :
    (tripleParentSystem baseSize depth).graph.Free
      (retainedHammingHost dimension radius retained) := by
  classical
  intro hcontained
  obtain ⟨copy⟩ := hcontained
  set potential : ℕ → ℝ := fun level =>
    if hlevel : level < depth + 1 then
      tripleGraphCopyLayerPotential retained copy ⟨level, hlevel⟩ else 0
    with hpotential
  apply potential_layers_impossible depth potential potentialIncrementThree
  · intro level hlevel
    have hinrange : level < depth + 1 := by omega
    simpa [hpotential, hinrange, show level ≤ depth from by omega] using
      tripleGraphCopyLayerPotential_mem_Icc (by omega) hdimension retained copy
        ⟨level, hinrange⟩
  · intro level hlevel
    have hnext : level + 1 < depth + 1 := by omega
    have hcurrent : level < depth + 1 := by omega
    have hsize : 3 ≤ Fintype.card (TripleLayer baseSize level) := by
      have hge := tripleLayer_card_ge_base baseSize level (by omega)
      omega
    let reference : TripleLayer (Fintype.card (TripleLayer baseSize level)) 1 :=
      Classical.choice (tripleLayerTriple_nonempty hsize)
    have hlower := tripleGraphCopy_entropy_lower_of_exclusion retained copy
      (by omega) ⟨level, hlevel⟩ reference
      (((betaThree : NNReal) : ℝ) - slackThree)
      (hexclusion
        (tripleGraphCopyChildSide retained copy ⟨level, hlevel⟩ reference)
        ⟨level, hlevel⟩)
    have hupper := tripleGraphCopy_layer_entropy_upper hbase hdimension retained
      copy ⟨level, hlevel⟩
      (tripleGraphCopy_averageDisagreement_le_tau (by omega) hdimension hradius
        retained copy ⟨level, hlevel⟩)
    have hincrement := potential_increment_three
      (tripleGraphCopyLayerPotential retained copy ⟨level, hcurrent⟩)
      (tripleGraphCopyLayerPotential retained copy ⟨level + 1, hnext⟩)
      (tripleChildArrayEntropy
        (tripleGraphCopyParentWords retained copy ⟨level, hlevel⟩)
        (tripleGraphCopyChildWords retained copy ⟨level, hlevel⟩))
      (ThreeDegenerateGraphs.worCorrection
        (Fintype.card (TripleLayer baseSize level)))
      (herror ⟨level, hlevel⟩) hlower hupper
    simpa [hpotential, hnext, hcurrent, hlevel,
      show level ≤ depth from by omega] using hincrement
  · exact hdepth

end Copy

/-- **The exclusion step.**  A retained host that avoids every bad
layer-retention event contains no copy of the layered triple graph. -/
theorem tripleGraphOverFin_free_of_exclusion
    {baseSize depth dimension : ℕ}
    (hbase : 10 ≤ baseSize) (hdimension : 0 < dimension)
    (hdepth : 1 < (depth : ℝ) * potentialIncrementThree)
    (herror : ∀ layer : Fin depth,
      ThreeDegenerateGraphs.worCorrection
        (Fintype.card (TripleLayer baseSize layer.val)) < slackThree)
    (retained : Set (Bool × HammingWord dimension))
    (hexclusion : retained ∉
      badTripleLayersRetentionEvent betaThree slackThree
        (fun layer : Fin depth => Fintype.card (TripleLayer baseSize layer.val))
        dimension) :
    (tripleGraphOverFin baseSize depth).Free
      (retainedHammingHost dimension (threeHammingRadius dimension) retained) := by
  refine (SimpleGraph.free_congr_left (tripleGraphOverFinIso baseSize depth)).mp ?_
  refine tripleGraph_free_of_layer_exclusion hbase hdimension hdepth
    (threeHammingRadius_le dimension) retained ?_ herror
  intro side layer hmem
  exact hexclusion (Set.mem_iUnion.mpr ⟨side, Set.mem_iUnion.mpr ⟨layer, hmem⟩⟩)

/-! ## Block G: the counterexample -/

theorem exists_free_dense_hosts :
    ∃ baseSize depth : ℕ, 4 ≤ baseSize ∧ 0 < depth ∧
      ∀ᶠ dimension : ℕ in atTop,
        ∃ retained : Set (Bool × HammingWord dimension),
          (tripleGraphOverFin baseSize depth).Free
              (retainedHammingHost dimension (threeHammingRadius dimension) retained) ∧
          threeRetainedVertexCount dimension retained <
            3 * threeRetentionProbability betaThree dimension *
              ((2 ^ dimension : ℕ) : ℝ) ∧
          threeExpectedRetainedEdgeCount betaThree dimension
              (threeHammingRadius dimension) / 2 ≤
            hammingRetainedEdgeCount dimension (threeHammingRadius dimension)
              retained := by
  obtain ⟨Lerr, hLerr⟩ := exists_worCorrection_base
  refine ⟨max baseSizeThree Lerr, depthThree, ?_, ?_, ?_⟩
  · have : (10 : ℕ) ^ 7 ≤ max baseSizeThree Lerr := le_max_left _ _
    omega
  · unfold depthThree; omega
  set baseSize := max baseSizeThree Lerr with hbaseSize
  have hbase4 : 10 ≤ baseSize := by
    have : baseSizeThree ≤ baseSize := le_max_left _ _
    unfold baseSizeThree at this; omega
  set layerSizes : Fin depthThree → ℕ :=
    fun layer => Fintype.card (TripleLayer baseSize layer.val) with hlayerSizes
  have hcard_ge : ∀ layer : Fin depthThree, baseSize ≤ layerSizes layer :=
    fun layer => tripleLayer_card_ge_base baseSize layer.val (by omega)
  have hparents : ∀ layer, 4 ≤ layerSizes layer :=
    fun layer => le_trans (by omega) (hcard_ge layer)
  have hcount : ∀ layer,
      (layerSizes layer : ℝ) +
        4 * logTwo (((layerSizes layer).choose 3 + 1 : ℕ) : ℝ) -
          slackThree * ((layerSizes layer).choose 3 : ℝ) < -1 := by
    intro layer
    refine counting_hypothesis_of_large _ ?_
    exact le_trans (le_max_left _ _) (hcard_ge layer)
  have herror : ∀ layer : Fin depthThree,
      ThreeDegenerateGraphs.worCorrection (layerSizes layer) < slackThree := by
    intro layer
    exact hLerr _ (le_trans (le_max_right _ _) (hcard_ge layer))
  filter_upwards [eventually_budget depthThree, Filter.eventually_gt_atTop 0]
    with dimension hbudget hdimension
  obtain ⟨retained, hout, hvert, hedge⟩ :=
    exists_good_retention betaThree slackThree layerSizes
      (threeHammingRadius dimension) hdimension hparents hcount hbudget
  exact ⟨retained,
    tripleGraphOverFin_free_of_exclusion hbase4 hdimension
      depthThree_increment herror retained hout,
    hvert, hedge⟩

open Classical in
theorem threeDegenerateExtremalCounterexample :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsDegenerate 3 H ∧
      ¬ IsDegenerate 2 H ∧
      ∃ c ε : ℝ, 0 < c ∧ 0 < ε ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((5 : ℝ) / 3 + ε) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  obtain ⟨baseSize, depth, hbase, hdepth, hhosts⟩ := exists_free_dense_hosts
  exact threeDegenerateExtremalCounterexample_of_hosts hbase hdepth hhosts

-- **Theorem 1 with the explicit exponent** `5/3 + 1/4000`.
open Classical in
theorem threeDegenerateExtremalCounterexample_explicit :
    ∃ (q : ℕ) (H : SimpleGraph (Fin q)),
      H.Connected ∧
      H.IsBipartite ∧
      IsDegenerate 3 H ∧
      ¬ IsDegenerate 2 H ∧
      ∃ c : ℝ, 0 < c ∧
        ∀ᶠ n : ℕ in atTop,
          c * (n : ℝ) ^ ((5 : ℝ) / 3 + 1 / 4000) ≤
            (SimpleGraph.extremalNumber n H : ℝ) := by
  obtain ⟨baseSize, depth, hbase, hdepth, hhosts⟩ := exists_free_dense_hosts
  exact threeDegenerateExtremalCounterexample_explicit_of_hosts hbase hdepth hhosts

end ThreeAssembly
