import CompactnessAndDegeneracy

/-!
# Exact degeneracy: generic lower-bound machinery

`TwoDegenerateGraphs.IsDegenerate r` is only an upper bound (degeneracy at
most `r`).  This file supplies the generic tools for the matching lower
bound `¬ IsDegenerate (r - 1)`:

* `not_isDegenerate_of_witness` — a finite set in which every vertex has
  more than `k` neighbors refutes `k`-degeneracy;
* `isDegenerate_of_iso` — degeneracy transports across graph isomorphisms
  (at any index, so its contrapositive transports the refutation too);
* `not_isDegenerate_of_layer_witness` — the layered-construction witness:
  if a graph contains a copy of the "roots and `r`-subsets" bipartite
  pattern over a base of at least `r + 1` roots, it is not
  `(r-1)`-degenerate.  Every layer-1 child keeps its `r` root parents, and
  every root lies in `C(base − 1, r − 1) ≥ C(r, r − 1) = r` children, so
  the union of the two layers has minimum degree `≥ r` inside itself.

`proofs/scratch/Assembly3.lean` (the triple graph) and `proofs/lib/AssemblyR.lean` (the general
layered `r`-graph) instantiate the witness with their bottom two layers.
-/

namespace ExactDegeneracy

open Finset TwoDegenerateGraphs

variable {V L : Type*}

/-- A finite set in which every vertex has more than `k` neighbors refutes
`k`-degeneracy. -/
theorem not_isDegenerate_of_witness {k : ℕ} {G : SimpleGraph V}
    (s : Finset V) (hs : s.Nonempty)
    (hmin : ∀ v ∈ s, k < (neighborsWithin G s v).card) :
    ¬ IsDegenerate k G := by
  intro h
  obtain ⟨v, hv, hcard⟩ := h s hs
  exact absurd hcard (not_le.mpr (hmin v hv))

/-- Degeneracy (at any index `k`) transports across graph isomorphisms. -/
theorem isDegenerate_of_iso {W : Type*} {k : ℕ}
    {G : SimpleGraph V} {H : SimpleGraph W}
    (e : G ≃g H) (hG : IsDegenerate k G) : IsDegenerate k H := by
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
        neighborsWithin H s (e v) =
          (neighborsWithin G t v).map e.toEquiv.toEmbedding := by
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

/-- **The two-layer witness.**  Suppose `G` contains a vertex `e0 a` for
every root `a : L` and a vertex `e1 c` for every `r`-subset `c` of the
roots, with each child adjacent to each of its `r` roots.  If there are at
least `r + 1` roots, then `G` is not `(r-1)`-degenerate. -/
theorem not_isDegenerate_of_layer_witness [Fintype L] [DecidableEq L]
    {r : ℕ} {G : SimpleGraph V} (hr : 1 ≤ r)
    (hcard : r + 1 ≤ Fintype.card L)
    (e0 : L ↪ V) (e1 : {P : Finset L // P.card = r} ↪ V)
    (hadj : ∀ (a : L) (c : {P : Finset L // P.card = r}),
      a ∈ c.val → G.Adj (e0 a) (e1 c)) :
    ¬ IsDegenerate (r - 1) G := by
  classical
  set s : Finset V := Finset.univ.map e0 ∪ Finset.univ.map e1 with hs_def
  apply not_isDegenerate_of_witness s
  · -- `s` is nonempty: there are `≥ r + 1 > 0` roots
    refine Finset.Nonempty.mono Finset.subset_union_left ?_
    rw [← Finset.card_pos, Finset.card_map, Finset.card_univ]
    omega
  · rintro v hv
    rcases Finset.mem_union.mp hv with hv0 | hv1
    · -- `v = e0 a` is a root: the children `insert a T` for
      -- `T ∈ powersetCard (r-1) (univ.erase a)` give
      -- `C(card L - 1, r-1) ≥ C(r, r-1) = r` neighbors within `s`
      obtain ⟨a, -, rfl⟩ := Finset.mem_map.mp hv0
      set pc : Finset (Finset L) :=
        (Finset.univ.erase a).powersetCard (r - 1) with hpc_def
      have hmem_pc : ∀ T ∈ pc, a ∉ T ∧ T.card = r - 1 := by
        intro T hT
        obtain ⟨hsub, hcardT⟩ := Finset.mem_powersetCard.mp hT
        exact ⟨fun h => (Finset.mem_erase.mp (hsub h)).1 rfl, hcardT⟩
      have hinsert_card : ∀ T ∈ pc, (insert a T).card = r := by
        intro T hT
        obtain ⟨haT, hcardT⟩ := hmem_pc T hT
        rw [Finset.card_insert_of_notMem haT, hcardT]
        omega
      have hle : pc.card ≤ (neighborsWithin G s (e0 a)).card := by
        rw [← Finset.card_attach (s := pc)]
        apply Finset.card_le_card_of_injOn
          (fun T => e1 ⟨insert a T.val, hinsert_card T.val T.property⟩)
        · intro T hT
          have hmem : e1 ⟨insert a T.val, hinsert_card T.val T.property⟩ ∈ s ∧
              G.Adj (e0 a)
                (e1 ⟨insert a T.val, hinsert_card T.val T.property⟩) :=
            ⟨Finset.mem_union_right _
              (Finset.mem_map_of_mem e1 (Finset.mem_univ _)),
             hadj a _ (Finset.mem_insert_self a T.val)⟩
          simpa [neighborsWithin] using hmem
        · intro T hT T' hT' heq
          have hval : insert a T.val = insert a T'.val := by
            have := e1.injective heq
            exact congrArg Subtype.val this
          have haT := (hmem_pc T.val T.property).1
          have haT' := (hmem_pc T'.val T'.property).1
          have : T.val = T'.val := by
            rw [← Finset.erase_insert haT, ← Finset.erase_insert haT', hval]
          exact Subtype.ext this
      have hpc_card : pc.card = (Fintype.card L - 1).choose (r - 1) := by
        rw [hpc_def, Finset.card_powersetCard,
          Finset.card_erase_of_mem (Finset.mem_univ a), Finset.card_univ]
      have hchoose : r ≤ (Fintype.card L - 1).choose (r - 1) := by
        calc r = ((r - 1) + 1).choose (r - 1) := by
              rw [Nat.choose_succ_self_right]; omega
          _ ≤ (Fintype.card L - 1).choose (r - 1) :=
              Nat.choose_le_choose _ (by omega)
      omega
    · -- `v = e1 c` is a child: its `r` roots are neighbors within `s`
      obtain ⟨c, -, rfl⟩ := Finset.mem_map.mp hv1
      have hsub : c.val.map e0 ⊆ neighborsWithin G s (e1 c) := by
        intro p hp
        obtain ⟨w, hw, rfl⟩ := Finset.mem_map.mp hp
        have hmem : e0 w ∈ s ∧ G.Adj (e1 c) (e0 w) :=
          ⟨Finset.mem_union_left _
            (Finset.mem_map_of_mem e0 (Finset.mem_univ _)),
           (hadj w c hw).symm⟩
        simpa [neighborsWithin] using hmem
      have hcard : (c.val.map e0).card = r := by
        rw [Finset.card_map]
        exact c.property
      have := Finset.card_le_card hsub
      omega

end ExactDegeneracy
