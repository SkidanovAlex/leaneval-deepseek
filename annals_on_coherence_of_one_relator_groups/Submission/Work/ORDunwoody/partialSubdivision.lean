/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# The partial subdivision of a `G`-tree is a `G`-tree

This file proves `Work.ORDunwoody.PartialSubdivision`, the tree-construction service of node
N12: for a `G`-tree `R.tree` together with a `G`-invariant set `R.edges` of its edges, the graph
`psubGraph R` (`Tracks/PartialSubdivision.lean`) obtained by subdividing exactly the marked
edges is again a `G`-tree, with the expected vertex stabilizers, and it is cocompact with
finitely generated stabilizers whenever `R.tree` is.

The mathematical content is:

* `psubGraph R` is connected and acyclic (hence a tree);
* it is cocompact when `R.tree` is;
* its vertex stabilizers are the stabilizers of the vertices of `R.tree` (old vertices) or the
  *setwise* stabilizers of the marked edges (midpoints), which are finitely generated whenever
  the edge stabilizers of `R.tree` are.

The acyclicity proof uses the projection `projW` of a walk of the partial subdivision to a walk
of `R.tree` (deleting the steps whose two endpoints have the same image under the "choose an
endpoint" map `psubPhi`).  A step is *collapsed* exactly when it joins `Sum.inl u` to
`Sum.inr e` with `u = psubPhi (Sum.inr e)`: then the image of the step is a genuine edge of
`T`, and the image map is injective on non-collapsed steps (`psub_edge_image_inj`).  Hence a
cycle of `psubGraph R` projects to a closed *trail* of positive length in `T`
(`projW_isTrail`, `AllCollapsed_of_projW_length_eq_zero`, `not_allCollapsed_of_isCycle`), which
in a tree is impossible.
-/
import Mathlib
import Submission.Work.ORDunwoody.Hypotheses
import Submission.Work.ORDunwoody.Tracks.PartialSubdivision
import Submission.Work.ORDunwoody.Lemmas.barycentricDefs
import Submission.Work.ORDunwoody.Lemmas.psubAux
import Submission.Work.ORDunwoody.Lemmas.isCocompact_iff_transversal

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORDunwoody

open GTree

variable {G : Type u} [Group G] {V : Type u} [MulAction G V]

/-! ## The endpoint map and the projection of walks -/

/-- A chosen endpoint of a marked edge, viewed as a map on the vertices of the partial
subdivision: old vertices go to themselves, midpoints to (an arbitrarily chosen) endpoint of
the corresponding edge. -/
noncomputable def psubPhi (R : EdgeInv G V) : PSubV R → V
  | Sum.inl v => v
  | Sum.inr e =>
      Classical.choose (Lemmas.exists_mem_of_mem_edgeSet (G := R.tree.graph) (R.isEdge e e.2))

@[simp] theorem psubPhi_inl (R : EdgeInv G V) (v : V) : psubPhi R (Sum.inl v) = v := rfl

theorem psubPhi_inr_mem (R : EdgeInv G V) (e : {e : Sym2 V // e ∈ R.edges}) :
    psubPhi R (Sum.inr e) ∈ (e : Sym2 V) :=
  Classical.choose_spec (Lemmas.exists_mem_of_mem_edgeSet (G := R.tree.graph) (R.isEdge e e.2))

/-- The map `psubPhi` sends adjacent vertices of the partial subdivision to adjacent vertices of
the tree, or to the same vertex. -/
theorem psubPhi_adj (R : EdgeInv G V) {a b : PSubV R} (h : (psubGraph R).Adj a b) :
    psubPhi R a = psubPhi R b ∨ R.tree.Adj (psubPhi R a) (psubPhi R b) := by
  rcases a with u | e <;> rcases b with v | f
  · exact Or.inr h.1
  · rcases eq_or_ne u (psubPhi R (Sum.inr f)) with h' | h'
    · exact Or.inl (by rw [psubPhi_inl]; exact h')
    · refine Or.inr ?_
      have h1 : u ∈ (f : Sym2 V) := h
      have h2 : psubPhi R (Sum.inr f) ∈ (f : Sym2 V) := psubPhi_inr_mem R f
      have hf : (f : Sym2 V) = s(u, psubPhi R (Sum.inr f)) :=
        (Sym2.mem_and_mem_iff h').mp ⟨h1, h2⟩
      have hmem : (f : Sym2 V) ∈ R.tree.graph.edgeSet := R.isEdge f f.2
      rw [hf] at hmem
      rw [psubPhi_inl]
      exact (SimpleGraph.mem_edgeSet _).mp hmem
  · rcases eq_or_ne (psubPhi R (Sum.inr e)) v with h' | h'
    · exact Or.inl (by rw [psubPhi_inl]; exact h')
    · refine Or.inr ?_
      have h1 : v ∈ (e : Sym2 V) := h
      have h2 : psubPhi R (Sum.inr e) ∈ (e : Sym2 V) := psubPhi_inr_mem R e
      have he : (e : Sym2 V) = s(psubPhi R (Sum.inr e), v) :=
        (Sym2.mem_and_mem_iff h').mp ⟨h2, h1⟩
      have hmem : (e : Sym2 V) ∈ R.tree.graph.edgeSet := R.isEdge e e.2
      rw [he] at hmem
      rw [psubPhi_inl]
      exact (SimpleGraph.mem_edgeSet _).mp hmem
  · exact absurd h (by simp)

/-- The projection of a walk of the partial subdivision to a walk of the tree: each step whose
endpoints have distinct images is kept, each step collapsed by `psubPhi` is deleted. -/
noncomputable def projW (R : EdgeInv G V) :
    ∀ {x y : PSubV R}, (psubGraph R).Walk x y →
      R.tree.graph.Walk (psubPhi R x) (psubPhi R y)
  | _, _, .nil => .nil
  | x, y, .cons (v := z) h rest => by
      classical
      by_cases hφ : psubPhi R x = psubPhi R z
      · exact (projW R rest).copy hφ.symm rfl
      · exact .cons ((psubPhi_adj R h).resolve_left hφ) (projW R rest)

/-- Every edge of `projW p` is the image under `psubPhi` of an edge of `p`. -/
theorem projW_edges (R : EdgeInv G V) {x y : PSubV R} (p : (psubGraph R).Walk x y) :
    ∀ f ∈ (projW R p).edges,
      ∃ a b : PSubV R, s(a, b) ∈ p.edges ∧ s(psubPhi R a, psubPhi R b) = f := by
  induction p with
  | nil => intro f hf; rw [projW.eq_1] at hf; simp at hf
  | cons h rest ih =>
      rw [projW.eq_2]
      split_ifs with hφ
      · intro f hf
        rw [SimpleGraph.Walk.edges_copy] at hf
        obtain ⟨a, b, hab, hf'⟩ := ih f hf
        exact ⟨a, b, List.mem_cons_of_mem _ hab, hf'⟩
      · intro f hf
        rw [SimpleGraph.Walk.edges_cons] at hf
        rcases List.mem_cons.mp hf with hf | hf
        · exact ⟨_, _, List.mem_cons_self .., hf.symm⟩
        · obtain ⟨a, b, hab, hf'⟩ := ih f hf
          exact ⟨a, b, List.mem_cons_of_mem _ hab, hf'⟩

/-- The image of a step joining an old vertex to a midpoint of a marked edge, when that step is
not collapsed, is the marked edge itself. -/
theorem psubPhi_image_mixed_inl (R : EdgeInv G V) {u : V} (e : {e : Sym2 V // e ∈ R.edges})
    (hu : u ∈ (e : Sym2 V)) (h : u ≠ psubPhi R (Sum.inr e)) :
    s(psubPhi R (Sum.inl u), psubPhi R (Sum.inr e)) = (e : Sym2 V) := by
  rw [psubPhi_inl]
  exact ((Sym2.mem_and_mem_iff h).mp ⟨hu, psubPhi_inr_mem R e⟩).symm

/-- The mirror image of `psubPhi_image_mixed_inl` with the endpoints of the step interchanged. -/
theorem psubPhi_image_mixed_inr (R : EdgeInv G V) {v : V} (e : {e : Sym2 V // e ∈ R.edges})
    (hv : v ∈ (e : Sym2 V)) (h : psubPhi R (Sum.inr e) ≠ v) :
    s(psubPhi R (Sum.inr e), psubPhi R (Sum.inl v)) = (e : Sym2 V) := by
  rw [Sym2.eq_swap]
  exact psubPhi_image_mixed_inl R e hv (Ne.symm h)

/-- Two `Sym2` elements with the same second element are determined by their first elements. -/
theorem sym2_eq_of_pair_right {α : Type*} {x y w : α} (h : s(x, w) = s(y, w)) (hx : x ≠ w) :
    x = y := by
  have hmem : x ∈ s(y, w) := by rw [← h]; exact Sym2.mem_mk_left x w
  rcases Sym2.mem_iff.mp hmem with h' | h'
  · exact h'
  · exact absurd h' hx

/-- Two `Sym2` elements with the same first element are determined by their second elements. -/
theorem sym2_eq_of_pair_left {α : Type*} {x y w : α} (h : s(w, x) = s(w, y)) (hx : x ≠ w) :
    x = y := by
  have hmem : x ∈ s(w, y) := by rw [← h]; exact Sym2.mem_mk_right w x
  rcases Sym2.mem_iff.mp hmem with h' | h'
  · exact absurd h' hx
  · exact h'

/-- The map sending a non-collapsed step of the partial subdivision to its image in the tree is
injective: the image of a step determines the step. -/
theorem psub_edge_image_inj (R : EdgeInv G V) {a b c d : PSubV R}
    (hab : (psubGraph R).Adj a b) (hcd : (psubGraph R).Adj c d)
    (h₁ : psubPhi R a ≠ psubPhi R b) (h₂ : psubPhi R c ≠ psubPhi R d)
    (him : s(psubPhi R a, psubPhi R b) = s(psubPhi R c, psubPhi R d)) :
    s(a, b) = s(c, d) := by
  rcases a with u₁ | e₁ <;> rcases b with v₁ | f₁ <;> rcases c with u₂ | e₂ <;>
    rcases d with v₂ | f₂
  · -- old vertex to old vertex
    have h := congrArg (Sym2.map (fun x : V => (Sum.inl x : PSubV R))) him
    simpa only [Sym2.map_mk, psubPhi_inl] using h
  · simp only [psubPhi_inl] at h₁ him
    have hmix : s(u₂, psubPhi R (Sum.inr f₂)) = (f₂ : Sym2 V) :=
      psubPhi_image_mixed_inl R f₂ hcd h₂
    rw [hmix] at him
    exact absurd (him ▸ f₂.2) hab.2
  · simp only [psubPhi_inl] at h₁ him
    have hmix : s(psubPhi R (Sum.inr e₂), v₂) = (e₂ : Sym2 V) :=
      psubPhi_image_mixed_inr R e₂ hcd h₂
    rw [hmix] at him
    exact absurd (him ▸ e₂.2) hab.2
  · exact absurd hcd (psubGraph_adj_inr_inr R e₂ f₂)
  · simp only [psubPhi_inl] at h₁ him
    have hmix : s(u₁, psubPhi R (Sum.inr f₁)) = (f₁ : Sym2 V) :=
      psubPhi_image_mixed_inl R f₁ hab h₁
    rw [hmix] at him
    exact absurd (him ▸ f₁.2) hcd.2
  · simp only [psubPhi_inl] at h₁ h₂ him
    have hA : s(u₁, psubPhi R (Sum.inr f₁)) = (f₁ : Sym2 V) :=
      psubPhi_image_mixed_inl R f₁ hab h₁
    have hB : s(u₂, psubPhi R (Sum.inr f₂)) = (f₂ : Sym2 V) :=
      psubPhi_image_mixed_inl R f₂ hcd h₂
    have hff : (f₁ : Sym2 V) = (f₂ : Sym2 V) := by rw [← hA, him, hB]
    have hsub : f₁ = f₂ := Subtype.ext hff
    subst hsub
    have hu : u₁ = u₂ := sym2_eq_of_pair_right him h₁
    rw [hu]
  · simp only [psubPhi_inl] at h₁ h₂ him
    have hA : s(u₁, psubPhi R (Sum.inr f₁)) = (f₁ : Sym2 V) :=
      psubPhi_image_mixed_inl R f₁ hab h₁
    have hB : s(psubPhi R (Sum.inr e₂), v₂) = (e₂ : Sym2 V) :=
      psubPhi_image_mixed_inr R e₂ hcd h₂
    have hff : (f₁ : Sym2 V) = (e₂ : Sym2 V) := by rw [← hA, him, hB]
    have hsub : f₁ = e₂ := Subtype.ext hff
    subst hsub
    have huv : u₁ = v₂ := by
      have hmem : u₁ ∈ s(psubPhi R (Sum.inr f₁), v₂) := by
        rw [← him]; exact Sym2.mem_mk_left u₁ (psubPhi R (Sum.inr f₁))
      rcases Sym2.mem_iff.mp hmem with h' | h'
      · exact absurd h' h₁
      · exact h'
    rw [huv]
    exact Sym2.eq_swap
  · exact absurd hcd (psubGraph_adj_inr_inr R e₂ f₂)
  · simp only [psubPhi_inl] at h₁ him
    have hmix : s(psubPhi R (Sum.inr e₁), v₁) = (e₁ : Sym2 V) :=
      psubPhi_image_mixed_inr R e₁ hab h₁
    rw [hmix] at him
    exact absurd (him ▸ e₁.2) hcd.2
  · simp only [psubPhi_inl] at h₁ h₂ him
    have hA : s(psubPhi R (Sum.inr e₁), v₁) = (e₁ : Sym2 V) :=
      psubPhi_image_mixed_inr R e₁ hab h₁
    have hB : s(u₂, psubPhi R (Sum.inr f₂)) = (f₂ : Sym2 V) :=
      psubPhi_image_mixed_inl R f₂ hcd h₂
    have hff : (e₁ : Sym2 V) = (f₂ : Sym2 V) := by rw [← hA, him, hB]
    have hsub : e₁ = f₂ := Subtype.ext hff
    subst hsub
    have hv : v₁ = u₂ := by
      have hmem : v₁ ∈ s(u₂, psubPhi R (Sum.inr e₁)) := by
        rw [← him]; exact Sym2.mem_mk_right (psubPhi R (Sum.inr e₁)) v₁
      rcases Sym2.mem_iff.mp hmem with h' | h'
      · exact h'
      · exact absurd h' (Ne.symm h₁)
    rw [hv]
    exact Sym2.eq_swap
  · simp only [psubPhi_inl] at h₁ h₂ him
    have hA : s(psubPhi R (Sum.inr e₁), v₁) = (e₁ : Sym2 V) :=
      psubPhi_image_mixed_inr R e₁ hab h₁
    have hB : s(psubPhi R (Sum.inr e₂), v₂) = (e₂ : Sym2 V) :=
      psubPhi_image_mixed_inr R e₂ hcd h₂
    have hff : (e₁ : Sym2 V) = (e₂ : Sym2 V) := by rw [← hA, him, hB]
    have hsub : e₁ = e₂ := Subtype.ext hff
    subst hsub
    rw [sym2_eq_of_pair_left him (Ne.symm h₁)]
  · exact absurd hcd (psubGraph_adj_inr_inr R e₂ f₂)
  · exact absurd hab (psubGraph_adj_inr_inr R e₁ f₁)
  · exact absurd hab (psubGraph_adj_inr_inr R e₁ f₁)
  · exact absurd hab (psubGraph_adj_inr_inr R e₁ f₁)
  · exact absurd hab (psubGraph_adj_inr_inr R e₁ f₁)

/-- The projection of a trail is a trail: distinct non-collapsed steps have distinct images. -/
theorem projW_isTrail (R : EdgeInv G V) {x y : PSubV R} (p : (psubGraph R).Walk x y)
    (hp : p.IsTrail) : (projW R p).IsTrail := by
  revert hp
  induction p with
  | nil => intro _; exact SimpleGraph.Walk.IsTrail.nil
  | cons h rest ih =>
      intro hp
      rw [projW.eq_2]
      rw [SimpleGraph.Walk.isTrail_cons] at hp
      split_ifs with hφ
      · rw [SimpleGraph.Walk.isTrail_copy]
        exact ih hp.1
      · rw [SimpleGraph.Walk.isTrail_def, SimpleGraph.Walk.edges_cons, List.nodup_cons]
        refine ⟨?_, ?_⟩
        · intro hmem
          obtain ⟨a, b, hab, himage⟩ := projW_edges R rest _ hmem
          have hab' : (psubGraph R).Adj a b :=
            (SimpleGraph.mem_edgeSet _).mp (rest.edges_subset_edgeSet hab)
          have h₂ : psubPhi R _ ≠ psubPhi R _ := hφ
          have h₁ : psubPhi R a ≠ psubPhi R b := by
            intro hh
            rcases Sym2.eq_iff.mp himage with ⟨h1', h2'⟩ | ⟨h1', h2'⟩
            · exact hφ (by rw [← h1', ← h2', hh])
            · exact hφ (by rw [← h2', ← h1', hh])
          exact absurd (psub_edge_image_inj R hab' h h₁ h₂ himage ▸ hab) hp.2
        · exact (ih hp.1).edges_nodup

/-! ## Positivity of the length of the projection of a cycle -/

/-- A walk of the partial subdivision all of whose steps are collapsed by `psubPhi`. -/
def AllCollapsed (R : EdgeInv G V) {x y : PSubV R} (p : (psubGraph R).Walk x y) : Prop :=
  ∀ i : ℕ, i < p.length → psubPhi R (p.getVert i) = psubPhi R (p.getVert (i + 1))

/-- The first step of a walk is collapsed if and only if the walk is `AllCollapsed` on its
tail. -/
theorem allCollapsed_cons (R : EdgeInv G V) {x z w : PSubV R}
    (h : (psubGraph R).Adj x z) (rest : (psubGraph R).Walk z w) :
    AllCollapsed R (SimpleGraph.Walk.cons h rest) ↔
      psubPhi R x = psubPhi R z ∧ AllCollapsed R rest := by
  constructor
  · intro hp
    refine ⟨?_, ?_⟩
    · have := hp 0 (by rw [SimpleGraph.Walk.length_cons]; omega)
      simpa using this
    · intro i hi
      have h2 := hp (i + 1) (by rw [SimpleGraph.Walk.length_cons]; omega)
      simpa [SimpleGraph.Walk.getVert_cons_succ] using h2
  · rintro ⟨h0, hrest⟩ i hi
    rw [SimpleGraph.Walk.length_cons] at hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · simpa using h0
    · obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (Nat.pos_iff_ne_zero.mp hpos)
      have hj : j < rest.length := by omega
      simp only [SimpleGraph.Walk.getVert_cons_succ]
      exact hrest j hj

/-- A walk whose projection is trivial is `AllCollapsed`: the steps of `projW` are exactly the
non-collapsed steps. -/
theorem AllCollapsed_of_projW_length_eq_zero (R : EdgeInv G V) {x y : PSubV R}
    (p : (psubGraph R).Walk x y) : (projW R p).length = 0 → AllCollapsed R p := by
  induction p with
  | nil => intro _ i hi; simp at hi
  | cons h rest ih =>
      intro hlen
      rw [allCollapsed_cons R h rest]
      rw [projW.eq_2] at hlen
      split_ifs at hlen with hφ
      · refine ⟨hφ, ih ?_⟩
        rwa [SimpleGraph.Walk.length_copy] at hlen
      · rw [SimpleGraph.Walk.length_cons] at hlen
        exact absurd hlen (by omega)

/-- An endpoint of a collapsed edge incident with the midpoint `Sum.inr e` is the old vertex
`Sum.inl (psubPhi (Sum.inr e))`. -/
theorem eq_inl_psubPhi_of_adj_mid (R : EdgeInv G V) {a : PSubV R}
    (e : {e : Sym2 V // e ∈ R.edges}) (h : (psubGraph R).Adj a (Sum.inr e))
    (hφ : psubPhi R a = psubPhi R (Sum.inr e)) :
    a = Sum.inl (psubPhi R (Sum.inr e)) := by
  rcases a with u | e'
  · rw [psubPhi_inl] at hφ
    rw [hφ]
  · exact absurd h (psubGraph_adj_inr_inr R e' e)

/-- A cycle of the partial subdivision is not `AllCollapsed`: two consecutive collapsed edges at
a midpoint would have the same midpoint as an endpoint, hence would coincide. -/
theorem not_allCollapsed_of_isCycle (R : EdgeInv G V) {x : PSubV R}
    (c : (psubGraph R).Walk x x) (hc : c.IsCycle) : ¬ AllCollapsed R c := by
  intro hall
  have hn : 3 ≤ c.length := hc.three_le_length
  have h0 : psubPhi R (c.getVert 0) = psubPhi R (c.getVert 1) := hall 0 (by omega)
  have h1 : psubPhi R (c.getVert 1) = psubPhi R (c.getVert 2) := hall 1 (by omega)
  have h2 : psubPhi R (c.getVert 2) = psubPhi R (c.getVert 3) := hall 2 (by omega)
  have adj0 : (psubGraph R).Adj (c.getVert 0) (c.getVert 1) :=
    SimpleGraph.Walk.adj_getVert_succ c (i := 0) (by omega)
  have adj1 : (psubGraph R).Adj (c.getVert 1) (c.getVert 2) :=
    SimpleGraph.Walk.adj_getVert_succ c (i := 1) (by omega)
  have adj2 : (psubGraph R).Adj (c.getVert 2) (c.getVert 3) :=
    SimpleGraph.Walk.adj_getVert_succ c (i := 2) (by omega)
  cases hz1 : c.getVert 1 with
  | inl u1 =>
    cases hz2 : c.getVert 2 with
    | inl u2 =>
      have hne : u1 ≠ u2 := by
        have had := adj1
        rw [hz1, hz2] at had
        exact had.1.ne
      rw [hz1, hz2, psubPhi_inl, psubPhi_inl] at h1
      exact hne h1
    | inr e2 =>
      have hz1' : c.getVert 1 = Sum.inl (psubPhi R (Sum.inr e2)) :=
        eq_inl_psubPhi_of_adj_mid R e2 (hz2 ▸ adj1) (hz2 ▸ h1)
      have hz3' : c.getVert 3 = Sum.inl (psubPhi R (Sum.inr e2)) :=
        eq_inl_psubPhi_of_adj_mid R e2 (hz2 ▸ adj2.symm) (hz2 ▸ h2.symm)
      have hc2 : c.getVert 1 ≠ c.getVert 3 :=
        show c.getVert (2 - 1) ≠ c.getVert (2 + 1) from
          hc.getVert_sub_one_ne_getVert_add_one (i := 2) (by omega)
      exact hc2 (hz1'.trans hz3'.symm)
  | inr e1 =>
    have hz0 : c.getVert 0 = Sum.inl (psubPhi R (Sum.inr e1)) :=
      eq_inl_psubPhi_of_adj_mid R e1 (hz1 ▸ adj0) (hz1 ▸ h0)
    have hz2 : c.getVert 2 = Sum.inl (psubPhi R (Sum.inr e1)) :=
      eq_inl_psubPhi_of_adj_mid R e1 (hz1 ▸ adj1.symm) (hz1 ▸ h1.symm)
    have hc1 : c.getVert 0 ≠ c.getVert 2 :=
      show c.getVert (1 - 1) ≠ c.getVert (1 + 1) from
        hc.getVert_sub_one_ne_getVert_add_one (i := 1) (by omega)
    exact hc1 (hz0.trans hz2.symm)

/-- **The partial subdivision of a tree is acyclic.**  A cycle would project to a closed trail
of positive length in `R.tree`. -/
theorem psubGraph_isAcyclic (R : EdgeInv G V) : (psubGraph R).IsAcyclic := by
  intro x c hc
  classical
  have htrail : (projW R c).IsTrail := projW_isTrail R c hc.isTrail
  have hne : projW R c ≠ SimpleGraph.Walk.nil := by
    intro hnil
    have hlen : (projW R c).length = 0 := by rw [hnil]; rfl
    exact not_allCollapsed_of_isCycle R c hc (AllCollapsed_of_projW_length_eq_zero R c hlen)
  have hcircuit : (projW R c).IsCircuit := ⟨htrail, hne⟩
  exact R.tree.isTree.isAcyclic _ hcircuit.isCycle_cycleBypass

/-! ## Connectivity -/

/-- A walk of the tree lifts to a walk of the partial subdivision between the corresponding old
vertices: a step of the tree is kept if the corresponding edge is unmarked and routed through
the new midpoint if it is marked. -/
theorem lifts_walk (R : EdgeInv G V) : ∀ {u v : V} (p : R.tree.graph.Walk u v),
    Nonempty ((psubGraph R).Walk (Sum.inl u) (Sum.inl v)) := by
  intro u v p
  induction p with
  | nil => exact ⟨SimpleGraph.Walk.nil⟩
  | cons hab rest ih =>
      rename_i x y z
      by_cases hmem : s(x, y) ∈ R.edges
      · have h1 : (psubGraph R).Adj (Sum.inl x) (Sum.inr ⟨s(x, y), hmem⟩) := by
          rw [psubGraph_adj_inl_inr]; exact Sym2.mem_mk_left x y
        have h2 : (psubGraph R).Adj (Sum.inr ⟨s(x, y), hmem⟩) (Sum.inl y) := by
          rw [psubGraph_adj_inr_inl]; exact Sym2.mem_mk_right x y
        obtain ⟨q⟩ := ih
        exact ⟨SimpleGraph.Walk.cons h1 (SimpleGraph.Walk.cons h2 q)⟩
      · have h1 : (psubGraph R).Adj (Sum.inl x) (Sum.inl y) := ⟨hab, hmem⟩
        obtain ⟨q⟩ := ih
        exact ⟨SimpleGraph.Walk.cons h1 q⟩

/-- Reachability of two vertices of the tree implies reachability of the corresponding old
vertices of the partial subdivision. -/
theorem reachable_inl_inl (R : EdgeInv G V) {u v : V} (h : R.tree.graph.Reachable u v) :
    (psubGraph R).Reachable (Sum.inl u) (Sum.inl v) :=
  h.elim fun p => (lifts_walk R p).elim fun q => ⟨q⟩

/-- **The partial subdivision of a connected graph is connected.** -/
theorem psubGraph_connected (R : EdgeInv G V) : (psubGraph R).Connected := by
  have hT := R.tree.isTree.connected
  haveI : Nonempty (PSubV R) := hT.nonempty.elim fun v => ⟨Sum.inl v⟩
  refine ⟨fun a b => ?_⟩
  rcases a with u | e
  · rcases b with v | f
    · exact reachable_inl_inl R (hT.preconnected u v)
    · exact (reachable_inl_inl R (hT.preconnected u (psubPhi R (Sum.inr f)))).trans
        (SimpleGraph.Adj.reachable (by
          rw [psubGraph_adj_inl_inr]; exact psubPhi_inr_mem R f))
  · rcases b with v | f
    · exact (SimpleGraph.Adj.reachable (by
          rw [psubGraph_adj_inr_inl]; exact psubPhi_inr_mem R e)).trans
        (reachable_inl_inl R (hT.preconnected (psubPhi R (Sum.inr e)) v))
    · exact (SimpleGraph.Adj.reachable (by
          rw [psubGraph_adj_inr_inl]; exact psubPhi_inr_mem R e)).trans
        ((reachable_inl_inl R (hT.preconnected (psubPhi R (Sum.inr e))
            (psubPhi R (Sum.inr f)))).trans
        (SimpleGraph.Adj.reachable (by
          rw [psubGraph_adj_inl_inr]; exact psubPhi_inr_mem R f)))

/-- **The partial subdivision of a tree is a tree.** -/
theorem psubGraph_isTree (R : EdgeInv G V) : (psubGraph R).IsTree :=
  ⟨psubGraph_connected R, psubGraph_isAcyclic R⟩

/-! ## Finitely generated stabilizers -/

/-- A subgroup generated by a finitely generated subgroup together with one further element is
finitely generated. -/
theorem FG_of_le_of_sup_singleton {P S : Subgroup G} (hPS : P ≤ S) (hP : P.FG) {σ : G}
    (hσ : σ ∈ S) (hcover : ∀ g ∈ S, g ∈ P ∨ ∃ p ∈ P, g = σ * p) : S.FG := by
  have hS : S = P ⊔ Subgroup.closure ({σ} : Set G) := by
    refine le_antisymm ?_ (sup_le hPS ?_)
    · intro g hg
      rcases hcover g hg with h | ⟨p, hp, hgp⟩
      · exact Subgroup.mem_sup_left h
      · rw [hgp]
        exact Subgroup.mul_mem _
          (Subgroup.mem_sup_right (Subgroup.subset_closure (Set.mem_singleton σ)))
          (Subgroup.mem_sup_left hp)
    · rw [Subgroup.closure_le]
      exact Set.singleton_subset_iff.mpr hσ
  rw [hS]
  exact Subgroup.FG.sup hP ((Group.fg_iff_subgroup_fg _).mp inferInstance)

/-- The stabilizer of the midpoint of a marked edge is finitely generated: it is the setwise
stabilizer of the edge, a subgroup of index at most `2` in it being the pointwise stabilizer,
which is an edge stabilizer of the tree. -/
theorem psub_mid_vertexStab_FG (R : EdgeInv G V) (h : (psubGraph R).IsTree)
    (hf : R.tree.HasFGStab) (e : {e : Sym2 V // e ∈ R.edges}) :
    ((psubGT R h).vertexStab (Sum.inr e)).FG := by
  classical
  obtain ⟨u, hu⟩ := Lemmas.exists_mem_of_mem_edgeSet (G := R.tree.graph) (R.isEdge e e.2)
  obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hu
  have hadj : R.tree.Adj u w := (SimpleGraph.mem_edgeSet _).mp (hw ▸ R.isEdge e e.2)
  have hS : ∀ g : G, g ∈ (psubGT R h).vertexStab (Sum.inr e) ↔
      (g • u = u ∧ g • w = w) ∨ (g • u = w ∧ g • w = u) := by
    intro g
    rw [psubGT_vertexStab_inr_mem R h e g, hw, Sym2.map_mk, Sym2.eq_iff]
  have hPmem : ∀ g : G, g ∈ R.tree.edgeStab u w ↔ (g • u = u ∧ g • w = w) :=
    fun g => gTree_edgeStab_mem R.tree g
  have hP : (R.tree.edgeStab u w).FG := hf.2 u w hadj
  by_cases hσ : ∃ σ : G, σ • u = w ∧ σ • w = u
  · obtain ⟨σ, hσu, hσw⟩ := hσ
    have hσS : σ ∈ (psubGT R h).vertexStab (Sum.inr e) :=
      (hS σ).mpr (Or.inr ⟨hσu, hσw⟩)
    refine FG_of_le_of_sup_singleton (fun g hg => (hS g).mpr (Or.inl ((hPmem g).mp hg)))
      hP hσS ?_
    intro g hg
    rcases (hS g).mp hg with ⟨hgu, hgw⟩ | ⟨hgu, hgw⟩
    · exact Or.inl ((hPmem g).mpr ⟨hgu, hgw⟩)
    · refine Or.inr ⟨σ⁻¹ * g, (hPmem _).mpr ⟨?_, ?_⟩, ?_⟩
      · show (σ⁻¹ * g) • u = u
        rw [mul_smul, hgu, ← hσu, inv_smul_smul]
      · show (σ⁻¹ * g) • w = w
        rw [mul_smul, hgw, ← hσw, inv_smul_smul]
      · group
  · have hSP : (psubGT R h).vertexStab (Sum.inr e) ≤ R.tree.edgeStab u w := by
      intro g hg
      rcases (hS g).mp hg with hh | hh
      · exact (hPmem g).mpr hh
      · exact absurd ⟨g, hh.1, hh.2⟩ hσ
    have heq : (psubGT R h).vertexStab (Sum.inr e) = R.tree.edgeStab u w :=
      le_antisymm hSP (fun g hg => (hS g).mpr (Or.inl ((hPmem g).mp hg)))
    rw [heq]; exact hP

/-- The stabilizer of the half-edge joining an old vertex to a midpoint is the pointwise
stabilizer of the marked edge, hence an edge stabilizer of the tree. -/
theorem psub_edgeStab_inl_inr_FG (R : EdgeInv G V) (h : (psubGraph R).IsTree)
    (hf : R.tree.HasFGStab) {u : V} (e : {e : Sym2 V // e ∈ R.edges})
    (hu : u ∈ (e : Sym2 V)) : ((psubGT R h).edgeStab (Sum.inl u) (Sum.inr e)).FG := by
  classical
  obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp hu
  have hadj : R.tree.Adj u w := (SimpleGraph.mem_edgeSet _).mp (hw ▸ R.isEdge e e.2)
  have heq : (psubGT R h).edgeStab (Sum.inl u) (Sum.inr e) = R.tree.edgeStab u w := by
    ext g
    simp only [gTree_edgeStab_mem, psub_smul_inl, psub_smul_inr_eq_iff, Sum.inl.injEq]
    constructor
    · rintro ⟨hg1, hg2⟩
      rw [hw, Sym2.map_mk, Sym2.eq_iff] at hg2
      refine ⟨hg1, ?_⟩
      rcases hg2 with ⟨-, h2⟩ | ⟨h2, -⟩
      · exact h2
      · exact absurd (h2.symm.trans hg1).symm hadj.ne
    · rintro ⟨hg1, hg2⟩
      exact ⟨hg1, by rw [hw, Sym2.map_mk, hg1, hg2]⟩
  rw [heq]; exact hf.2 u w hadj

/-- **The partial subdivision has finitely generated stabilizers** whenever the tree does. -/
theorem psub_hasFGStab (R : EdgeInv G V) (h : (psubGraph R).IsTree)
    (hf : R.tree.HasFGStab) : (psubGT R h).HasFGStab := by
  refine ⟨?_, ?_⟩
  · intro v
    rcases v with u | e
    · rw [psubGT_vertexStab_inl]
      exact hf.1 u
    · exact psub_mid_vertexStab_FG R h hf e
  · intro a b hab
    rcases a with u | e <;> rcases b with v | f
    · have heqv : (psubGT R h).edgeStab (Sum.inl u) (Sum.inl v) = R.tree.edgeStab u v := by
        ext g
        simp only [gTree_edgeStab_mem, psub_smul_inl, Sum.inl.injEq]
      rw [heqv]
      exact hf.2 u v hab.1
    · exact psub_edgeStab_inl_inr_FG R h hf f hab
    · rw [GTree.edgeStab_comm]
      exact psub_edgeStab_inl_inr_FG R h hf e hab
    · exact absurd hab (psubGraph_adj_inr_inr R e f)

/-! ## Cocompactness -/

/-- **The partial subdivision is cocompact** whenever the tree is. -/
theorem psub_isCocompact (R : EdgeInv G V) (h : (psubGraph R).IsTree)
    (hc : R.tree.IsCocompact) : (psubGT R h).IsCocompact := by
  classical
  obtain ⟨⟨sV, hsV⟩, ⟨tE, htE⟩⟩ := (Lemmas.isCocompact_iff_transversal R.tree).mp hc
  -- the marked edges among the representatives of the edge orbits of the tree
  let midB : Finset (V × V) :=
    tE.filter (fun p => R.tree.Adj p.1 p.2 ∧ s(p.1, p.2) ∈ R.edges)
  let midFn : {p : V × V // p ∈ midB} → {e : Sym2 V // e ∈ R.edges} :=
    fun p => ⟨s(p.1.1, p.1.2), (Finset.mem_filter.mp p.2).2.2⟩
  let midF : Finset {e : Sym2 V // e ∈ R.edges} := midB.attach.image midFn
  have hmid : ∀ e : {e : Sym2 V // e ∈ R.edges}, ∃ g : G,
      (⟨Sym2.map (fun v : V => g • v) (e : Sym2 V), R.smul_mem g e.2⟩ :
        {e : Sym2 V // e ∈ R.edges}) ∈ midF := by
    intro e
    obtain ⟨a, ha⟩ := Lemmas.exists_mem_of_mem_edgeSet (G := R.tree.graph) (R.isEdge e e.2)
    obtain ⟨b, hb⟩ := Sym2.mem_iff_exists.mp ha
    have hadj : R.tree.Adj a b := (SimpleGraph.mem_edgeSet _).mp (hb ▸ R.isEdge e e.2)
    obtain ⟨g, hg⟩ := htE (a, b) hadj
    have hmap : s(g • a, g • b) = Sym2.map (fun v : V => g • v) (e : Sym2 V) := by
      rw [hb, Sym2.map_mk]
    have hfm : (g • a, g • b) ∈ midB :=
      Finset.mem_filter.mpr ⟨hg, R.tree.smul_adj g hadj, hmap ▸ R.smul_mem g e.2⟩
    have h1 : (⟨(g • a, g • b), hfm⟩ : {p : V × V // p ∈ midB}) ∈ midB.attach :=
      Finset.mem_attach _ _
    have h2 : midFn ⟨(g • a, g • b), hfm⟩ ∈ midF := Finset.mem_image_of_mem midFn h1
    have h3 : midFn ⟨(g • a, g • b), hfm⟩ =
        ⟨Sym2.map (fun v : V => g • v) (e : Sym2 V), R.smul_mem g e.2⟩ := Subtype.ext hmap
    exact ⟨g, h3 ▸ h2⟩
  let vertF : Finset (PSubV R) := sV.image Sum.inl ∪ midF.image Sum.inr
  have hvert : ∀ z : PSubV R, ∃ g : G, g • z ∈ vertF := by
    intro z
    rcases z with u | e
    · obtain ⟨g, hg⟩ := hsV u
      refine ⟨g, Finset.mem_union_left _ ?_⟩
      rw [psub_smul_inl]
      exact Finset.mem_image_of_mem Sum.inl hg
    · obtain ⟨g, hg⟩ := hmid e
      refine ⟨g, Finset.mem_union_right _ ?_⟩
      rw [psub_smul_inr]
      exact Finset.mem_image_of_mem Sum.inr hg
  -- the oriented edges of the partial subdivision
  let eOOB : Finset (V × V) := tE.filter (fun p => R.tree.Adj p.1 p.2 ∧ s(p.1, p.2) ∉ R.edges)
  let eOOFn : V × V → PSubV R × PSubV R :=
    fun p => ((Sum.inl p.1 : PSubV R), (Sum.inl p.2 : PSubV R))
  let eOO : Finset (PSubV R × PSubV R) := eOOB.image eOOFn
  let eXB : Finset (V × V) := tE.filter (fun p => R.tree.Adj p.1 p.2 ∧ s(p.1, p.2) ∈ R.edges)
  let eXFn : {p : V × V // p ∈ eXB} → PSubV R × PSubV R :=
    fun p => ((Sum.inl p.1.1 : PSubV R),
      (Sum.inr ⟨s(p.1.1, p.1.2), (Finset.mem_filter.mp p.2).2.2⟩ : PSubV R))
  let eX : Finset (PSubV R × PSubV R) := eXB.attach.image eXFn
  let eXFn' : {p : V × V // p ∈ eXB} → PSubV R × PSubV R :=
    fun p => ((Sum.inr ⟨s(p.1.1, p.1.2), (Finset.mem_filter.mp p.2).2.2⟩ : PSubV R),
      (Sum.inl p.1.1 : PSubV R))
  let eX' : Finset (PSubV R × PSubV R) := eXB.attach.image eXFn'
  let edgeF : Finset (PSubV R × PSubV R) := eOO ∪ eX ∪ eX'
  have hedge : ∀ p : PSubV R × PSubV R, (psubGT R h).Adj p.1 p.2 →
      ∃ g : G, (g • p.1, g • p.2) ∈ edgeF := by
    intro p hp
    rcases p with ⟨a, b⟩
    rcases a with u | e <;> rcases b with v | f
    · -- old vertex to old vertex
      obtain ⟨g, hg⟩ := htE (u, v) hp.1
      refine ⟨g, ?_⟩
      have hunm : s(g • u, g • v) ∉ R.edges := by
        intro hmem
        have h1 := R.smul_mem g⁻¹ hmem
        rw [Sym2.map_mk, inv_smul_smul, inv_smul_smul] at h1
        exact hp.2 h1
      have hfm : (g • u, g • v) ∈ eOOB :=
        Finset.mem_filter.mpr ⟨hg, R.tree.smul_adj g hp.1, hunm⟩
      have h2 : eOOFn (g • u, g • v) ∈ eOO :=
        Finset.mem_image_of_mem eOOFn hfm
      rw [psub_smul_inl, psub_smul_inl]
      exact Finset.mem_union_left _ (Finset.mem_union_left _ h2)
    · -- old vertex to midpoint
      obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp (show u ∈ (f : Sym2 V) from hp)
      have hadj : R.tree.Adj u w := (SimpleGraph.mem_edgeSet _).mp (hw ▸ R.isEdge f f.2)
      obtain ⟨g, hg⟩ := htE (u, w) hadj
      refine ⟨g, ?_⟩
      have hmap : s(g • u, g • w) = Sym2.map (fun v : V => g • v) (f : Sym2 V) := by
        rw [hw, Sym2.map_mk]
      have hfm : (g • u, g • w) ∈ eXB :=
        Finset.mem_filter.mpr ⟨hg, R.tree.smul_adj g hadj, hmap ▸ R.smul_mem g f.2⟩
      have h1 : (⟨(g • u, g • w), hfm⟩ : {p : V × V // p ∈ eXB}) ∈ eXB.attach :=
        Finset.mem_attach _ _
      have h2 : eXFn ⟨(g • u, g • w), hfm⟩ ∈ eX := Finset.mem_image_of_mem eXFn h1
      have h3 : eXFn ⟨(g • u, g • w), hfm⟩ =
          ((Sum.inl (g • u) : PSubV R),
            (Sum.inr ⟨Sym2.map (fun v : V => g • v) (f : Sym2 V), R.smul_mem g f.2⟩ : PSubV R)) :=
        Prod.ext rfl (congrArg Sum.inr (Subtype.ext hmap))
      rw [psub_smul_inl, psub_smul_inr]
      exact h3 ▸ (Finset.mem_union_left _ (Finset.mem_union_right _ h2))
    · -- midpoint to old vertex
      obtain ⟨w, hw⟩ := Sym2.mem_iff_exists.mp (show v ∈ (e : Sym2 V) from hp)
      have hadj : R.tree.Adj v w := (SimpleGraph.mem_edgeSet _).mp (hw ▸ R.isEdge e e.2)
      obtain ⟨g, hg⟩ := htE (v, w) hadj
      refine ⟨g, ?_⟩
      have hmap : s(g • v, g • w) = Sym2.map (fun v : V => g • v) (e : Sym2 V) := by
        rw [hw, Sym2.map_mk]
      have hfm : (g • v, g • w) ∈ eXB :=
        Finset.mem_filter.mpr ⟨hg, R.tree.smul_adj g hadj, hmap ▸ R.smul_mem g e.2⟩
      have h1 : (⟨(g • v, g • w), hfm⟩ : {p : V × V // p ∈ eXB}) ∈ eXB.attach :=
        Finset.mem_attach _ _
      have h2 : eXFn' ⟨(g • v, g • w), hfm⟩ ∈ eX' := Finset.mem_image_of_mem eXFn' h1
      have h3 : eXFn' ⟨(g • v, g • w), hfm⟩ =
          ((Sum.inr ⟨Sym2.map (fun v : V => g • v) (e : Sym2 V), R.smul_mem g e.2⟩ : PSubV R),
            (Sum.inl (g • v) : PSubV R)) :=
        Prod.ext (congrArg Sum.inr (Subtype.ext hmap)) rfl
      rw [psub_smul_inr, psub_smul_inl]
      exact h3 ▸ (Finset.mem_union_right _ h2)
    · exact absurd hp (psubGraph_adj_inr_inr R e f)
  exact (Lemmas.isCocompact_iff_transversal (psubGT R h)).mpr
    ⟨⟨vertF, hvert⟩, ⟨edgeF, hedge⟩⟩

/-! ## The service of node N12 -/

theorem partialSubdivision (Y : Type u) : Work.ORDunwoody.PartialSubdivision Y := by
  intro G _ V _ R hc hf
  refine ⟨psubGT R (psubGraph_isTree R), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun u v => psubGraph_adj_inl_inl R u v
  · exact fun u e => psubGraph_adj_inl_inr R u e
  · exact fun e e' => psubGraph_adj_inr_inr R e e'
  · exact fun g v => psub_smul_inl R g v
  · exact fun g e => ⟨⟨Sym2.map (fun v : V => g • v) (e : Sym2 V), R.smul_mem g e.2⟩,
      psub_smul_inr R g e⟩
  · exact fun v => psubGT_vertexStab_inl R _ v
  · exact fun e => psubGT_vertexStab_inr R _ e
  · exact psub_isCocompact R _ hc
  · exact psub_hasFGStab R _ hf

end Work.ORDunwoody
