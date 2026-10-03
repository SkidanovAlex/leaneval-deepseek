/-
Copyright: work of the ORDunwoody subproject (node N13 of the
`annals_on_coherence_of_one_relator_groups` project).

# From a quiver tree to a simplicial tree with group action

`Work.ORBassSerre` develops Bass--Serre theory for *quivers* with an involutive reversal of
arrows, while `Work.ORDunwoody` develops the theory of groups acting on *simplicial trees* in
terms of Mathlib `SimpleGraph`s.  This file proves that the two notions agree:  the underlying
simple graph of a quiver tree is a tree, and the associated `G`-action is cocompact for the
simple graph exactly when the quiver theoretic action is cocompact.

The proof of `ofQuiverTree` proceeds as follows.

* The underlying graph `quiverGraph V hnl` has `Adj u v := Nonempty (u ⟶ v)`; it is a
  `SimpleGraph` because a tree quiver has no loops (`noLoop_of_isTree`).
* It is connected, since a path in the quiver induces a walk in the graph (`toWalk`).
* It is acyclic.  A cycle in the graph would give (after dropping its first step) a walk
  `p` with `p.IsPath`; the induced path `ofWalk p` is reduced (`isReduced_ofWalk_of_isPath`),
  and by uniqueness of reduced paths in a tree (`qpath_eq_of_isTree`) it must be the
  one-arrow path, so `p` has length one.  A closed walk of length two is not a trail in a
  simple graph, so it is not a cycle.
* Finally, `T.IsCocompact` is about orbits of vertices and of oriented edges, while
  `Work.ORBassSerre.IsCocompact` is about orbits of vertices and of arrows; the two edge
  parts agree because a tree quiver has at most one arrow between two vertices, so an
  oriented edge and an arrow are the same thing.
-/
import Mathlib
import Submission.Work.ORDunwoody.Basic
import Submission.Work.ORBassSerre.Action.Basic
import Submission.Work.ORDunwoody.Lemmas.ofQuiverTreeDefs
import Submission.Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree
import Submission.Work.ORDunwoody.Lemmas.isCocompact_iff_transversal

set_option autoImplicit false

set_option linter.unusedVariables false

universe u v w

namespace Work.ORDunwoody.Lemmas

open Quiver

/-! ## A quiver tree has no loops and at most one arrow between any two vertices -/

section QuiverTree

variable {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-- In a tree quiver there are no loops. -/
theorem noLoop_of_isTree (h : Work.ORBassSerre.IsTree V) (u : V) : ¬ Nonempty (u ⟶ u) := by
  rintro ⟨e⟩
  have hred : e.toPath.IsReduced :=
    Quiver.Path.IsReduced.of_length_lt_two (by rw [Quiver.Path.length_toPath]; norm_num)
  have hnil := h.2 u e.toPath hred
  have hlen := congrArg Quiver.Path.length hnil
  rw [Quiver.Path.length_toPath, Quiver.Path.length_nil] at hlen
  exact absurd hlen (by norm_num)

/-- In a tree quiver there is at most one arrow between any two vertices. -/
theorem subsingleton_hom_of_isTree (h : Work.ORBassSerre.IsTree V) (u v : V) :
    Subsingleton (u ⟶ v) := by
  refine ⟨fun e f => ?_⟩
  have hred : ∀ e' : u ⟶ v, e'.toPath.IsReduced := fun e' =>
    Quiver.Path.IsReduced.of_length_lt_two (by rw [Quiver.Path.length_toPath]; norm_num)
  have heq : e.toPath = f.toPath :=
    Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree h (hred e) (hred f)
  have h2 : (Quiver.Path.nil.cons e) = (Quiver.Path.nil.cons f) := by
    simpa only [Quiver.Hom.toPath] using heq
  exact eq_of_heq (Quiver.Path.hom_heq_of_cons_eq_cons h2)

end QuiverTree

/-! ## The induced path of a walk in the underlying graph -/

section Induced

variable {V : Type v} [Quiver V] [Quiver.HasInvolutiveReverse V]
  {hnl : ∀ u : V, ¬ Nonempty (u ⟶ u)}

/-- **A simple walk induces a reduced path.**  If a walk in the underlying graph has no
repeated vertices, then the induced path has no backtracks: a backtrack `e · e⁻¹` would
display the same vertex twice in the vertex list. -/
theorem isReduced_ofWalk_of_isPath {a b : V} (p : (quiverGraph V hnl).Walk a b)
    (hp : p.IsPath) : (ofWalk p).IsReduced := by
  intro q hdb
  obtain ⟨x, y, p₁, e, p₂, h1, -⟩ :=
    Work.ORBassSerre.Tree.Geodesic.deleteBacktrack_iff.mp hdb
  have hN : ((ofWalk p).vertices).Nodup := by
    rw [vertices_ofWalk]
    exact hp.support_nodup
  rw [h1, vertices_comp_backtrack] at hN
  exact List.disjoint_of_nodup_append hN
    (List.mem_append_right _ List.mem_cons_self) (Quiver.Path.start_mem_vertices p₂)

/-- The underlying graph of a connected quiver is connected. -/
theorem preconnected_quiverGraph (h : Work.ORBassSerre.IsTree V) :
    (quiverGraph V hnl).Preconnected := by
  intro a b
  obtain ⟨p⟩ := h.1 a b
  exact ⟨toWalk p⟩

/-- A closed walk of length two is not a trail in a simple graph. -/
theorem not_isTrail_cons_cons_nil {V' : Type v} {G : SimpleGraph V'} {a b : V'}
    (h : G.Adj a b) (h' : G.Adj b a) :
    ¬ (SimpleGraph.Walk.cons h (SimpleGraph.Walk.cons h' SimpleGraph.Walk.nil)).IsTrail := by
  intro htr
  have hedges : (s(a, b) :: s(b, a) :: []).Nodup := htr.edges_nodup
  have hmem : s(a, b) ∉ [s(b, a)] := (List.nodup_cons.mp hedges).1
  exact hmem (List.mem_singleton.mpr Sym2.eq_swap)

/-- **The underlying graph of a quiver tree is acyclic.** -/
theorem isAcyclic_quiverGraph (h : Work.ORBassSerre.IsTree V) :
    (quiverGraph V hnl).IsAcyclic := by
  intro v c hc
  cases c with
  | nil => exact hc.isCircuit.ne_nil rfl
  | cons hadj p =>
    have hnodup : p.support.Nodup := by
      have h1 := hc.support_nodup
      rw [SimpleGraph.Walk.support_cons, List.tail_cons] at h1
      exact h1
    have hred : (ofWalk p).IsReduced :=
      isReduced_ofWalk_of_isPath p (SimpleGraph.Walk.IsPath.mk' hnodup)
    have hrevred : (Quiver.reverse (Classical.choice hadj)).toPath.IsReduced :=
      Quiver.Path.IsReduced.of_length_lt_two (by rw [Quiver.Path.length_toPath]; norm_num)
    have heq : ofWalk p = (Quiver.reverse (Classical.choice hadj)).toPath :=
      Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree h hred hrevred
    have hlen : p.length = 1 := by
      have h1 := ofWalk_length p
      rw [heq, Quiver.Path.length_toPath] at h1
      exact h1.symm
    have htrail : (SimpleGraph.Walk.cons hadj p).IsTrail := hc.isCircuit.isTrail
    cases p with
    | nil => simp at hlen
    | cons h' p' =>
      have hp' : p'.length = 0 := by
        simp only [SimpleGraph.Walk.length_cons] at hlen
        omega
      cases p' with
      | nil => exact not_isTrail_cons_cons_nil hadj h' htrail
      | cons h'' p'' =>
        simp only [SimpleGraph.Walk.length_cons] at hp'
        omega

/-- **The underlying graph of a quiver tree is a tree.** -/
theorem isTree_quiverGraph [Nonempty V] (h : Work.ORBassSerre.IsTree V) :
    (quiverGraph V hnl).IsTree :=
  ⟨⟨preconnected_quiverGraph h⟩, isAcyclic_quiverGraph h⟩

/-- The action on the underlying graph preserves adjacency. -/
theorem quiverGraph_smul_adj {G : Type u} [Group G] [MulAction G V]
    [Work.ORBassSerre.GraphAction G V] (g : G) {a b : V}
    (h : (quiverGraph V hnl).Adj a b) : (quiverGraph V hnl).Adj (g • a) (g • b) :=
  h.elim fun e => ⟨Work.ORBassSerre.GraphAction.smulArrow g e⟩

end Induced

/-! ## Cocompactness -/

section Cocompact

variable {G : Type u} {V : Type v} [Group G] [Quiver V] [Quiver.HasInvolutiveReverse V]
  [MulAction G V] [Work.ORBassSerre.GraphAction G V]

/-- Two arrows of a quiver with subsingleton hom-types and the same source and target are
equal, as elements of `Quiver.Total`. -/
theorem total_ext (hsub : ∀ u v : V, Subsingleton (u ⟶ v)) {a b a' b' : V} (ha : a = a')
    (hb : b = b') (f : a ⟶ b) (g : a' ⟶ b') :
    (⟨a, b, f⟩ : Quiver.Total V) = ⟨a', b', g⟩ := by
  subst ha
  subst hb
  exact congrArg (fun e => (⟨a, b, e⟩ : Quiver.Total V)) (Subsingleton.elim f g)

/-- The oriented edge underlying an arrow. -/
def arrowToAdjPair (T : Work.ORDunwoody.GTree G V)
    (hAdj : ∀ u v : V, T.Adj u v ↔ Nonempty (u ⟶ v)) (e : Quiver.Total V) : T.AdjPair :=
  ⟨(e.left, e.right), (hAdj e.left e.right).mpr ⟨e.hom⟩⟩

/-- A chosen arrow of an oriented edge. -/
noncomputable def adjPairToArrow (T : Work.ORDunwoody.GTree G V)
    (hAdj : ∀ u v : V, T.Adj u v ↔ Nonempty (u ⟶ v)) (p : T.AdjPair) : Quiver.Total V :=
  ⟨p.1.1, p.1.2, Classical.choice ((hAdj p.1.1 p.1.2).mp p.2)⟩

theorem arrowToAdjPair_smul (T : Work.ORDunwoody.GTree G V)
    (hAdj : ∀ u v : V, T.Adj u v ↔ Nonempty (u ⟶ v)) (g : G) (e : Quiver.Total V) :
    arrowToAdjPair T hAdj (g • e) = g • arrowToAdjPair T hAdj e := by
  refine Subtype.ext (Prod.ext ?_ ?_)
  · dsimp only [arrowToAdjPair]
    exact Work.ORBassSerre.GraphAction.smul_left g e
  · dsimp only [arrowToAdjPair]
    exact Work.ORBassSerre.GraphAction.smul_right g e

theorem arrowToAdjPair_adjPairToArrow (T : Work.ORDunwoody.GTree G V)
    (hAdj : ∀ u v : V, T.Adj u v ↔ Nonempty (u ⟶ v)) (p : T.AdjPair) :
    arrowToAdjPair T hAdj (adjPairToArrow T hAdj p) = p :=
  Subtype.ext rfl

theorem adjPairToArrow_arrowToAdjPair (T : Work.ORDunwoody.GTree G V)
    (hAdj : ∀ u v : V, T.Adj u v ↔ Nonempty (u ⟶ v))
    (hsub : ∀ u v : V, Subsingleton (u ⟶ v)) (e : Quiver.Total V) :
    adjPairToArrow T hAdj (arrowToAdjPair T hAdj e) = e := by
  cases e with
  | mk a b f => exact total_ext hsub rfl rfl _ f

/-- **Cocompactness is the same in the two formalizations.**  If a `G`-tree `T` has the
adjacency relation of the underlying graph of a quiver, and there is at most one arrow
between any two vertices, then `T` is cocompact exactly when the quiver action is. -/
theorem isCocompact_iff_adjPair_total (T : Work.ORDunwoody.GTree G V)
    (hAdj : ∀ u v : V, T.Adj u v ↔ Nonempty (u ⟶ v))
    (hsub : ∀ u v : V, Subsingleton (u ⟶ v)) :
    T.IsCocompact ↔ Work.ORBassSerre.IsCocompact G V := by
  classical
  -- Every arrow orbit is hit by the chosen arrow of an oriented edge of a finite set of
  -- oriented edges meeting every edge orbit.
  have step1 : Finite (MulAction.orbitRel.Quotient G T.AdjPair) →
      Finite (MulAction.orbitRel.Quotient G (Quiver.Total V)) := by
    intro hfin
    haveI := hfin
    obtain ⟨s, hs⟩ : ∃ s : Finset T.AdjPair, ∀ v : T.AdjPair, ∃ g : G, g • v ∈ s :=
      exists_finset_of_finite_orbitQuotient
    refine finite_orbitQuotient_of_exists_finset (s.image (adjPairToArrow T hAdj))
      (fun e => ?_)
    obtain ⟨g, hg⟩ := hs (arrowToAdjPair T hAdj e)
    exact ⟨g, Finset.mem_image.mpr ⟨g • arrowToAdjPair T hAdj e, hg, by
      rw [← arrowToAdjPair_smul T hAdj g e]
      exact adjPairToArrow_arrowToAdjPair T hAdj hsub (g • e)⟩⟩
  -- Every oriented edge orbit is hit by the underlying oriented edge of an arrow of a finite
  -- set of arrows meeting every arrow orbit.
  have step2 : Finite (MulAction.orbitRel.Quotient G (Quiver.Total V)) →
      Finite (MulAction.orbitRel.Quotient G T.AdjPair) := by
    intro hfin
    haveI := hfin
    obtain ⟨s, hs⟩ : ∃ s : Finset (Quiver.Total V), ∀ v : Quiver.Total V, ∃ g : G,
      g • v ∈ s := exists_finset_of_finite_orbitQuotient
    refine finite_orbitQuotient_of_exists_finset (s.image (arrowToAdjPair T hAdj))
      (fun p => ?_)
    obtain ⟨g, hg⟩ := hs (adjPairToArrow T hAdj p)
    exact ⟨g, Finset.mem_image.mpr ⟨g • adjPairToArrow T hAdj p, hg, by
      rw [arrowToAdjPair_smul T hAdj g (adjPairToArrow T hAdj p),
        arrowToAdjPair_adjPairToArrow T hAdj p]⟩⟩
  exact ⟨fun h => ⟨h.1, step1 h.2⟩, fun h => ⟨h.1, step2 h.2⟩⟩

end Cocompact

/-! ## The main statement -/

/-- **The underlying graph of a quiver tree is a simplicial tree with the same cocompactness
behaviour.** -/
theorem ofQuiverTree {G : Type*} [Group G] {V : Type*} [Quiver V]
    [Quiver.HasInvolutiveReverse V] [MulAction G V] [Work.ORBassSerre.GraphAction G V]
    [Nonempty V] (h : Work.ORBassSerre.IsTree V) :
    ∃ T : Work.ORDunwoody.GTree G V,
      (∀ u v : V, T.Adj u v ↔ Nonempty (u ⟶ v)) ∧
      (T.IsCocompact ↔ Work.ORBassSerre.IsCocompact G V) := by
  classical
  have hnl : ∀ u : V, ¬ Nonempty (u ⟶ u) := noLoop_of_isTree h
  refine ⟨⟨quiverGraph V hnl, isTree_quiverGraph h, fun g a b hab => ?_⟩, ?_, ?_⟩
  · exact quiverGraph_smul_adj g hab
  · intro a b
    exact Iff.rfl
  · exact isCocompact_iff_adjPair_total _ (fun a b => Iff.rfl) (subsingleton_hom_of_isTree h)

end Work.ORDunwoody.Lemmas
