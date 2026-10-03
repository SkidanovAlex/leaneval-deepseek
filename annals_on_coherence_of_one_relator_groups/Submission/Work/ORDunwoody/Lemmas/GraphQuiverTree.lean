/-
Copyright: work of the ORDunwoody subproject (node N13).

# The edge quiver of a tree is a Bass--Serre tree

This file shows that the edge quiver `graphQuiver T.graph` of a `G`-tree `T`
(`Work.ORDunwoody.GTree`, i.e. a `SimpleGraph` tree with an adjacency preserving action) is a
Bass--Serre tree (`Work.ORBassSerre.IsTree`), that the `G`-action on the vertices extends to
an action on the quiver (`Work.ORBassSerre.GraphAction`), and that cocompactness of the two
notions agree.
-/
import Mathlib
import Submission.Work.ORDunwoody.Basic
import Submission.Work.ORBassSerre.Action.Basic
import Submission.Work.ORDunwoody.Lemmas.GraphQuiver
import Submission.Work.ORDunwoody.Lemmas.backtrackFreeWalk
import Submission.Work.ORBassSerre.Tree.Geodesic.qpath_eq_of_isTree

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.style.haveILetI false

universe u x

namespace Work.ORDunwoody.Lemmas

open SimpleGraph

variable {V : Type u}

/-- An equivariant equivalence of `G`-sets induces a bijection of the orbit sets. -/
theorem finite_orbitQuotient_congr {G : Type*} [Group G] {X Y : Type*} [MulAction G X]
    [MulAction G Y] (e : X ≃ Y) (he : ∀ (g : G) (x : X), e (g • x) = g • e x) :
    Finite (MulAction.orbitRel.Quotient G X) ↔ Finite (MulAction.orbitRel.Quotient G Y) := by
  have hmap : ∀ x x' : X, MulAction.orbitRel G X x x' → MulAction.orbitRel G Y (e x) (e x') := by
    intro x x' hxx'
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hxx' ⊢
    obtain ⟨g, hg⟩ := hxx'
    exact ⟨g, by rw [← he g x', hg]⟩
  have hmap' : ∀ y y' : Y,
      MulAction.orbitRel G Y y y' → MulAction.orbitRel G X (e.symm y) (e.symm y') := by
    intro y y' hyy'
    rw [MulAction.orbitRel_apply, MulAction.mem_orbit_iff] at hyy' ⊢
    obtain ⟨g, hg⟩ := hyy'
    refine ⟨g, ?_⟩
    have h1 : e.symm (g • y') = g • e.symm y' := by
      conv_lhs => rw [← Equiv.apply_symm_apply e y']
      rw [← he g (e.symm y'), Equiv.symm_apply_apply]
    rw [← h1, hg]
  constructor
  · intro hX
    exact Finite.of_surjective (Quotient.map e hmap) (by
      intro q
      refine Quotient.inductionOn q ?_
      intro y
      exact ⟨Quotient.mk _ (e.symm y), by rw [Quotient.map_mk, Equiv.apply_symm_apply]⟩)
  · intro hY
    exact Finite.of_surjective (Quotient.map e.symm hmap') (by
      intro q
      refine Quotient.inductionOn q ?_
      intro x
      exact ⟨Quotient.mk _ (e x), by rw [Quotient.map_mk, Equiv.symm_apply_apply]⟩)

/-- If the first two darts of a walk are mutually inverse, then its `walkToPath` is not
reduced. -/
theorem not_isReduced_walkToPath_cons_cons {G : SimpleGraph V} {u v z w : V} (h : G.Adj u v)
    (h' : G.Adj v z) (p : G.Walk z w)
    (hd : (⟨(v, z), h'⟩ : G.Dart) = (⟨(u, v), h⟩ : G.Dart).symm) :
    ¬ @Quiver.Path.IsReduced V (graphQuiver G) u w (graphQuiverHasReverse G)
      (walkToPath G (SimpleGraph.Walk.cons h (SimpleGraph.Walk.cons h' p))) := by
  letI : Quiver V := graphQuiver G
  letI : Quiver.HasReverse V := graphQuiverHasReverse G
  have hvu : z = u := by
    have h2 := congrArg (fun d : G.Dart => d.toProd.2) hd
    simpa [SimpleGraph.Dart.symm_mk] using h2
  subst hvu
  have heq : (ULift.up ⟨(), h'⟩ : @Quiver.Hom V (graphQuiver G) v z)
      = ULift.up ⟨(), h.symm⟩ := Subsingleton.elim _ _
  intro hred
  refine hred (walkToPath G p) ?_
  rw [walkToPath_cons', walkToPath_cons', heq]
  have hdbt := @Quiver.Path.DeleteBacktrack.intro V (graphQuiver G) (graphQuiverHasReverse G)
    z z v w (qnil G z) (ULift.up ⟨(), h⟩ : @Quiver.Hom V (graphQuiver G) z v) (walkToPath G p)
  simp only [Quiver.Path.nil_comp] at hdbt
  exact hdbt

/-- A walk with an immediate backtrack has a non-reduced `walkToPath`. -/
theorem not_isReduced_walkToPath_of_not_backtrackFree {G : SimpleGraph V} {a b : V}
    (w : G.Walk a b) (hw : ¬ w.BacktrackFree) :
    ¬ @Quiver.Path.IsReduced V (graphQuiver G) a b (graphQuiverHasReverse G) (walkToPath G w) := by
  letI : Quiver V := graphQuiver G
  letI : Quiver.HasReverse V := graphQuiverHasReverse G
  refine @SimpleGraph.Walk.rec V G (fun a b w => ¬ w.BacktrackFree →
      ¬ @Quiver.Path.IsReduced V (graphQuiver G) a b (graphQuiverHasReverse G) (walkToPath G w))
    ?_ ?_ a b w hw
  · intro u0 hw'
    exact absurd (SimpleGraph.Walk.backtrackFree_nil u0) hw'
  · intro u v w' h p ih hw'
    rw [SimpleGraph.Walk.BacktrackFree, SimpleGraph.Walk.darts_cons, List.isChain_cons] at hw'
    rcases not_and_or.mp hw' with hcase | hcase
    · -- the first two darts of the walk are mutually inverse
      have hcase' : ∃ y, y ∈ p.darts.head? ∧ y = (⟨(u, v), h⟩ : G.Dart).symm := by
        by_contra hc
        refine hcase (fun y hy hyy => ?_)
        exact hc ⟨y, hy, hyy⟩
      obtain ⟨y, hy, hny⟩ := hcase'
      cases p with
      | nil => simp at hy
      | cons h' p' =>
        rename_i zz
        have hy' : (⟨(v, zz), h'⟩ : G.Dart) = y := by simpa using hy
        have hd : (⟨(v, zz), h'⟩ : G.Dart) = (⟨(u, v), h⟩ : G.Dart).symm := hy'.trans hny
        exact not_isReduced_walkToPath_cons_cons h h' p' hd
    · -- the tail already has a backtrack
      have hnot := ih hcase
      intro hred
      obtain ⟨q', hq'⟩ : ∃ q', Quiver.Path.DeleteBacktrack (walkToPath G p) q' := by
        by_contra hc
        exact hnot (fun q' hq' => hc ⟨q', hq'⟩)
      exact hred _ (by
        rw [walkToPath_cons']
        exact Quiver.Path.DeleteBacktrack.comp_left hq' _)

/-- A reduced path has a backtrack free walk. -/
theorem SimpleGraph.Walk.backtrackFree_pathToWalk_of_qReduced {G : SimpleGraph V} {a b : V}
    (p : @Quiver.Path V (graphQuiver G) a b) (hp : qReduced G p) :
    (pathToWalk G p).BacktrackFree := by
  by_contra hw
  have hbad : ¬ @Quiver.Path.IsReduced V (graphQuiver G) a b (graphQuiverHasReverse G)
      (walkToPath G (pathToWalk G p)) :=
    not_isReduced_walkToPath_of_not_backtrackFree (pathToWalk G p) hw
  rw [walkToPath_pathToWalk] at hbad
  exact hbad hp

/-- The edge quiver of a `G`-tree is a Bass--Serre tree. -/
theorem graphQuiver_isTree {G : Type*} [Group G] {V : Type*} [MulAction G V]
    (T : Work.ORDunwoody.GTree G V) :
    @Work.ORBassSerre.IsTree V (graphQuiver T.graph) (graphQuiverHasInvolutiveReverse T.graph) := by
  letI : Quiver V := graphQuiver T.graph
  letI : Quiver.HasReverse V := graphQuiverHasReverse T.graph
  letI : Quiver.HasInvolutiveReverse V := graphQuiverHasInvolutiveReverse T.graph
  refine ⟨fun a b => ?_, fun a p hp => ?_⟩
  · obtain ⟨w⟩ := T.isTree.connected.preconnected a b
    exact ⟨walkToPath T.graph w⟩
  · have hbf : (pathToWalk T.graph p).BacktrackFree :=
      SimpleGraph.Walk.backtrackFree_pathToWalk_of_qReduced p hp
    have hnil := walk_eq_nil_of_backtrackFree_of_isAcyclic (pathToWalk T.graph p)
      T.isTree.isAcyclic hbf
    exact (pathToWalk_eq_nil_iff T.graph p).mp hnil

/-- Cocompactness of a `G`-tree agrees with cocompactness of its edge quiver. -/
theorem graphQuiver_isCocompact_iff {G : Type*} [Group G] {V : Type*} [MulAction G V]
    (T : Work.ORDunwoody.GTree G V) :
    @Work.ORBassSerre.IsCocompact G V _ (graphQuiver T.graph) (graphQuiverHasReverse T.graph) _
        (graphQuiverAction T) ↔ T.IsCocompact := by
  letI : Quiver V := graphQuiver T.graph
  letI : Quiver.HasReverse V := graphQuiverHasReverse T.graph
  letI : Work.ORBassSerre.GraphAction G V := graphQuiverAction T
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (finite_orbitQuotient_congr (totalEquivAdjPair T)
      (fun g e => totalEquivAdjPair_smul T (graphQuiverAction T) g e)).mp h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, (finite_orbitQuotient_congr (totalEquivAdjPair T)
      (fun g e => totalEquivAdjPair_smul T (graphQuiverAction T) g e)).mpr h2⟩

end Work.ORDunwoody.Lemmas
