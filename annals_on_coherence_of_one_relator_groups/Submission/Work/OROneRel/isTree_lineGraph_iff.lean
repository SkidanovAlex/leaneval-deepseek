import Mathlib
import Submission.Work.OROneRel.bandLineGraphDefs
import Submission.Work.OROneRel.cosetGraph_lineGraph_iso
import Submission.Work.OROneRel.graded_hnn_coset
import Submission.Work.ORBassSerre.Tree.Basic
import Submission.Work.ORBassSerre.Tree.IsTreeAPI
import Submission.Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.OROneRel

open Quiver

universe u

/-! ## Generalities: tree-ness is an isomorphism invariant of quivers

Both the coset graph `GradedHNN.Coset H t` and the line graph `lineVertex H t φ hH` carry the
"proof-irrelevant" quiver structure: the arrows `x ⟶ y` are `PLift` of a proposition (the adjacency
relation).  Consequently a bijection on vertices which matches up the two adjacency relations
upgrades to a pair of mutually inverse prefunctors, and `IsTree` transports. -/

section General

variable {V : Type u} {W : Type u}

/-- A prefunctor preserves the length of a path. -/
theorem qprefunctor_mapPath_length [Quiver V] [Quiver W] (F : V ⥤q W) {a b : V}
    (p : Quiver.Path a b) : (F.mapPath p).length = p.length := by
  induction p with
  | nil => rfl
  | cons p e ih =>
      rw [Prefunctor.mapPath_cons, Quiver.Path.length_cons, Quiver.Path.length_cons, ih]

/-- **Tree-ness is an isomorphism invariant of quivers.**

If `F : V ⥤q W` and `G : W ⥤q V` are mutually inverse on vertices (`hFG`, `hGF`), injective on
objects and on arrows, and both preserve reversal, then `V` is a tree exactly when `W` is.

The forward implication pushes a path across by `F` (and its reverse across by `G`), the backward one
by `G` (and its reverse by `F`); reducedness is preserved by `qpath_mapPath_isReduced` and a reduced
closed path mapped to the trivial path has length `0`, hence is trivial. -/
theorem isTree_iff_of_prefunctors [Quiver V] [Quiver.HasInvolutiveReverse V]
    [Quiver W] [Quiver.HasInvolutiveReverse W]
    (F : V ⥤q W) [F.MapReverse] (G : W ⥤q V) [G.MapReverse]
    (hinjF : Function.Injective F.obj)
    (hinjF' : ∀ ⦃x y : V⦄, Function.Injective (fun e : x ⟶ y => F.map e))
    (hinjG : Function.Injective G.obj)
    (hinjG' : ∀ ⦃x y : W⦄, Function.Injective (fun e : x ⟶ y => G.map e))
    (hFG : ∀ y, F.obj (G.obj y) = y) (hGF : ∀ x, G.obj (F.obj x) = x) :
    Work.ORBassSerre.IsTree V ↔ Work.ORBassSerre.IsTree W := by
  constructor
  · rintro ⟨hconn, hacyc⟩
    refine ⟨?_, ?_⟩
    · intro x y
      obtain ⟨p⟩ := hconn (G.obj x) (G.obj y)
      exact ⟨(F.mapPath p).cast (hFG x) (hFG y)⟩
    · intro x q hq
      have hred : (G.mapPath q).IsReduced :=
        Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced G hinjG hinjG' hq
      have hnil : G.mapPath q = Quiver.Path.nil := hacyc (G.obj x) _ hred
      have hlen : q.length = 0 := by
        have h := qprefunctor_mapPath_length G q
        rw [hnil] at h
        simpa using h.symm
      exact Quiver.Path.eq_nil_of_length_zero q hlen
  · rintro ⟨hconn, hacyc⟩
    refine ⟨?_, ?_⟩
    · intro x y
      obtain ⟨p⟩ := hconn (F.obj x) (F.obj y)
      exact ⟨(G.mapPath p).cast (hGF x) (hGF y)⟩
    · intro x q hq
      have hred : (F.mapPath q).IsReduced :=
        Work.ORBassSerre.Tree.Map.qpath_mapPath_isReduced F hinjF hinjF' hq
      have hnil : F.mapPath q = Quiver.Path.nil := hacyc (F.obj x) _ hred
      have hlen : q.length = 0 := by
        have h := qprefunctor_mapPath_length F q
        rw [hnil] at h
        simpa using h.symm
      exact Quiver.Path.eq_nil_of_length_zero q hlen

end General

/-- **The tree property transports along the reduction `cosetGraph_lineGraph_iso`.**

The coset graph of `(H, t)` (vertices `G ⧸ H`, edges `{gH, gtH}`) and the line graph of the chain
of conjugates of `H` in `ker φ` are isomorphic as quivers (with proof-irrelevant labels), so one is
`Work.ORBassSerre.IsTree` if and only if the other is.  Consequently
`Work.OROneRel.band_cosetGraph_isTree` is *equivalent* to the statement that the line graph of the
band chain is a tree. -/
theorem isTree_lineGraph_iff {G : Type u} [Group G] (H : Subgroup G) (t : G)
    (φ : G →* Multiplicative ℤ) (hH : H ≤ φ.ker) (ht : φ t = Multiplicative.ofAdd 1) :
    Work.ORBassSerre.IsTree (Work.OROneRel.GradedHNN.Coset H t) ↔
      Work.ORBassSerre.IsTree (Work.OROneRel.lineVertex H t φ hH) := by
  classical
  obtain ⟨e, he⟩ := cosetGraph_lineGraph_iso H t φ hH ht
  let F : GradedHNN.Coset H t ⥤q lineVertex H t φ hH :=
    ⟨e, fun {x y} f => ⟨(he x y).mp f.down⟩⟩
  let G' : lineVertex H t φ hH ⥤q GradedHNN.Coset H t :=
    ⟨e.symm, fun {x y} f => ⟨(he (e.symm x) (e.symm y)).mpr (by simpa using f.down)⟩⟩
  have hFrev : F.MapReverse := ⟨fun {_ _} _ => Subsingleton.elim _ _⟩
  have hGrev : G'.MapReverse := ⟨fun {_ _} _ => Subsingleton.elim _ _⟩
  have hFG : ∀ y, F.obj (G'.obj y) = y := fun y => e.apply_symm_apply y
  have hGF : ∀ x, G'.obj (F.obj x) = x := fun x => e.symm_apply_apply x
  refine isTree_iff_of_prefunctors F G' e.injective ?_ e.symm.injective ?_ hFG hGF
  · intro x y a b _
    exact Subsingleton.elim a b
  · intro x y a b _
    exact Subsingleton.elim a b

end Work.OROneRel
