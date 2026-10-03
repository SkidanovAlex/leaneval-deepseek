/-
# The projection of a reduced path of the cyclic cover is reduced

The cyclic cover `Γ̃` of a `ℤ`-labelled graph `Γ` (`Submission.Work.ORLocInd.Howie.CoverGraph`)
has vertex set `V × ℤ`, an arrow `(e, n) : (a, n) → (b, n + θ e)` for every arrow `e : a → b` of
`Γ`, and reversal `(e, n)⁻¹ = (e⁻¹, n + θ e)`.  The projection `coverProjPath` sends a path of
`Γ̃` to the path of `Γ` obtained by forgetting the levels.

This file proves `coverProjPath_isReduced`: **the projection of a reduced path is reduced**.  This
is the converse of `liftPath_isReduced` (a reduced path of the base lifts to a reduced path of the
cover) and is exactly the statement needed to transfer reducedness of paths in the cyclic cover
back to the base graph.

The proof is the natural one: a backtrack of the projection corresponds to a backtrack of the
original path.  Two ingredients are needed.

* `exists_endsWith_lift` : the *last* arrow of a path of the cover projects to the last arrow of
  its projection (the two `cons` decompositions are matched by `Quiver.Path.cons.inj`).  This
  produces the last arrow `g` of `P'` together with the base last arrow `f` of the projection.
* `coverProjArrow_injective` : on arrows with the same source and target of the cover, the
  projection is injective (a cover arrow is a base total arrow subject to a *level* condition,
  and both the source and the target of a cover arrow are determined by the base arrow once the
  source is fixed).

The only bookkeeping is the *level* of the source of `g`: it is forced to equal the level of the
target `q` of the arrow `e` closing the path, which is what makes `g` an arrow with source `q`
rather than merely an arrow with source `y` of the same vertex as `q`.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverPresentation
import Submission.Work.ORLocInd.Howie.coverPath_properties

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## Bookkeeping for `Quiver.Total` -/

/-- The `Total` arrow with source `X` and underlying hom `homOfEq f hX rfl` is the transport of the
`Total` arrow with source `X'`.  This is the identity that lets one compare `Total` arrows whose
sources differ along an equality. -/
theorem total_mk_homOfEq {X X' Y : V} (f : X ⟶ Y) (hX : X = X') :
    Quiver.Total.mk X Y f = Quiver.Total.mk X' Y (Quiver.homOfEq f hX rfl) :=
  Quiver.Total.ext hX rfl (Quiver.homOfEq_heq hX rfl f).symm

/-! ## Injectivity of the projection on arrows with the same source and target -/

/-- Two arrows of the cover with the same source and target and the same projection are equal: a
cover arrow is the data of a base total arrow subject to a level condition, and both source and
target of a cover arrow are determined by the base arrow together with the source. -/
theorem coverProjArrow_injective {L : Labelling V} {p q : CoverVertex L} {f g : p ⟶ q}
    (h : coverProjArrow f = coverProjArrow g) : f = g := by
  apply Subtype.ext
  rw [← coverProjArrow_total L f, ← coverProjArrow_total L g, h]

/-! ## The last arrow of a path of the cover -/

/-- **The last arrow of a path of the cover projects to the last arrow of its projection.**  More
precisely, if a base arrow `f` ends the projection of `P`, then there is an arrow `g` of the cover
ending `P`, with `g`'s source of the same vertex as `f`'s source, and whose projection is `f`.

The proof is immediate: the decomposition of the projection supplied by `EndsWith` has the same
last arrow as the `cons` decomposition of `P`, by `Quiver.Path.cons.inj`. -/
theorem exists_endsWith_lift {L : Labelling V} {p a : CoverVertex L} (P : Quiver.Path p a)
    {b : V} {f : b ⟶ a.vert} (h : Quiver.Path.EndsWith (coverProjPath L p P) f) :
    ∃ (y : CoverVertex L) (hy : y.vert = b) (g : y ⟶ a),
      Quiver.Path.EndsWith P g ∧ HEq (coverProjArrow g) f := by
  cases P with
  | nil =>
      rw [coverProjPath_nil] at h
      exact absurd h (Quiver.Path.not_endsWith_nil f)
  | cons P' g₀ =>
      rw [coverProjPath_cons] at h
      obtain ⟨P₁, hP₁⟩ := h
      obtain ⟨hmid, -, harrow⟩ := Quiver.Path.cons.inj hP₁
      exact ⟨_, hmid, g₀, Quiver.Path.endsWith_cons P' g₀, harrow⟩

/-! ## The induction step -/

/-- The `cons` step of `coverProjPath_isReduced`.  Given `P = P'.cons e` reduced in the cover, the
projection `(coverProjPath L p P').cons (coverProjArrow e)` is reduced: the induction hypothesis
deals with the prefix, and a backtrack at the join would give an arrow `g` of the cover ending `P'`
with `e = reverse g`.

The source of this `g` is `y`; the base arrow `f` ending the projection of `P'` satisfies
`f = coverProjArrow g` (up to the transport along `y.vert = q.vert`), so `coverProjArrow e =
reverse f` says precisely that `coverProjArrow (reverse g) = coverProjArrow e`.  The level of `y`
is then forced: `coverProjArrow e = reverse f` says that the label of `e` is `- L f`, i.e. the
label of `reverse g`, and hence `y` has the same level as `q`, so `y = q` and injectivity of the
projection gives `reverse g = e`, contradicting the reducedness of `P'.cons e`. -/
theorem coverProjPath_cons_isReduced {L : Labelling V} {p mid q : CoverVertex L}
    (P' : Quiver.Path p mid) (e : mid ⟶ q)
    (ih : P'.IsReduced → (coverProjPath L p P').IsReduced)
    (h : (P'.cons e).IsReduced) :
    (coverProjPath L p (P'.cons e)).IsReduced := by
  rw [coverProjPath_cons]
  obtain ⟨h', hlast⟩ := isReduced_cons_iff.mp h
  refine isReduced_cons_iff.mpr ⟨ih h', ?_⟩
  intro f hf he
  -- `f : q.vert ⟶ mid.vert`, `hf : EndsWith (coverProjPath L p P') f`,
  -- `he : coverProjArrow e = reverse f`.
  obtain ⟨y, hy, g, hgend, hge⟩ := exists_endsWith_lift P' hf
  -- `g : y ⟶ mid`, `hy : y.vert = q.vert`, `hgend : EndsWith P' g`,
  -- `hge : HEq (coverProjArrow g) f`.
  have hlev : y.level = q.level := by
    have h1 : mid.level = y.level + L g.1 := g.2.2.2
    have h2 : q.level = mid.level + L e.1 := e.2.2.2
    have hg1 : g.1 = Quiver.Total.mk q.vert mid.vert f := by
      rw [← coverProjArrow_total L g, total_mk_homOfEq (coverProjArrow g) hy]
      congr 1
      exact eq_of_heq ((Quiver.homOfEq_heq hy rfl (coverProjArrow g)).trans hge)
    have he1 : L e.1 = - L (Quiver.Total.mk q.vert mid.vert f) := by
      rw [← coverProjArrow_total L e, he, ← Quiver.totalReverse_mk]
      exact L.apply_totalReverse (Quiver.Total.mk q.vert mid.vert f)
    rw [hg1] at h1
    rw [he1] at h2
    omega
  have hyq : y = q := CoverVertex.ext hy hlev
  subst hyq
  have hge' : coverProjArrow g = f := eq_of_heq hge
  have hthis : coverProjArrow (Quiver.reverse g) = coverProjArrow e := by
    rw [coverProjArrow_reverse, hge', ← he]
  have hrev : Quiver.reverse g = e := coverProjArrow_injective hthis
  exact hlast g hgend hrev.symm

/-- **The projection of a reduced path of the cyclic cover is reduced.** -/
theorem coverProjPath_isReduced {V : Type*} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (L : Work.ORLocInd.Howie.Labelling V) {p q : Work.ORLocInd.Howie.CoverVertex L}
    (P : Quiver.Path p q) (h : P.IsReduced) :
    (Work.ORLocInd.Howie.coverProjPath L p P).IsReduced := by
  revert h
  induction P with
  | nil =>
      intro _
      rw [coverProjPath_nil]
      exact Quiver.Path.IsReduced.nil _
  | cons P' e ih =>
      intro h
      exact coverProjPath_cons_isReduced P' e ih h

end Work.ORLocInd.Howie
