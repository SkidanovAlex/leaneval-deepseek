/-
# The cyclic cover of a staggered presentation (Howie 2000, Case 1 of Theorem 3.1)

This file sets up the *combinatorial* part of Howie's Case 1.  Given a presentation `P` of a
groupoid by a graph `Γ` and a labelling `θ : E(Γ) → ℤ` (a `Labelling V`) which is *zero on the
relators*, the cyclic cover `Γ̃` (`CoverGraph.lean`) has vertex set `V × ℤ` and arrows `(e, n)`, and
every relator lifts to a *closed* path `coverPath P L hrel i n` at level `n`.

The graph `Γ̃` carries a linear ordering of its *unoriented edges*: an edge of the cover is a pair
`{(e, n), (e⁻¹, n + θ e)}`, and its code is

    `coverEdgeOf P L τ (e, n) := (ω e, n + τ e)`,

where `ω` is the code of the edge of `Γ` and `τ` is a section of the level cocycle
(`τ (e⁻¹) = τ e - θ e`); this makes the code constant on `{(e,n), (e,n)⁻¹}`, as required by the
`Presentation` machinery.  The lifted presentation `⟨Γ̃ | R̃⟩` (`R̃ = {coverPath i n}`) is again
staggered for this code, with the lexicographic order on the relators `(i, n)`; that is Howie's
Case 1, and it is proved on top of this file.

We also define `coverProjPath`, the projection of a path of the cover to the base graph, together
with its basic API.
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverGraph
import Submission.Work.ORLocInd.Howie.Relator
import Submission.Work.ORLocInd.Howie.liftPath_arrowList

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

section PathLists

/-- Casting a path along equalities of its endpoints does not change its arrow list, up to the
projection `g`. -/
theorem Quiver.Path.arrowList_cast_map {β : Type*} (g : Quiver.Total V → β) {u v u' v' : V}
    (hu : u = u') (hv : v = v') (p : Quiver.Path u v) :
    ((p.cast hu hv).arrowList).map g = p.arrowList.map g := by
  cases hu; cases hv
  rw [Quiver.Path.cast_rfl_rfl]

end PathLists

/-- Extensionality for the vertices of the cyclic cover. -/
theorem CoverVertex.ext {L : Labelling V} {p q : CoverVertex L} (h1 : p.vert = q.vert)
    (h2 : p.level = q.level) : p = q := by
  cases p; cases q; simp_all

/-- A labelling of `Γ` is *zero on the relators* of `P` when the level of every relator is `0`;
this is the condition under which the relators lift to *closed* paths of the cyclic cover. -/
def VanishOnRelators (L : Labelling V) (P : Presentation V) : Prop :=
  ∀ i : P.ι, pathSum L.toFun (P.path i) = 0

/-- The relators of the lifted presentation: a relator of `P` together with a level, ordered
lexicographically (`Lex (P.ι × ℤ)`). -/
def CoverRelator (P : Presentation V) : Type u := Lex (P.ι × ℤ)

/-- The code of an unoriented edge of the lifted presentation, valued in `Lex (P.α × ℤ)` (the code
of the projected edge, refined lexicographically by the level of the source translated by the
section `τ`). -/
def CoverCode (P : Presentation V) : Type u := Lex (P.α × ℤ)

instance coverRelatorLinearOrder (P : Presentation V) : LinearOrder (CoverRelator P) :=
  inferInstanceAs (LinearOrder (Lex (P.ι × ℤ)))

instance coverCodeLinearOrder (P : Presentation V) : LinearOrder (CoverCode P) :=
  inferInstanceAs (LinearOrder (Lex (P.α × ℤ)))

/-- The relator `i` of `P`, lifted to the cyclic cover as a closed path at level `n`. -/
noncomputable def coverPath (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (i : P.ι) (n : ℤ) :
    Quiver.Path (⟨P.base i, n⟩ : CoverVertex L) ⟨P.base i, n⟩ := by
  have hlevel : (⟨P.base i, n + pathSum L.toFun (P.path i)⟩ : CoverVertex L) =
      ⟨P.base i, n⟩ :=
    CoverVertex.ext rfl (by rw [hrel i, add_zero])
  exact Quiver.Path.cast rfl hlevel (liftPath L (P.path i) n)

theorem coverPath_arrowList (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (i : P.ι) (n : ℤ) :
    (coverPath P L hrel i n).arrowList.map (fun f => f.hom.1) = (P.path i).arrowList := by
  rw [coverPath]
  rw [Quiver.Path.arrowList_cast_map]
  exact liftPath_arrowList L (P.path i) n

/-- The code of an unoriented edge of the cyclic cover. -/
noncomputable def coverEdgeOf (P : Presentation V) (L : Labelling V)
    (τ : Quiver.Total V → ℤ) : Quiver.Total (CoverVertex L) → CoverCode P :=
  fun f => toLex (P.edgeOf f.hom.1, f.left.level + τ f.hom.1)

/-- The projection of a path of the cyclic cover to the base graph. -/
def coverProjPath (L : Labelling V) (p : CoverVertex L) :
    ∀ {q : CoverVertex L}, Quiver.Path p q → Quiver.Path p.vert q.vert
  | _, .nil => .nil
  | _, .cons P e => (coverProjPath L p P).cons (coverProjArrow e)

theorem coverProjPath_nil (L : Labelling V) (p : CoverVertex L) :
    coverProjPath L p (Quiver.Path.nil : Quiver.Path p p) = Quiver.Path.nil := rfl

theorem coverProjPath_cons (L : Labelling V) {p q r : CoverVertex L} (P : Quiver.Path p q)
    (e : q ⟶ r) :
    coverProjPath L p (P.cons e) = (coverProjPath L p P).cons (coverProjArrow e) := rfl

/-- The projection of the total space: an arrow of the cover, viewed through the projection, is the
underlying total arrow of the base graph. -/
theorem homOfEq_heq {X Y X' Y' : V} (f : X ⟶ Y) (hX : X = X') (hY : Y = Y') :
    HEq (Quiver.homOfEq f hX hY) f := by
  cases hX; cases hY
  rw [show Quiver.homOfEq f rfl rfl = f from rfl]

theorem coverProjArrow_total (L : Labelling V) {p q : CoverVertex L} (e : p ⟶ q) :
    Quiver.Total.mk p.vert q.vert (coverProjArrow e) = e.1 := by
  obtain ⟨f, h1, h2, h3⟩ := e
  refine Quiver.Total.ext h1.symm h2.symm ?_
  exact homOfEq_heq f.hom h1 h2

theorem coverProjPath_comp (L : Labelling V) {p q r : CoverVertex L} (P : Quiver.Path p q)
    (Q : Quiver.Path q r) :
    coverProjPath L p (P.comp Q) = (coverProjPath L p P).comp (coverProjPath L q Q) := by
  induction Q with
  | nil => rw [Quiver.Path.comp_nil, coverProjPath_nil, Quiver.Path.comp_nil]
  | cons Q e ih =>
      rw [Quiver.Path.comp_cons, coverProjPath_cons, ih, coverProjPath_cons, Quiver.Path.comp_cons]

theorem coverProjPath_compPower (L : Labelling V) {u : CoverVertex L} (q : Quiver.Path u u)
    (m : ℕ) :
    coverProjPath L u (Quiver.Path.compPower q m) =
      Quiver.Path.compPower (coverProjPath L u q) m := by
  induction m with
  | zero => rw [Quiver.Path.compPower_zero, coverProjPath_nil, Quiver.Path.compPower_zero]
  | succ m ih =>
      rw [Quiver.Path.compPower_succ, Quiver.Path.compPower_succ, coverProjPath_comp, ih]

theorem coverProjPath_arrowList (L : Labelling V) {p q : CoverVertex L} (P : Quiver.Path p q) :
    (coverProjPath L p P).arrowList = P.arrowList.map (fun f => f.hom.1) := by
  induction P with
  | nil => rw [coverProjPath_nil]; rfl
  | cons P e ih =>
      rw [coverProjPath_cons, Quiver.Path.arrowList_cons, ih, Quiver.Path.arrowList_cons,
        List.map_append, List.map_cons, List.map_nil, ← coverProjArrow_total L e]

end Work.ORLocInd.Howie
