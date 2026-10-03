/-
# The lifted relators of the cyclic cover are reduced, cyclically reduced, and not proper powers

Howie's Case 1 (`Submission.Work.ORLocInd.Howie.CoverPresentation`) lifts a staggered presentation
`⟨Γ | R⟩` with a labelling `L` vanishing on the relators to the cyclic cover `Γ̃`, whose relators
are the closed paths `coverPath P L hrel i n` (the lift of `P.path i` through the level `n`).

For the lifted presentation to be a `Presentation` again (as the Case 1 step requires) one needs
that each lifted relator is reduced, cyclically reduced, and not a proper power.  This file proves
exactly that.

The whole file rests on the *projection* `coverProjPath` of a path of the cover to the base graph:

* `coverProjPath_liftPath` : the projection of the lift of a path is the path itself;
* `coverProjPath_coverPath` : the projection of a lifted relator is the relator;
* `coverProjArrow_reverse` : the projection commutes with reversal of arrows.

Since a projected cyclic decomposition of the lift is a cyclic decomposition of the relator, and a
projected proper-power decomposition of the lift is a proper-power decomposition of the relator,
the corresponding properties are inherited from `P`.  (In particular the "no self-inverse loop in
the cover" hypothesis `hns` of `coverPath_properties` is not needed for these three properties:
the projection argument never has to distinguish a one-arrow cycle.)
-/
import Mathlib
import Submission.Work.ORLocInd.Howie.CoverPresentation
import Submission.Work.ORLocInd.Howie.liftPath_isReduced
import Submission.Work.ORLocInd.Howie.isReduced_compPower_of_comp_self

set_option autoImplicit false
set_option linter.unusedVariables false

universe u

namespace Work.ORLocInd.Howie

open Quiver

variable {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]

/-! ## Casting paths along equalities of their endpoints -/

/-- Casting a path along two equalities of its endpoints with themselves does not change it (the
equality proofs are irrelevant, so both casts may be replaced by `rfl`). -/
theorem path_cast_self {U : Type*} [Quiver U] {u v : U} (p : Quiver.Path u v)
    (hu : u = u) (hv : v = v) : p.cast hu hv = p := by
  rw [show hu = rfl from Subsingleton.elim hu rfl, show hv = rfl from Subsingleton.elim hv rfl,
    Quiver.Path.cast_rfl_rfl]

/-! ## The projection of a path of the cyclic cover -/

/-- `coverProjPath` is compatible with casting the target of a path of the cover: casting the path
and then projecting is the same as projecting and then casting (the base vertices of a cast path
are the casts of the base vertices). -/
theorem coverProjPath_cast_right (L : Labelling V) {u v v' : CoverVertex L} (hv : v = v')
    (p : Quiver.Path u v) :
    coverProjPath L u (p.cast rfl hv) =
      (coverProjPath L u p).cast rfl (congrArg CoverVertex.vert hv) := by
  cases hv
  simp

/-- The projection of the singleton path of an arrow of the cover is the singleton path of the
projected arrow. -/
theorem coverProjPath_toPath (L : Labelling V) {u v : CoverVertex L} (e : u ⟶ v) :
    coverProjPath L u e.toPath = (coverProjArrow e).toPath := rfl

/-- **The projection of the lift of a path is the path itself.** -/
theorem coverProjPath_liftPath (L : Labelling V) {a b : V} (p : Quiver.Path a b) (n : ℤ) :
    coverProjPath L (⟨a, n⟩ : CoverVertex L) (liftPath L p n) = p := by
  induction p with
  | nil =>
    rw [liftPath_nil_cast']
    rw [coverProjPath_cast_right]
    rw [coverProjPath_nil]
    exact path_cast_self _ _ _
  | cons p e ih =>
    rw [liftPath_cons_cast']
    rw [coverProjPath_cast_right]
    rw [coverProjPath_cons]
    rw [ih]
    rw [coverProjArrow_coverLiftArrow]
    exact path_cast_self _ _ _

/-- **The projection of a lifted relator is the relator.**  This is the identity that transfers
every path-theoretic property of a relator to its lift: the two cyclic-cover bookkeeping casts
(the level bookkeeping of `liftPath` and the closing cast of `coverPath`, along
`pathSum L (P.path i) = 0`) disappear under the projection. -/
theorem coverProjPath_coverPath (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (i : P.ι) (n : ℤ) :
    coverProjPath L (⟨P.base i, n⟩ : CoverVertex L) (coverPath P L hrel i n) = P.path i := by
  rw [coverPath, coverProjPath_cast_right, coverProjPath_liftPath]
  exact path_cast_self _ _ _

/-! ## Reversal -/

/-- Reversal commutes with the transport of an arrow along equalities of its endpoints. -/
theorem reverse_homOfEq {U : Type*} [Quiver U] [Quiver.HasReverse U] {X Y X' Y' : U}
    (f : X ⟶ Y) (hX : X = X') (hY : Y = Y') :
    Quiver.reverse (Quiver.homOfEq f hX hY) = Quiver.homOfEq (Quiver.reverse f) hY hX := by
  subst hX
  subst hY
  rw [Quiver.homOfEq_rfl, Quiver.homOfEq_rfl]

/-- The projection of the cyclic cover commutes with reversal of arrows. -/
theorem coverProjArrow_reverse (L : Labelling V) {p q : CoverVertex L} (f : p ⟶ q) :
    coverProjArrow (Quiver.reverse f) = Quiver.reverse (coverProjArrow f) := by
  unfold coverProjArrow
  rw [reverse_homOfEq]
  rfl

/-! ## The three properties of a lifted relator -/

/-- A lifted relator is reduced. -/
theorem isReduced_coverPath (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (i : P.ι) (n : ℤ) :
    (coverPath P L hrel i n).IsReduced := by
  rw [coverPath]
  exact (isReduced_cast rfl _ _).2 (liftPath_isReduced L (P.path i) (P.reduced i) n)

/-- A lifted relator is cyclically reduced: a cyclic decomposition of the lift would project to a
cyclic decomposition of the relator. -/
theorem isCyclicallyReduced_coverPath (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (i : P.ι) (n : ℤ) :
    IsCyclicallyReduced (coverPath P L hrel i n) := by
  rintro ⟨u, e, q, hq⟩
  refine P.cyclicallyReduced i ⟨u.vert, coverProjArrow e, coverProjPath L u q, ?_⟩
  have h := congrArg (coverProjPath L (⟨P.base i, n⟩ : CoverVertex L)) hq
  rw [coverProjPath_coverPath] at h
  rw [coverProjPath_comp, coverProjPath_toPath, coverProjPath_cons, coverProjArrow_reverse] at h
  exact h

/-- A lifted relator is not a proper power: a proper-power decomposition of the lift would project
to a proper-power decomposition of the relator. -/
theorem not_isProperPower_coverPath (P : Presentation V) (L : Labelling V)
    (hrel : VanishOnRelators L P) (i : P.ι) (n : ℤ) :
    ¬ IsProperPower (coverPath P L hrel i n) := by
  rintro ⟨q, m, hm, hq⟩
  refine P.notProperPower i ⟨coverProjPath L (⟨P.base i, n⟩ : CoverVertex L) q, m, hm, ?_⟩
  have h := congrArg (coverProjPath L (⟨P.base i, n⟩ : CoverVertex L)) hq
  rw [coverProjPath_coverPath, coverProjPath_compPower] at h
  exact h

theorem coverPath_properties {V : Type u} [Quiver V] [Quiver.HasInvolutiveReverse V]
    (P : Work.ORLocInd.Howie.Presentation V) (L : Work.ORLocInd.Howie.Labelling V)
    (hrel : Work.ORLocInd.Howie.VanishOnRelators L P)
    (hns : ∀ (u : Work.ORLocInd.Howie.CoverVertex L) (f : u ⟶ u), Quiver.reverse f ≠ f)
    (i : P.ι) (n : ℤ) :
    (Work.ORLocInd.Howie.coverPath P L hrel i n).IsReduced ∧
      Work.ORLocInd.Howie.IsCyclicallyReduced (Work.ORLocInd.Howie.coverPath P L hrel i n) ∧
      ¬ Work.ORLocInd.Howie.IsProperPower (Work.ORLocInd.Howie.coverPath P L hrel i n) :=
  ⟨isReduced_coverPath P L hrel i n, isCyclicallyReduced_coverPath P L hrel i n,
    not_isProperPower_coverPath P L hrel i n⟩

end Work.ORLocInd.Howie
