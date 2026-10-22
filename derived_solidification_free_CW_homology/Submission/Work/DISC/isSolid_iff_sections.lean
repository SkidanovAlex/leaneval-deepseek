import Mathlib
import Submission.Work.DISC.Defs

/-!
# AREA DISC — solidity is detected on sections

A light condensed abelian group `A` is solid iff the endomorphism `(1 - shift)^*` of the internal
hom `A^P` (`P = ℤ[ℕ∪{∞}]/ℤ[∞]`) is invertible.  Here we observe that invertibility of a morphism
of light condensed abelian groups may be tested on its sections at light profinite sets: the
forgetful functor from sheaves of `ℤ`-modules on `LightProfinite` to presheaves reflects
isomorphisms (it is fully faithful), and a natural transformation of presheaves is invertible as
soon as all of its components are.

Consequently solidity of `A` is equivalent to: for every light profinite set `S`, the induced
endomorphism of `A^P(S)` is bijective.
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed OnePoint
open _root_.LightCondensed _root_.LightCondensed.Solid
open Opposite

noncomputable section

namespace Work.DISC

/-- A morphism of light condensed abelian groups is an isomorphism if and only if all of its
components on sections (at light profinite sets) are isomorphisms. -/
lemma isIso_iff_isIso_sections {A B : LightCondAb} (f : A ⟶ B) :
    CategoryTheory.IsIso f ↔
      ∀ S : LightProfinite.{0}, CategoryTheory.IsIso (f.hom.app (op S)) := by
  rw [← CategoryTheory.isIso_iff_of_reflects_iso f
        (sheafToPresheaf (coherentTopology LightProfinite) (ModuleCat ℤ))]
  rw [NatTrans.isIso_iff_isIso_app]
  exact ⟨fun h S => h (op S), fun h X => h X.unop⟩

/-- **Solidity is detected on sections**: `A` is solid iff `(1 - shift)^*` is invertible on
sections of `A^P` at every light profinite set. -/
theorem isSolid_iff_sections (A : LightCondAb) :
    LightCondensed.isSolid A ↔
      ∀ S : LightProfinite.{0},
        CategoryTheory.IsIso ((Work.DISC.oneMinusShiftStar A).hom.app (Opposite.op S)) := by
  simpa only [LightCondensed.isSolid, ObjectProperty.Is, Work.DISC.oneMinusShiftStar]
    using isIso_iff_isIso_sections (Work.DISC.oneMinusShiftStar A)

end Work.DISC
