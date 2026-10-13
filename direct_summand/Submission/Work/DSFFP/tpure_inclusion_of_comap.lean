import Mathlib
import Submission.Work.DSFFP.Defs

namespace Work.DSFFP

universe u

theorem tpure_inclusion_of_comap {S : Type u} [CommRing S] {T : Type u} [AddCommGroup T]
    [Module S T] {Q : Type u} [AddCommGroup Q] [Module S Q] (A B : Submodule S Q) (hAB : A ≤ B)
    (H : Work.DSFFP.TPure T (Submodule.comap B.subtype A).subtype) :
    Work.DSFFP.TPure T (A.inclusion hAB) := by
  -- `A` and `comap B.subtype A` are canonically isomorphic, and the inclusion
  -- `A ↪ B` factors as `comap B.subtype A ↪ B` after that isomorphism.
  have he : TPure T
      ((Submodule.comapSubtypeEquivOfLe hAB).symm : A →ₗ[S] Submodule.comap B.subtype A) := by
    apply TPure.of_retract
      (r := (Submodule.comapSubtypeEquivOfLe hAB : Submodule.comap B.subtype A →ₗ[S] A))
    ext x
    simp
  have hcomp : A.inclusion hAB = (Submodule.comap B.subtype A).subtype ∘ₗ
      ((Submodule.comapSubtypeEquivOfLe hAB).symm : A →ₗ[S]
        Submodule.comap B.subtype A) := by
    ext x
    rfl
  rw [hcomp]
  exact he.comp H

end Work.DSFFP
