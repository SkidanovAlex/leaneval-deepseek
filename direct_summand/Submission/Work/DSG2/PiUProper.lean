import Mathlib
import Submission.Work.DSG2.Setup
import Submission.Work.DSG2.Glue
import Submission.Work.DSG2.Basic

/-!
# DSG2: the restriction of `π` over `U i` is proper (Stacks 0200)

The inclusion `ri P i : V i ⟶ π⁻¹(U i)` is an open immersion with `ri ≫ piU = phii` proper
(`isProper_ri_comp_piU`) and `piU` separated (`isSeparated_piU`); hence `ri` is proper, so (being
an immersion) a closed immersion, and it is scheme-theoretically dominant
(`isSchemeTheoreticallyDominant_ri`), so it is an isomorphism.  Transporting `phii` along it gives
that `piU` is proper.
-/

open CategoryTheory AlgebraicGeometry Limits

universe u

namespace Work.DSG2

namespace ChowSetup

variable {A : Type u} [CommRing A] {X : Scheme.{u}} {f : X ⟶ Spec (.of A)}

theorem isProper_piU_alt (D : ChowSetup A X f) [IsSeparated f] (P : GluedPi D) (i : Fin D.m) :
    IsProper (piU P i) := by
  haveI hproper_ri : IsProper (ri P i) := by
    haveI : IsProper (ri P i ≫ piU P i) := isProper_ri_comp_piU P i
    haveI : IsSeparated (piU P i) := isSeparated_piU P i
    exact IsProper.of_comp (ri P i) (piU P i)
  haveI hisOpen : IsOpenImmersion (ri P i) := isOpenImmersion_ri P i
  haveI hclosed : IsClosedImmersion (ri P i) :=
    isClosedImmersion_of_isImmersion_of_isProper (ri P i)
  haveI hiso : IsIso (ri P i) :=
    IsClosedImmersion.isIso_iff_ker_eq_bot.mpr
      (D.isSchemeTheoreticallyDominant_ri P i).ker_eq_bot
  have h : piU P i = inv (ri P i) ≫ (ri P i ≫ piU P i) := by
    rw [← Category.assoc, IsIso.inv_hom_id, Category.id_comp]
  rw [h]
  haveI : IsProper (ri P i ≫ piU P i) := isProper_ri_comp_piU P i
  infer_instance

end ChowSetup

end Work.DSG2
