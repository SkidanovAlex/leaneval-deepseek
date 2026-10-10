import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.Functoriality
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E0bClean.eBridge_natural
import Submission.Work.SSGRoute.PTDefsOmega
import Submission.Work.SSGRoute.classIncl_inflation_injective
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.E4R3

open CategoryTheory
open SSGRoute.PTExt

noncomputable section

/-- The `Ext`-bridge `eBridge` intertwines the level inflation `inflC` of `PTDefs` with the
group-cohomology map `groupCohomology.map (galRes k F L) (classIncl k F L)`. -/
lemma inflC_eq_eBridge_map (k F L : Type) [Field k] [NumberField k] [Field F] [NumberField F]
    [Field L] [NumberField L] [Algebra k F] [Algebra F L] [Algebra k L] [IsScalarTower k F L]
    [FiniteDimensional k F] [IsGalois k F] [FiniteDimensional k L] [IsGalois k L]
    (y : extH (classesK k F) 2) :
    inflC (k := k) (K := F) (L := L) y
      = Work.SSGRoute.E0bGroupCoeff.eBridge 2 (L ≃ₐ[k] L) (classesK k L)
          ((groupCohomology.map (galRes k F L) (classIncl k F L) 2).hom
            ((Work.SSGRoute.E0bGroupCoeff.eBridge 2 (F ≃ₐ[k] F) (classesK k F)).symm y)) := by
  have hnat := Work.SSGRoute.E0bClean.eBridge_natural (galRes k F L) (classIncl k F L) 2
    ((Work.SSGRoute.E0bGroupCoeff.eBridge 2 (F ≃ₐ[k] F) (classesK k F)).symm y)
  rw [AddEquiv.apply_symm_apply] at hnat
  rw [hnat]
  rfl

theorem inflC_injective (k F L : Type) [Field k] [NumberField k] [Field F] [NumberField F] [Field L] [NumberField L] [Algebra k F] [Algebra F L] [Algebra k L] [IsScalarTower k F L] [FiniteDimensional k F] [IsGalois k F] [FiniteDimensional k L] [IsGalois k L] : Function.Injective (fun y : SSGRoute.PTExt.extH (SSGRoute.PTExt.classesK k F) 2 => SSGRoute.PTExt.inflC (k := k) (K := F) (L := L) y) := by
  intro y y' hyy'
  dsimp only at hyy'
  have h1 : (groupCohomology.map (galRes k F L) (classIncl k F L) 2).hom
        ((Work.SSGRoute.E0bGroupCoeff.eBridge 2 (F ≃ₐ[k] F) (classesK k F)).symm y)
      = (groupCohomology.map (galRes k F L) (classIncl k F L) 2).hom
        ((Work.SSGRoute.E0bGroupCoeff.eBridge 2 (F ≃ₐ[k] F) (classesK k F)).symm y') := by
    apply (Work.SSGRoute.E0bGroupCoeff.eBridge 2 (L ≃ₐ[k] L) (classesK k L)).injective
    rw [← inflC_eq_eBridge_map k F L y, ← inflC_eq_eBridge_map k F L y', hyy']
  exact (Work.SSGRoute.E0bGroupCoeff.eBridge 2 (F ≃ₐ[k] F) (classesK k F)).symm.injective
    (Work.SSGRoute.classIncl_inflation_injective k F L h1)

end

end Work.SSGRoute.E4R3
