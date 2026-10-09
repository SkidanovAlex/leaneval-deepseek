import Mathlib
import Submission.Work.SSGRoute.E1aClean.phiCanDefs
import Submission.Work.SSGRoute.E1aClean.LeadNatWit
import Submission.Work.SSGRoute.E1aClean.decompFieldHenselEmb
import Submission.Work.SSGRoute.E1aClean.e1cMapCocycleFormula
import Submission.Work.SSGRoute.ValuationSES.C1
import Submission.Work.SSGRoute.ZDataMup.LocalUnramified.kummerChar_zero_on_inertia_imp_mem_unramified
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# (U1) of the lead's design `_lead_design/ssg_phiunr_1120`: the `Ext⁰`-factor through the free cover

If the `Ext⁰`-class `y : R₁ ⟶ Kˣ` followed by `μ : Kˣ ⟶ M` extends over the canonical free cover
`κ : R₁ ↪ F`, then `PhiE y = δ y` dies under `μ`:

  `(PhiE y).comp (mk₀ μ) = 0`.

This is a formal consequence of the connecting map being `extClass` of the canonical presentation
plus the associativity of `Ext.comp`.  Copied from the lead's design file (there it is in namespace
`Work.SSGRoute.ExtChain.E1cGeneric`; here in `Work.SSGRoute.E1aClean` to avoid any clash).
-/

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 2000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.E1aClean

open Work.SSGRoute.ExtChain.E1cGeneric

/-- **(U1)** If the `Ext⁰`-class `y : R₁ ⟶ Kˣ` followed by `μ : Kˣ ⟶ M` extends over the free
cover `κ : R₁ ↪ F`, then `PhiE y = δ y` dies under `μ`. -/
theorem PhiE_comp_mk0_eq_zero_of_factor {k : Type} [Field k] [CharZero k] {Ω : Type} [Field Ω]
    [Algebra k Ω] [IsAlgClosure k Ω] {K : IntermediateField k Ω} [FiniteDimensional k K]
    [IsGalois k K] (R : Rep.{0} Coeff (K ≃ₐ[k] K)) {M : Rep.{0} Coeff (K ≃ₐ[k] K)}
    (μ : unitsK k K ⟶ M)
    (y : Abelian.Ext.{0} (E1cR1 (k := k) (Ω := Ω) (K := K) R) (unitsK k K) 0)
    (h' : E1cF (k := k) (Ω := Ω) (K := K) R ⟶ M)
    (hfac : Abelian.Ext.addEquiv₀ y ≫ μ = Limits.kernel.ι (freeCover R) ≫ h') :
    (PhiE (k := k) (Ω := Ω) (K := K) R y).comp (Abelian.Ext.mk₀ μ) (add_zero 1) = 0 := by
  have hy : y = Abelian.Ext.mk₀ (Abelian.Ext.addEquiv₀ y) :=
    (Abelian.Ext.mk₀_addEquiv₀_apply y).symm
  show ((freeCoverSES_shortExact R).extClass.comp y (by norm_num : 1 + 0 = 1)).comp
      (Abelian.Ext.mk₀ μ) (add_zero 1) = 0
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero, hy, Abelian.Ext.mk₀_comp_mk₀, hfac,
    ← Abelian.Ext.mk₀_comp_mk₀, ← Abelian.Ext.comp_assoc_of_second_deg_zero]
  have h0 := (freeCoverSES_shortExact R).extClass_comp
  simp only [freeCoverSES] at h0
  rw [h0, Abelian.Ext.zero_comp]

end Work.SSGRoute.E1aClean
