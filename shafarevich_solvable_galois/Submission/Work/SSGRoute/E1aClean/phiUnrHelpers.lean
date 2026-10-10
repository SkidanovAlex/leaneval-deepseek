import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.LinearAlgebra.TensorProduct.Defs
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.E1aClean.LeadPhiUnr.decompFieldHenselEmb_units_mem_localUnits_iff
import Submission.Work.SSGRoute.E1aClean.LeadPhiUnr.henselUnit_pow_mul_localUnits_of_inertiaFixedRoot
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Bookkeeping lemmas for the unramified clause `phiCan_unramified` (U5)

The push factor of `phiCan` is the postcomposition `(mk₀ θ).postcomp XD (add_zero 1)`.  The two
`Ext`-identities below let one (a) compose the result with another `mk₀` (the valuation
`mk₀ localUnitsValHom` of the detector `ValuationSES.isUnramifiedExt_iff_comp_valHom`), and (b) move
through the `Eq.mp`/`AddEquiv.refl` transport (factor 6 of the chain, the
`Rep.res e.symm (Rep.res e (unitsK …)) = unitsK …` re-spelling).
-/

open CategoryTheory SSGRoute.PTExt
open scoped TensorProduct

set_option maxHeartbeats 4000000
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

namespace Work.SSGRoute.E1aClean

noncomputable section

/-- **Postcomposition by `mk₀ θ`, then composition with `mk₀ v`.**  For `θ : Y ⟶ Z`, `v : Z ⟶ W`
and `y : Ext X Y 1`,
`((mk₀ θ).postcomp X (add_zero 1) y).comp (mk₀ v) (add_zero 1) = y.comp (mk₀ (θ ≫ v)) (add_zero 1)`.
This is `Ext.comp_assoc_of_second_deg_zero` plus `Ext.mk₀_comp_mk₀`. -/
theorem postcomp_mk₀_comp_mk₀ {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
    [CategoryTheory.HasExt C] {X Y Z W : C} (θ : Y ⟶ Z) (y : CategoryTheory.Abelian.Ext X Y 1)
    (v : Z ⟶ W) :
    ((CategoryTheory.Abelian.Ext.mk₀ θ).postcomp X (add_zero 1) y).comp
        (CategoryTheory.Abelian.Ext.mk₀ v) (add_zero 1)
      = y.comp (CategoryTheory.Abelian.Ext.mk₀ (θ ≫ v)) (add_zero 1) := by
  change (y.comp (CategoryTheory.Abelian.Ext.mk₀ θ) (add_zero 1)).comp
      (CategoryTheory.Abelian.Ext.mk₀ v) (add_zero 1)
    = y.comp (CategoryTheory.Abelian.Ext.mk₀ (θ ≫ v)) (add_zero 1)
  rw [CategoryTheory.Abelian.Ext.comp_assoc_of_second_deg_zero,
    CategoryTheory.Abelian.Ext.mk₀_comp_mk₀]

/-- **The `Eq.rec`-transport in the second variable of `Ext` commutes with `mk₀`-precomposition.**
For `h : u₁ = u₂`, `z : Ext R u₁ 1` and `χ : u₂ ⟶ T`,
`(h ▸ z).comp (mk₀ χ) = z.comp (mk₀ (h.symm ▸ χ))`. -/
theorem ext_ndrec_comp_mk₀ {C : Type*} [CategoryTheory.Category C] [CategoryTheory.Abelian C]
    [CategoryTheory.HasExt C] {R u₁ u₂ T : C} (h : u₁ = u₂)
    (z : CategoryTheory.Abelian.Ext R u₁ 1) (χ : u₂ ⟶ T) :
    (h ▸ z).comp (CategoryTheory.Abelian.Ext.mk₀ χ) (add_zero 1)
      = z.comp (CategoryTheory.Abelian.Ext.mk₀ (h.symm ▸ χ)) (add_zero 1) := by
  cases h
  rfl

/-- **The `Eq.mp`/`AddEquiv.refl` transport of factor 6 of `phiCan` is the canonical cast.**
With `F := fun S => CategoryTheory.Abelian.Ext R S 1`, the transport
`Eq.mp (congrArg (fun S => Ext R u₁ 1 ≃+ Ext R S 1) h) (AddEquiv.refl _)` acts on elements as
`h ▸ ·`. -/
theorem eq_mp_congrArg_refl_apply_ext {C : Type*} [CategoryTheory.Category C]
    [CategoryTheory.Abelian C] [CategoryTheory.HasExt C] {R u₁ u₂ : C} (h : u₁ = u₂)
    (x : CategoryTheory.Abelian.Ext R u₁ 1) :
    (Eq.mp (congrArg (fun S => CategoryTheory.Abelian.Ext R u₁ 1 ≃+
        CategoryTheory.Abelian.Ext R S 1) h) (AddEquiv.refl _)) x = h ▸ x := by
  cases h
  rfl

end

end Work.SSGRoute.E1aClean
