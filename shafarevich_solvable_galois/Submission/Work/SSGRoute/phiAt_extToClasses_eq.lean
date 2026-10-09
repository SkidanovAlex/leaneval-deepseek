import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open SSGRoute.PTExt CategoryTheory

/-- **Naturality of `φ` in the class `x`.**  The value of `φ` at level `L` on the class
`extToClasses z` (the push-forward of `z ∈ Ext¹_G(M, 𝕀_K)` along `𝕀_K → C_K`) is the push-forward
along the *idèle-class* map at the level `L` of the level pairing of `z` with the same `h`,
provided the two maps `𝕀 → C` are compatible in the sense of `hJ`
(`res C_K → C_L` induced by `resMap (classGroupMap K) ≫ classIncl` equals
`J ≫ classGroupMap L`).

This is pure `Ext`-calculus: both sides are the Yoneda product of `h` with the class
`(res z) ∘ mk₀(J ≫ classGroupMap L)`; the only inputs are associativity of `Ext.comp`,
`mk₀_comp_mk₀`, `mapExactFunctor` applied to a composite, and `hJ`. -/
theorem phiAt_extToClasses_eq (k K : Type) [Field k] [NumberField k] [Field K] [NumberField K]
    [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (L : Type) [Field L] [NumberField L] [Algebra k L] [Algebra K L] [IsScalarTower k K L]
    [FiniteDimensional k L] [IsGalois k L]
    (J : Rep.res (galRes k K L) (idelesK k K) ⟶ idelesK k L)
    (hJ : Rep.resMap (galRes k K L) (NK.HassePrinciple.classGroupMap k K) ≫ classIncl k K L =
        J ≫ NK.HassePrinciple.classGroupMap k L)
    {M : Rep Coeff (K ≃ₐ[k] K)} (z : Abelian.Ext M (idelesK k K) 1)
    (h : extH (Rep.res (galRes k K L) M) 1) :
    phiAt (k := k) (K := K) (L := L) (extToClasses z) h =
      (levelPair (galRes k K L) J z h).comp
        (Abelian.Ext.mk₀ (NK.HassePrinciple.classGroupMap k L)) (add_zero 2) := by
  -- `mapExactFunctor` sends the composite `extToClasses z` to the composite of the images.
  have hA : (extToClasses z).mapExactFunctor (Rep.resFunctor (galRes k K L)) =
      (z.mapExactFunctor (Rep.resFunctor (galRes k K L))).comp
        (Abelian.Ext.mk₀ (Rep.resMap (galRes k K L) (NK.HassePrinciple.classGroupMap k K)))
        (add_zero 1) := by
    simp only [extToClasses, Abelian.Ext.mapExactFunctor_comp,
      Abelian.Ext.mapExactFunctor_mk₀]
  simp only [phiAt, levelPair, extRes]
  rw [hA]
  -- reassociate on the left: `((Y ∘ mk₀ cgK) ∘ mk₀ classIncl) = Y ∘ (mk₀ cgK ∘ mk₀ classIncl)`
  rw [Abelian.Ext.comp_assoc_of_second_deg_zero]
  rw [Abelian.Ext.mk₀_comp_mk₀]
  rw [hJ]
  -- reassociate on the right: `(h ∘ (Y ∘ mk₀ J)) ∘ mk₀ cgL = h ∘ ((Y ∘ mk₀ J) ∘ mk₀ cgL)`
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [Abelian.Ext.comp_assoc_of_third_deg_zero]
  rw [Abelian.Ext.mk₀_comp_mk₀]

end Work.SSGRoute
