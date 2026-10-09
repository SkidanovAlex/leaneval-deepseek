import Mathlib
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

/-- **`Ext`-cohomology depends on the coefficient module only up to isomorphism.**  If
`e : A ≅ B` is an isomorphism of `Rep Coeff G`, then `H^n(G,A) = Ext^n_G(ℤ,A) ≅ Ext^n_G(ℤ,B)`,
by additivity of `Ext` in its second variable (`Ext.comp_add`, `Ext.mk₀`).  Used by E7a to replace
`Hom_ℤ(E^∨(1), Ω̄ˣ)` by `E` after `Work.SSGRoute.hom_dualMod_local_units`. -/
theorem extH_congr {G : Type} [Group G] {A B : Rep.{0} SSGRoute.PTExt.Coeff G}
    (e : CategoryTheory.Iso A B) (n : ℕ) :
    Nonempty (SSGRoute.PTExt.extH A n ≃+ SSGRoute.PTExt.extH B n) := by
  classical
  -- Postcomposition with `e` and with `e⁻¹` on `Ext^n_G(ℤ, -)`.
  let φ : SSGRoute.PTExt.extH A n →+ SSGRoute.PTExt.extH B n :=
    (CategoryTheory.Abelian.Ext.mk₀ e.hom).postcomp (SSGRoute.PTExt.unitRep G) (add_zero n)
  let ψ : SSGRoute.PTExt.extH B n →+ SSGRoute.PTExt.extH A n :=
    (CategoryTheory.Abelian.Ext.mk₀ e.inv).postcomp (SSGRoute.PTExt.unitRep G) (add_zero n)
  -- the two composites of the components of `e` are the identities of `Ext^0`
  have hmid₁ : (CategoryTheory.Abelian.Ext.mk₀ e.hom).comp
      (CategoryTheory.Abelian.Ext.mk₀ e.inv) (add_zero 0) =
      CategoryTheory.Abelian.Ext.mk₀ (𝟙 A) := by
    rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, e.hom_inv_id]
  have hmid₂ : (CategoryTheory.Abelian.Ext.mk₀ e.inv).comp
      (CategoryTheory.Abelian.Ext.mk₀ e.hom) (add_zero 0) =
      CategoryTheory.Abelian.Ext.mk₀ (𝟙 B) := by
    rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, e.inv_hom_id]
  have hleft : ∀ y, ψ (φ y) = y := by
    intro y
    change ((y.comp (CategoryTheory.Abelian.Ext.mk₀ e.hom) (add_zero n)).comp
      (CategoryTheory.Abelian.Ext.mk₀ e.inv) (add_zero n)) = y
    rw [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero y
      (CategoryTheory.Abelian.Ext.mk₀ e.hom) (CategoryTheory.Abelian.Ext.mk₀ e.inv) (add_zero n),
      hmid₁, CategoryTheory.Abelian.Ext.comp_mk₀_id]
  have hright : ∀ z, φ (ψ z) = z := by
    intro z
    change ((z.comp (CategoryTheory.Abelian.Ext.mk₀ e.inv) (add_zero n)).comp
      (CategoryTheory.Abelian.Ext.mk₀ e.hom) (add_zero n)) = z
    rw [CategoryTheory.Abelian.Ext.comp_assoc_of_third_deg_zero z
      (CategoryTheory.Abelian.Ext.mk₀ e.inv) (CategoryTheory.Abelian.Ext.mk₀ e.hom) (add_zero n),
      hmid₂, CategoryTheory.Abelian.Ext.comp_mk₀_id]
  exact ⟨{ toFun := ⇑φ
           invFun := ⇑ψ
           left_inv := hleft
           right_inv := hright
           map_add' := fun x y => φ.map_add x y }⟩

end Work.SSGRoute
