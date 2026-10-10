import Mathlib.Tactic.Have
import Mathlib.RepresentationTheory.Rep.Basic
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
import Submission.Work.SSGRoute.PTDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

open CategoryTheory

/-- **`Ext` depends on its *second* argument only up to isomorphism.**  If `e : N ≅ N'` is an
isomorphism in `Rep Coeff G`, then `Ext^n_G(M,N) ≅ Ext^n_G(M,N')` — via composition with
`Ext.mk₀ e.hom` / `Ext.mk₀ e.inv` (`Ext.postcomp`, `Ext.mk₀_comp_mk₀`, `Ext.comp_assoc_of_third_deg_zero`).

This is the general form of the already-proved `Work.SSGRoute.extH_congr` (the `M = unitRep G`
case): the same proof text with `unitRep G` replaced by the variable `M`.  It is the tool that lets
the E7a assembly replace the coefficient module `K_wˣ` of `Ext¹_{D_w}(res E', K_wˣ)` by the units of
the intermediate field `K' ⊆ κ̄` using
`Work.SSGRoute.localUnitsK_iso_intermediateField`. -/
theorem ext_congr_right {G : Type} [Group G] {M N N' : Rep.{0} SSGRoute.PTExt.Coeff G}
    (e : CategoryTheory.Iso N N') (n : ℕ) :
    Nonempty (CategoryTheory.Abelian.Ext M N n ≃+ CategoryTheory.Abelian.Ext M N' n) := by
  classical
  -- Postcomposition with `e` and with `e⁻¹` on `Ext^n_G(M, -)`.
  let φ : CategoryTheory.Abelian.Ext M N n →+ CategoryTheory.Abelian.Ext M N' n :=
    (CategoryTheory.Abelian.Ext.mk₀ e.hom).postcomp M (add_zero n)
  let ψ : CategoryTheory.Abelian.Ext M N' n →+ CategoryTheory.Abelian.Ext M N n :=
    (CategoryTheory.Abelian.Ext.mk₀ e.inv).postcomp M (add_zero n)
  -- the two composites of the components of `e` are the identities of `Ext^0`
  have hmid₁ : (CategoryTheory.Abelian.Ext.mk₀ e.hom).comp
      (CategoryTheory.Abelian.Ext.mk₀ e.inv) (add_zero 0) =
      CategoryTheory.Abelian.Ext.mk₀ (𝟙 N) := by
    rw [CategoryTheory.Abelian.Ext.mk₀_comp_mk₀, e.hom_inv_id]
  have hmid₂ : (CategoryTheory.Abelian.Ext.mk₀ e.inv).comp
      (CategoryTheory.Abelian.Ext.mk₀ e.hom) (add_zero 0) =
      CategoryTheory.Abelian.Ext.mk₀ (𝟙 N') := by
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
