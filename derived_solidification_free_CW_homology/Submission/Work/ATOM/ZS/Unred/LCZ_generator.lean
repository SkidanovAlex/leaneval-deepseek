import Mathlib
import Submission.Work.ATOM.ZS.Unred.LCZ
import Submission.Work.ATOM.ZS.Unred.LCZ_unit_const

/-!
# The generator statement `∃ j : LCZ ⟶ ℤ[*], j_*(1) = e₁`

This is the only piece of the identification `ℤ[*] ≅ ℤ` that the proof of
`Work.ATOM.ZS.Unred.LocallyConstantIndicator` needs: a morphism `LCZ ⟶ ℤ[*]` which carries the
constant function `1` (the canonical generator of `LCZ(*) = ℤ`) to the canonical generator
`e₁ = homFreeEquiv * 𝟙` of `ℤ[*](*)`.

The morphism is produced by the adjunction `LCZ = lcFunctor ℤ ⊣ underlying`: a morphism
`LCZ ⟶ ℤ[*]` corresponds to a map `ℤ ⟶ ℤ[*](*)`, namely `toSpanSingleton e₁`.  Its value at the
point is computed with `Adjunction.homEquiv_apply` (the value of `homEquiv j` at `1` is
`j_*(unit 1)`) and `LCZ_unit_const` (the unit of the adjunction sends `1` to the constant function
`1`).
-/

open CategoryTheory Limits LightProfinite LightCondensed MonoidalCategory MonoidalClosed
open _root_.LightCondensed
open Opposite

noncomputable section

namespace Work.ATOM.ZS.Unred

/-- **The generator statement.**  There is a morphism `LCZ ⟶ ℤ[*]` carrying the constant function
`1` to the canonical generator `e₁`. -/
theorem LCZ_generator :
    ∃ j : LCZ ⟶ Work.ATOM.zfree Work.ATOM.pt,
      j.hom.app (op Work.ATOM.pt) oneLCZ = e1 := by
  refine ⟨((LightCondMod.LocallyConstant.adjunction ℤ).homEquiv (ModuleCat.of ℤ ℤ)
      (Work.ATOM.zfree Work.ATOM.pt)).symm
    (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ e1)), ?_⟩
  have hj : (LightCondMod.LocallyConstant.adjunction ℤ).homEquiv (ModuleCat.of ℤ ℤ)
      (Work.ATOM.zfree Work.ATOM.pt)
      (((LightCondMod.LocallyConstant.adjunction ℤ).homEquiv (ModuleCat.of ℤ ℤ)
        (Work.ATOM.zfree Work.ATOM.pt)).symm
        (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ e1)))
      = ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ e1) := Equiv.apply_symm_apply _ _
  have h5 : (ConcreteCategory.hom ((LightCondMod.LocallyConstant.adjunction ℤ).homEquiv
      (ModuleCat.of ℤ ℤ) (Work.ATOM.zfree Work.ATOM.pt)
      (((LightCondMod.LocallyConstant.adjunction ℤ).homEquiv (ModuleCat.of ℤ ℤ)
        (Work.ATOM.zfree Work.ATOM.pt)).symm
          (ModuleCat.ofHom (LinearMap.toSpanSingleton ℤ _ e1))))) (1 : ℤ) = e1 := by
    rw [hj]
    exact LinearMap.toSpanSingleton_apply_one ℤ _ e1
  have h4 : (ConcreteCategory.hom (((LightCondMod.LocallyConstant.adjunction ℤ).unit.app
      (ModuleCat.of ℤ ℤ)))) (1 : ℤ) = oneLCZ := LCZ_unit_const (ModuleCat.of ℤ ℤ) 1
  rw [Adjunction.homEquiv_apply, ConcreteCategory.comp_apply, h4] at h5
  exact h5

end Work.ATOM.ZS.Unred
