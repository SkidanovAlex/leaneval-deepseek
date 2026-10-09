import Mathlib
import Submission.Work.SSGRoute.CC.MagFourDefs
import Submission.Work.SSGRoute.CC.MagFourMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.CC

open scoped commutatorElement

/-- The re-labelling `freeGroupCongr σ` of the free group on the letters is an involution
whenever `σ` is one. -/
theorem freeGroupCongr_invol (X : Type) (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x) (g : FreeGroup X) :
    FreeGroup.freeGroupCongr σ (FreeGroup.freeGroupCongr σ g) = g := by
  have htrans := FreeGroup.freeGroupCongr_trans σ σ
  have hrefl : σ.trans σ = Equiv.refl X := Equiv.ext (fun x => hσ x)
  rw [hrefl, FreeGroup.freeGroupCongr_refl] at htrans
  calc FreeGroup.freeGroupCongr σ (FreeGroup.freeGroupCongr σ g)
      = (FreeGroup.freeGroupCongr σ).trans (FreeGroup.freeGroupCongr σ) g := rfl
    _ = g := by rw [htrans]; rfl

/-- The double witness word `ν(g · σg)` equals the commutator `⁅g⁻¹, (σg)⁻¹⁆`. -/
theorem doubleWord_eq_commutator {X : Type} (σ : X ≃ X) (hσ : ∀ x, σ (σ x) = x)
    (g : FreeGroup X) :
    Work.SSGRoute.doubleWord X σ g =
      g⁻¹ * ((FreeGroup.freeGroupCongr σ) g)⁻¹ * g * (FreeGroup.freeGroupCongr σ) g := by
  unfold doubleWord
  rw [map_mul, freeGroupCongr_invol X σ hσ g]
  group

end Work.SSGRoute.CC
