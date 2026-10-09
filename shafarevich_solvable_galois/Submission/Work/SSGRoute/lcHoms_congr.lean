import Mathlib
import Submission.Work.SSGRoute.localKummerReciprocity
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

theorem lcHoms_congr {p : ℕ} [Fact p.Prime] {Γ Γ' : Type} [Group Γ] [TopologicalSpace Γ]
    [Group Γ'] [TopologicalSpace Γ'] (e : Γ ≃* Γ') (hcont : Continuous e)
    (hopen : IsOpenMap e) :
    Nonempty (↥(Work.SSGRoute.lcHoms p Γ) ≃* ↥(Work.SSGRoute.lcHoms p Γ')) := by
  -- `e` is a bijection, so being an open map is the same as `e.symm` being continuous.
  have hsymm : Continuous (e.symm : Γ' → Γ) := e.toEquiv.continuous_symm_iff.mpr hopen
  refine ⟨{ toFun := fun χ => ⟨χ.1.comp e.symm.toMonoidHom, χ.2.comp_continuous hsymm⟩
            invFun := fun ξ => ⟨ξ.1.comp e.toMonoidHom, ξ.2.comp_continuous hcont⟩
            left_inv := ?_
            right_inv := ?_
            map_mul' := ?_ }⟩
  · intro χ; ext g; simp
  · intro ξ; ext g; simp
  · intro χ ψ; ext g; simp

end Work.SSGRoute
