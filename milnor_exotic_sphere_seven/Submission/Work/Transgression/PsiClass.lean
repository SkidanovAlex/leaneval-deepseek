import Mathlib
import Submission.Work.Transgression.Pieces
import Submission.Work.Transgression.PsiAux

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 2000000
set_option linter.style.haveILetI false
set_option linter.unusedSectionVars false

namespace Work.Transgression

open Work.TangentClasses

/-! # The class of the clutching map `ψ (u,v) = uᵃ v uᵇ`

`Work.Transgression.PsiClass`: the pullback along `ψ a b : S³ × S³ → S³` of the class `gen`
(any generator of `H³(S³;ℤ)`) is `(a + b) • prjA^* gen + prjB^* gen`.  The proof restricts along
the two factor inclusions `sectA`, `sectB`, where `ψ ∘ sectA = (q ↦ qᵃ⁺ᵇ)` and `ψ ∘ sectB = id`,
and uses the Künneth injectivity `Work.Transgression.PsiAux.KunnethInjS3Prod` together with the
Hopf formula `Work.Transgression.PsiAux.s3MulCm_HMap`. -/

theorem PsiClass (a b : ℤ) (gen : ↥(Work.Thom.Coh ℤ 3 Work.CharacteristicClasses.S3))
    (hgen : ∀ x : ↥(Work.Thom.Coh ℤ 3 Work.CharacteristicClasses.S3), ∃ k : ℤ, x = k • gen) :
    (Work.TangentClasses.HMap (Work.Transgression.psi a b) 3).hom gen
      = (a + b) • (Work.TangentClasses.HMap Work.Transgression.prjA 3).hom gen
        + (Work.TangentClasses.HMap Work.Transgression.prjB 3).hom gen := by
  refine sub_eq_zero.mp (PsiAux.KunnethInjS3Prod
    ((HMap (psi a b) 3).hom gen
      - ((a + b) • (HMap prjA 3).hom gen + (HMap prjB 3).hom gen)) ?_ ?_)
  · have h1 : (HMap sectA 3).hom ((HMap (psi a b) 3).hom gen) = (a + b) • gen := by
      rw [← LinearMap.comp_apply, PsiAux.sectA_comp_psi a b, PsiAux.zPow_HMap]
    have h2 : (HMap sectA 3).hom ((HMap prjA 3).hom gen) = gen := by
      rw [← LinearMap.comp_apply, PsiAux.sectA_comp_prjA, LinearMap.id_apply]
    have h3 : (HMap sectA 3).hom ((HMap prjB 3).hom gen) = 0 := by
      rw [← LinearMap.comp_apply, PsiAux.sectA_prjB_zero, LinearMap.zero_apply]
    rw [map_sub, map_add, map_zsmul, h1, h2, h3]
    simp
  · have h1 : (HMap sectB 3).hom ((HMap (psi a b) 3).hom gen) = gen := by
      rw [← LinearMap.comp_apply, PsiAux.sectB_comp_psi a b, LinearMap.id_apply]
    have h2 : (HMap sectB 3).hom ((HMap prjB 3).hom gen) = gen := by
      rw [← LinearMap.comp_apply, PsiAux.sectB_comp_prjB, LinearMap.id_apply]
    have h3 : (HMap sectB 3).hom ((a + b) • (HMap prjA 3).hom gen) = 0 := by
      rw [← map_zsmul (HMap prjA 3).hom (a + b) gen]
      rw [← LinearMap.comp_apply, PsiAux.sectB_prjA_zero, LinearMap.zero_apply]
    rw [map_sub, map_add, h1, h3, h2]
    simp

end Work.Transgression
