import Mathlib
import Submission.Work.CrauderKatz.BlowUp.ThickDefs
import Submission.Work.CrauderKatz.BlowUp.transHom_exists

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CrauderKatz.BlowUp

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme

noncomputable section

variable (𝕜 : Type) [Field 𝕜]

/-- The substitution `transSubst` is compatible with the `𝕜`-algebra structures: it sends
constants to constants. -/
lemma transSubst_algebraMap (c : 𝕜) :
    transSubst 𝕜 (algebraMap 𝕜 (thickRing 𝕜) c) = algebraMap 𝕜 (ovRing 𝕜) c := by
  rw [← mk_C_eq_algebraMap 𝕜 c, transSubst_mk, transPoly_C]

/-- The automorphism `transSigma` of the overlap ring fixes the constants. -/
lemma transSigma_algebraMap_const (c : 𝕜) :
    transSigma 𝕜 (algebraMap 𝕜 (ovRing 𝕜) c) = algebraMap 𝕜 (ovRing 𝕜) c := by
  conv_lhs => rw [IsScalarTower.algebraMap_apply 𝕜 (thickRing 𝕜) (ovRing 𝕜) c]
  rw [transSigma_algebraMap 𝕜]
  exact transSubst_algebraMap 𝕜 c

/-- The transition homomorphism `transHom` is `𝕜`-linear. -/
lemma transHom_algebraMap (c : 𝕜) :
    transHom 𝕜 (algebraMap 𝕜 (thickRing 𝕜) c) = algebraMap 𝕜 (ovRing 𝕜) c := by
  rw [transHom, RingHom.comp_apply,
    ← IsScalarTower.algebraMap_apply 𝕜 (thickRing 𝕜) (ovRing 𝕜) c]
  exact transSigma_algebraMap_const 𝕜 c

theorem transHom_exists_alg (𝕜 : Type) [Field 𝕜] : ∃ (φ : Work.CrauderKatz.BlowUp.thickRing 𝕜 →+* Work.CrauderKatz.BlowUp.ovRing 𝕜), AlgebraicGeometry.IsOpenImmersion (AlgebraicGeometry.Spec.map (CommRingCat.ofHom φ)) ∧ φ (Work.CrauderKatz.BlowUp.thickX 𝕜) = algebraMap _ _ (Work.CrauderKatz.BlowUp.thickX 𝕜) * algebraMap _ _ (Work.CrauderKatz.BlowUp.thickT 𝕜) ∧ φ (Work.CrauderKatz.BlowUp.thickT 𝕜) = IsLocalization.Away.invSelf (Work.CrauderKatz.BlowUp.thickT 𝕜) ∧ φ (Work.CrauderKatz.BlowUp.thickE 𝕜) = algebraMap _ _ (Work.CrauderKatz.BlowUp.thickE 𝕜) ∧ (∀ c : 𝕜, φ (algebraMap 𝕜 (Work.CrauderKatz.BlowUp.thickRing 𝕜) c) = algebraMap 𝕜 (Work.CrauderKatz.BlowUp.ovRing 𝕜) c) := by
  refine ⟨transHom 𝕜, isOpenImmersion_Spec_transHom 𝕜, transHom_X 𝕜, transHom_T 𝕜,
    transHom_E 𝕜, ?_⟩
  intro c
  exact transHom_algebraMap 𝕜 c

end

end Work.CrauderKatz.BlowUp
