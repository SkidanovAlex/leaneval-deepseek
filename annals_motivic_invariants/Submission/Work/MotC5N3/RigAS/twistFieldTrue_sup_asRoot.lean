import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV5.RigAS.twistFieldTrue_sup_asRoot

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `asTwistFieldTrue ⊔ K⟮asRoot g⟯ = asFieldL D g` (general base field `K`)

Port of `Submission/Work/MotV5/RigAS/twistFieldTrue_sup_asRoot.lean`: the generic field-theoretic
part of the source file is imported and used directly, only the final node is restated for the
general base field `K`.
-/

set_option autoImplicit false
set_option maxHeartbeats 800000
set_option linter.style.haveILetI false

namespace Work.MotC5N3.RigAS

open IntermediateField

theorem twistFieldTrue_sup_asRoot (𝕜 : Type) [Field 𝕜] [CharP 𝕜 5] {K : Type} [Field K]
    [Algebra 𝕜 K] [CharP K 5] (D : Work.MotV.KleinData 𝕜) (g : K)
    (τ : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D)
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D)
    (σ : Work.MotC5N3.KbA K ≃ₐ[K] Work.MotC5N3.KbA K)
    (h : Work.MotC5N3.ASTwistData 𝕜 D g τ σS σ) :
    Work.MotC5N3.asTwistFieldTrue D g τ σS
      ⊔ IntermediateField.adjoin K
          {algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot g)}
      = Work.MotC5N3.asFieldL D g := by
  have hw : algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot g) ∈
      Work.MotC5N3.asFieldL D g := by
    show _ ∈ Work.MotC5N3.kleinField K D ⊔ _
    exact (le_sup_right : _ ≤ Work.MotC5N3.kleinField K D ⊔ _)
      (IntermediateField.subset_adjoin _ _ (Set.mem_singleton _))
  have hAw : Work.MotC5N3.asTwistAction D τ σS
      (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot g))
      = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot g) + 1 := by
    rw [Work.MotC5N3.asTwistAction, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply]
    rw [h.hτ, AlgEquiv.commutes, h.hσ, map_add, map_one]
  exact Work.MotV5.RigAS.sup_inf_fixedField_adjoin_eq (Work.MotC5N3.asFieldL D g)
    (Work.MotC5N3.asTwistAction D τ σS) h.hpres h.h5L h.hneL
    (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot g)) hw hAw

end Work.MotC5N3.RigAS
