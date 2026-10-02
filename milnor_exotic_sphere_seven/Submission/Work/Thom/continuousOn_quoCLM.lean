import Mathlib
import Submission.Work.Thom.tautologicalQuotient

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

namespace Work.Thom

/-- The tautological quotient projection `w ↦ quoCLM l w` is continuous on the open chart piece
where the `l`-th coordinate of `w` is invertible. -/
theorem continuousOn_quoCLM {n : ℕ} (l : Fin (n+1)) :
    ContinuousOn (fun w : EuclideanSpace ℂ (Fin (n+1)) => Work.Thom.quoCLM l w) {w | w l ≠ 0} := by
  have hev : Continuous (fun w : EuclideanSpace ℂ (Fin (n+1)) => w l) := (evalCLM l).continuous
  have hdrop : Continuous (fun w : EuclideanSpace ℂ (Fin (n+1)) => dropFun l w) :=
    (dropCLM l).continuous
  have hψ : ContinuousOn (fun w : EuclideanSpace ℂ (Fin (n+1)) => (w l)⁻¹ • dropFun l w)
      {w | w l ≠ 0} :=
    (hev.continuousOn.inv₀ (fun x hx => hx)).smul hdrop.continuousOn
  have hsmul : ContinuousOn (fun w : EuclideanSpace ℂ (Fin (n+1)) =>
      (evalCLM l).smulRight ((w l)⁻¹ • dropFun l w)) {w | w l ≠ 0} := by
    have h2 := (ContinuousLinearMap.smulRightL ℂ (EuclideanSpace ℂ (Fin (n+1)))
      (EuclideanSpace ℂ (Fin n)) (evalCLM l)).continuous.comp_continuousOn hψ
    refine ContinuousOn.congr h2 (fun w _ => ?_)
    simp only [Function.comp_apply, ContinuousLinearMap.smulRightL_apply_apply]
  refine ContinuousOn.congr ?_ (fun w _ => quoCLM_eq l w)
  exact continuousOn_const.sub hsmul

end Work.Thom
