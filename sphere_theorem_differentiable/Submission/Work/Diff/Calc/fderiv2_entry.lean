import Mathlib
import Submission.Work.Diff.STE.Lead.fderiv_flatAffine_pdR

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.Calc

theorem fderiv2_entry
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {n : ℕ} (A : E → (Fin n → Fin n → ℝ)) {y : E} (i k : Fin n) (u v : E)
    (hA : ContDiffAt ℝ 2 A y) :
    ((fderiv ℝ (fun y' : E => fderiv ℝ A y') y u) v) i k
      = (fderiv ℝ (fun y' : E => fderiv ℝ (fun y'' : E => A y'' i k) y') y u) v := by
  -- The `(i,k)`-component evaluation as a continuous linear functional.
  let ev : (Fin n → Fin n → ℝ) →L[ℝ] ℝ :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => ℝ) k).comp
      (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ => Fin n → ℝ) i)
  -- The two second-derivative functions.
  let F : E → (E →L[ℝ] (Fin n → Fin n → ℝ)) := fun y' => fderiv ℝ A y'
  let G : E → (E →L[ℝ] ℝ) := fun y' => fderiv ℝ (fun y'' : E => A y'' i k) y'
  -- Post-composition with `ev`, as a continuous linear map.
  let compL : (E →L[ℝ] (Fin n → Fin n → ℝ)) →L[ℝ] (E →L[ℝ] ℝ) :=
    ContinuousLinearMap.compL ℝ E (Fin n → Fin n → ℝ) ℝ ev
  -- `G` agrees near `y` with `compL ∘ F`, since `A` is differentiable near `y`.
  have hGeq : G =ᶠ[nhds y] (⇑compL ∘ F) := by
    filter_upwards [hA.eventually (by norm_num)] with y' hy'
    have hdA : DifferentiableAt ℝ A y' := hy'.differentiableAt (by norm_num)
    show fderiv ℝ (fun y'' : E => A y'' i k) y' = compL (F y')
    rw [show (fun y'' : E => A y'' i k) = ⇑ev ∘ A from rfl]
    rw [((ContinuousLinearMap.hasFDerivAt ev).comp y' hdA.hasFDerivAt).fderiv]
    rfl
  have hFderiv : HasFDerivAt F (fderiv ℝ F y) y :=
    ((hA.fderiv_right (by norm_num)).differentiableAt_one).hasFDerivAt
  have hcomp : HasFDerivAt (⇑compL ∘ F) (compL.comp (fderiv ℝ F y)) y :=
    (ContinuousLinearMap.hasFDerivAt compL (x := F y)).comp y hFderiv
  have hGderiv : fderiv ℝ G y = compL.comp (fderiv ℝ F y) := by
    rw [hGeq.fderiv_eq]
    exact hcomp.fderiv
  rw [hGderiv]
  show (((fderiv ℝ F y) u) v) i k = (compL ((fderiv ℝ F y) u)) v
  rfl

end Work.Diff.Calc
