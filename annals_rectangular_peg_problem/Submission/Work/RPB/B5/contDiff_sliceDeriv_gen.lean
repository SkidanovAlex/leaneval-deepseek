import Mathlib
import Submission.Work.RPB.B5.contDiff_signedArea

/-!
# B5: smoothness of the slice derivative, for an arbitrary parameter space

If `V : X → ℝ → ℂ` is a family of plane curves depending on a parameter `z.1 : X` and
`(z, s) ↦ V z s` is jointly `C^{k+1}`, then the `s`-slice derivative
`(z, s) ↦ deriv (fun u => V z u) s` is jointly `C^k`.

The derivative of the slice is the evaluation of the Fréchet derivative of the joint map
`W := fun z : X × ℝ => V z.1 z.2` at the tangent vector `(0, 1)`
(`deriv (fun u => W (z.1, u)) z.2 = fderiv ℝ W z (0, 1)`, obtained by composing the
Fréchet derivative of `W` at `z` with the `HasFDerivAt` of `u ↦ (z.1, u)`, whose derivative is
`ContinuousLinearMap.inr ℝ X ℝ`).  Since `W` is `C^{k+1}`, its Fréchet derivative is `C^k`
(`ContDiff.fderiv_right`), and evaluating a `C^k` family of continuous linear maps at the
constant vector `(0,1)` preserves `C^k` (`ContDiff.clm_apply`).
-/

set_option autoImplicit false

noncomputable section

namespace Work.RPB.B5

lemma contDiff_sliceDeriv_gen {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (V : X → ℝ → ℂ) {k : ℕ}
    (hV : ContDiff ℝ (k + 1) (fun z : X × ℝ => V z.1 z.2)) :
    ContDiff ℝ k (fun z : X × ℝ => deriv (fun s => V z.1 s) z.2) := by
  let W : X × ℝ → ℂ := fun z => V z.1 z.2
  have hW : ContDiff ℝ (k + 1) W := hV
  have hdiffW : Differentiable ℝ W := hW.differentiable (by simp)
  -- The Fréchet derivative of the joint map is `C^k`.
  have hfd : ContDiff ℝ k (fderiv ℝ W) :=
    hW.fderiv_right (m := (k : WithTop ℕ∞)) (by norm_num)
  -- Evaluating it at the constant tangent vector `(0, 1)` keeps it `C^k`.
  have hderivVal : ContDiff ℝ k (fun z : X × ℝ => (fderiv ℝ W z) (0, 1)) :=
    hfd.clm_apply contDiff_const
  -- And that evaluation is exactly the slice derivative.
  have heq : (fun z : X × ℝ => deriv (fun s => V z.1 s) z.2)
      = fun z => (fderiv ℝ W z) (0, 1) := by
    funext z
    change deriv (fun y : ℝ => W (z.1, y)) z.2 = (fderiv ℝ W z) (0, 1)
    have h1 : HasFDerivAt (fun y : ℝ => (z.1, y)) (ContinuousLinearMap.inr ℝ X ℝ) z.2 :=
      hasFDerivAt_prodMk_right z.1 z.2
    have h2 : HasFDerivAt (fun y : ℝ => W (z.1, y))
        ((fderiv ℝ W z).comp (ContinuousLinearMap.inr ℝ X ℝ)) z.2 := by
      simpa [Function.comp_def] using ((hdiffW z).hasFDerivAt).comp z.2 h1
    rw [h2.hasDerivAt.deriv]
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.inr_apply]
  rw [heq]
  exact hderivVal

end Work.RPB.B5
