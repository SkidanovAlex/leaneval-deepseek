import Mathlib
import Submission.Work.NN.Newton.pushforward_setup

namespace Work.NN.Newton

/-- The derivative of `z ↦ DvCLM v z = ContinuousLinearMap.pi (fun l => fderiv ℝ (v l) z)`.

Both `DvCLM v` and `ContinuousLinearMap.pi` are built from the continuous-linear-map
"product" construction, which is a continuous linear equivalence
(`ContinuousLinearMap.piEquivL`).  Writing `F z = fun l => fderiv ℝ (v l) z`, we have
`DvCLM v = piEquivL ∘ F`; the chain rule combined with `hasFDerivAt_pi` gives the result. -/
lemma fderiv_DvCLM_apply {n : ℕ} {v : Fin n → Work.NN.Core.Cn n → ℂ} {x : Work.NN.Core.Cn n}
    (hd : ∀ l, DifferentiableAt ℝ (fun z => fderiv ℝ (v l) z) x) (h : Work.NN.Core.Cn n) :
    fderiv ℝ (Work.NN.Newton.DvCLM v) x h
      = ContinuousLinearMap.pi
          (fun l => fderiv ℝ (fun z => fderiv ℝ (v l) z) x h) := by
  let F : Work.NN.Core.Cn n → (Fin n → (Work.NN.Core.Cn n →L[ℝ] ℂ)) :=
    fun z l => fderiv ℝ (v l) z
  have hF : HasFDerivAt F
      (ContinuousLinearMap.pi (fun l => fderiv ℝ (fun z => fderiv ℝ (v l) z) x)) x := by
    rw [show F = (fun z l => fderiv ℝ (v l) z) from rfl]
    rw [hasFDerivAt_pi]
    intro l
    exact (hd l).hasFDerivAt
  let e : (Fin n → (Work.NN.Core.Cn n →L[ℝ] ℂ)) ≃L[ℝ]
      (Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n) :=
    ContinuousLinearMap.piEquivL ℝ (Work.NN.Core.Cn n) (fun _ : Fin n => ℂ)
  have hF' : HasFDerivAt F (fderiv ℝ F x) x := hF.fderiv.symm ▸ hF
  have hcomp : HasFDerivAt (fun z => e (F z))
      ((e : (Fin n → (Work.NN.Core.Cn n →L[ℝ] ℂ)) →L[ℝ]
          (Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)).comp
        (fderiv ℝ F x)) x :=
    HasFDerivAt.comp x e.hasFDerivAt hF'
  have hDv : fderiv ℝ (Work.NN.Newton.DvCLM v) x
      = (e : (Fin n → (Work.NN.Core.Cn n →L[ℝ] ℂ)) →L[ℝ]
          (Work.NN.Core.Cn n →L[ℝ] Work.NN.Core.Cn n)).comp
        (fderiv ℝ F x) := by
    rw [show Work.NN.Newton.DvCLM v = fun z => e (F z) from rfl]
    exact hcomp.fderiv
  rw [hDv, ContinuousLinearMap.comp_apply, hF.fderiv]
  rfl

end Work.NN.Newton
