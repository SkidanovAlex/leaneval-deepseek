import Mathlib
import Submission.Work.Diff.STE.B3.VarCoef.Assembly

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3.VarCoef

theorem commMulPd {ι : Type*} [Fintype ι] [DecidableEq ι] (m : (ι → ℝ) → ℝ)
    (hm : ContDiff ℝ (⊤ : ℕ∞) m) (a : ι) (f : (ι → ℝ) → ℂ)
    (hf : Work.Diff.STE.B3.VarCoef.SmoothPer f) :
    Work.Diff.STE.B3.VarCoef.commOp (Work.Diff.STE.B3.VarCoef.mulOp m)
        (Work.Diff.STE.B3.VarCoef.pdOp a) f
      = -(Work.Diff.STE.B3.VarCoef.mulOp (Work.Diff.STE.pdR a m) f) := by
  funext x
  have hmd : DifferentiableAt ℝ m x := hm.contDiffAt.differentiableAt (by simp)
  have hfd : DifferentiableAt ℝ f x := hf.1.contDiffAt.differentiableAt (by simp)
  have hgm : DifferentiableAt ℝ (fun y : ι → ℝ => (m y : ℂ)) x :=
    Complex.ofRealCLM.differentiableAt.comp x hmd
  -- the product rule for `∂ₐ` and the chain rule for the real-to-complex coercion
  have hkey : fderiv ℝ (fun y : ι → ℝ => ((m y : ℝ) : ℂ) * f y) x
      = ((m x : ℝ) : ℂ) • fderiv ℝ f x + f x • (Complex.ofRealCLM.comp (fderiv ℝ m x)) := by
    rw [fderiv_fun_mul hgm hfd,
      show fderiv ℝ (fun y : ι → ℝ => (m y : ℂ)) x = Complex.ofRealCLM.comp (fderiv ℝ m x) by
        rw [show (fun y : ι → ℝ => (m y : ℂ)) = Complex.ofRealCLM ∘ m from rfl,
          fderiv_comp x Complex.ofRealCLM.differentiableAt hmd, ContinuousLinearMap.fderiv]]
  simp only [commOp_apply, mulOp, pdOp, Work.Diff.STE.pd, Work.Diff.STE.pdR, Pi.sub_apply,
    Pi.neg_apply]
  rw [show fderiv ℝ (mulOp m f) x (Pi.single a 1)
      = fderiv ℝ (fun y : ι → ℝ => ((m y : ℝ) : ℂ) * f y) x (Pi.single a 1) from rfl]
  rw [hkey]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, Complex.ofRealCLM_apply]
  ring

end Work.Diff.STE.B3.VarCoef
