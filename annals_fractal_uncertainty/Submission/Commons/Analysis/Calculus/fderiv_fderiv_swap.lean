import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Order.CompletePartialOrder

namespace Commons.Analysis.Calculus

/-- The two mixed second directional derivatives of a `C²` function on `Fin d → ℂ` commute:
`fderiv ℝ (fun w => fderiv ℝ h w a) z b = fderiv ℝ (fun w => fderiv ℝ h w b) z a`. -/
theorem fderiv_fderiv_swap {d : ℕ} {h : (Fin d → ℂ) → ℂ} (hh : ContDiff ℝ 2 h) (a b z : Fin d → ℂ) :
    fderiv ℝ (fun w => fderiv ℝ h w a) z b = fderiv ℝ (fun w => fderiv ℝ h w b) z a := by
  -- `fderiv ℝ h` is differentiable at `z`, since `h` is `C²`.
  have hF : DifferentiableAt ℝ (fderiv ℝ h) z :=
    (hh.fderiv_right (m := 1) (by norm_num)).contDiffAt.differentiableAt (by norm_num)
  -- The derivative of `w ↦ fderiv ℝ h w v` is `(fderiv ℝ (fderiv ℝ h) z).flip v`.
  have key : ∀ v : Fin d → ℂ, fderiv ℝ (fun w => fderiv ℝ h w v) z
      = (fderiv ℝ (fderiv ℝ h) z).flip v := by
    intro v
    rw [fderiv_clm_apply (c := fderiv ℝ h) (u := fun _ : Fin d → ℂ => v) (x := z) hF
      (differentiableAt_const v)]
    simp
  rw [key a, key b]
  simp only [ContinuousLinearMap.flip_apply]
  -- Symmetry of the second derivative of `h` at `z`.
  exact (hh.contDiffAt.isSymmSndFDerivAt (by norm_num)).eq b a

end Commons.Analysis.Calculus