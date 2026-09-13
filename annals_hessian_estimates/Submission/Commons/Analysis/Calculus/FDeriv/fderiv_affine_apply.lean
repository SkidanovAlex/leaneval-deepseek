import Mathlib.Algebra.Order.Archimedean.Real.Hom
import Mathlib.Analysis.Calculus.FDeriv.Add

namespace Commons.Analysis.Calculus.FDeriv

theorem fderiv_affine_apply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F] {u : E → F} {y x : E} {a b : ℝ}
    (hu : DifferentiableAt ℝ u (b • x + y)) :
    fderiv ℝ (fun z => a • u (b • z + y)) x = (a * b) • fderiv ℝ u (b • x + y) := by
  have hg : HasFDerivAt (fun z : E => b • z + y) (b • ContinuousLinearMap.id ℝ E) x := by
    simpa using ((hasFDerivAt_id x).const_smul (𝕜 := ℝ) b).add_const y
  have hu' : HasFDerivAt u (fderiv ℝ u (b • x + y)) (b • x + y) := hu.hasFDerivAt
  have hc : HasFDerivAt (fun z => u (b • z + y))
      ((fderiv ℝ u (b • x + y)).comp (b • ContinuousLinearMap.id ℝ E)) x :=
    hu'.comp x hg
  have hd : DifferentiableAt ℝ (fun z => u (b • z + y)) x := hc.differentiableAt
  rw [show (fun z => a • u (b • z + y)) = a • (fun z => u (b • z + y)) from rfl]
  rw [fderiv_const_smul hd a, hc.fderiv]
  ext v
  simp [smul_smul]

end Commons.Analysis.Calculus.FDeriv