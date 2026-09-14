import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.InnerProductSpace.Dual

namespace Commons.Analysis.GaussianMeasure

open Real
open scoped Real

/-- The weighted Laplacian `M u = -Δu + ⟪∇f, ∇u⟫` is `ℝ`-linear in `u`. -/
theorem laplacian_weighted_linear {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] (f : E → ℝ) (a b : ℝ) (u v : E → ℝ)
    (hu : ContDiff ℝ 2 u) (hv : ContDiff ℝ 2 v) :
    (fun x => - Laplacian.laplacian (fun y => a * u y + b * v y) x
        + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
            ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ (fun y => a * u y + b * v y) x)))
      = (fun x => a * (- Laplacian.laplacian u x
            + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)))
          + b * (- Laplacian.laplacian v x
            + inner ℝ ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ f x))
                ((InnerProductSpace.toDual ℝ E).symm (fderiv ℝ v x)))) := by
  funext x
  have hu2 : ContDiffAt ℝ 2 u x := hu.contDiffAt
  have hv2 : ContDiffAt ℝ 2 v x := hv.contDiffAt
  have hcu : ContDiffAt ℝ 2 (fun y => a * u y) x := by
    simpa [Pi.mul_apply] using (contDiffAt_const (c := a) (x := x)).mul hu2
  have hcv : ContDiffAt ℝ 2 (fun y => b * v y) x := by
    simpa [Pi.mul_apply] using (contDiffAt_const (c := b) (x := x)).mul hv2
  have hdu : DifferentiableAt ℝ (fun y => a * u y) x := hcu.differentiableAt (by norm_num)
  have hdv : DifferentiableAt ℝ (fun y => b * v y) x := hcv.differentiableAt (by norm_num)
  -- split the combined function into a syntactic sum of two functions
  have hsplit : (fun y => a * u y + b * v y)
      = (fun y => a * u y) + (fun y => b * v y) := by
    funext y; rfl
  rw [hsplit]
  have h1 : (fun y => a * u y) = a • u := by funext y; rfl
  have h1' : (fun y => b * v y) = b • v := by funext y; rfl
  -- linearity of the Laplacian
  have hL : Laplacian.laplacian ((fun y => a * u y) + (fun y => b * v y)) x
      = a * Laplacian.laplacian u x + b * Laplacian.laplacian v x := by
    rw [ContDiffAt.laplacian_add hcu hcv, h1, h1',
      InnerProductSpace.laplacian_smul a hu2, InnerProductSpace.laplacian_smul b hv2,
      smul_eq_mul, smul_eq_mul]
  -- linearity of the gradient
  have hG : fderiv ℝ ((fun y => a * u y) + (fun y => b * v y)) x
      = a • fderiv ℝ u x + b • fderiv ℝ v x := by
    rw [fderiv_add hdu hdv, h1, h1',
      fderiv_const_smul (hu2.differentiableAt (by norm_num)) a,
      fderiv_const_smul (hv2.differentiableAt (by norm_num)) b]
  -- the inner product factor
  have hT : (InnerProductSpace.toDual ℝ E).symm
        (fderiv ℝ ((fun y => a * u y) + (fun y => b * v y)) x)
      = a • (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ u x)
        + b • (InnerProductSpace.toDual ℝ E).symm (fderiv ℝ v x) := by
    rw [hG]
    simp only [map_add, map_smul]
  rw [hL, hT]
  simp only [inner_add_right, inner_smul_right]
  ring

end Commons.Analysis.GaussianMeasure
