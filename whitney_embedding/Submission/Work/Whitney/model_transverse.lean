import Mathlib
import Submission.Work.Whitney.LocalModel
import Submission.Work.Whitney.TransverseAux
import Submission.Work.Whitney.model_fderiv_e0
import Submission.Work.Whitney.model_fderiv_neg_e0

namespace Work.Whitney

open scoped Manifold ContDiff
open Set Filter Topology

/-- The self-intersection of Whitney's local model `model n : ℝⁿ → ℝⁿ × ℝⁿ` (defined in `Submission/Work/Whitney/LocalModel.lean`) is *transverse*: the "two sheets" linear endomorphism `(u, v) ↦ D model (e0 n) u + D model (-(e0 n)) v` of `ℝⁿ × ℝⁿ` (the `coprod` of the two derivatives) is invertible, i.e. its determinant is nonzero. -/
theorem model_transverse (n : ℕ) [NeZero n] :
    LinearMap.det (((fderiv ℝ (Work.Whitney.model n) (Work.Whitney.e0 n)).coprod
        (fderiv ℝ (Work.Whitney.model n) (-(Work.Whitney.e0 n)))) :
      ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ))) ≠ 0 := by
  have hcop : (((fderiv ℝ (Work.Whitney.model n) (Work.Whitney.e0 n)).coprod
        (fderiv ℝ (Work.Whitney.model n) (-(Work.Whitney.e0 n)))) :
      ((Fin n → ℝ) × (Fin n → ℝ)) →ₗ[ℝ] ((Fin n → ℝ) × (Fin n → ℝ))) = C n := by
    apply LinearMap.ext
    intro p
    rw [ContinuousLinearMap.coe_coprod, LinearMap.coprod_apply, ContinuousLinearMap.coe_coe,
      ContinuousLinearMap.coe_coe, model_fderiv_e0 n p.1, model_fderiv_neg_e0 n p.2,
      C_apply]
    rfl
  rw [hcop]
  exact det_C_ne_zero n

end Work.Whitney
