import Mathlib
import Submission.Work.CR.Flat.Polydisc
import Submission.Work.CR.Flat.Cauchy.holderNorm_le_sup_of_holomorphic

namespace Work.CR.Flat.Cauchy

/-- If a real-differentiable function `f : ℂⁿ → ℂ` has all its `∂̄`-coordinate derivatives
vanishing at `z`, then `f` is complex-differentiable at `z`. -/
theorem differentiableAt_complex_of_dbarCoord_eq_zero {n : ℕ} {f : (Fin n → ℂ) → ℂ} {z : Fin n → ℂ} (hf : DifferentiableAt ℝ f z) (h : ∀ j : Fin n, Work.CR.Flat.dbarCoord j f z = 0) : DifferentiableAt ℂ f z := by
  classical
  refine (differentiableAt_iff_restrictScalars ℝ hf).mpr
    ⟨∑ j : Fin n, (ContinuousLinearMap.proj j).smulRight ((fderiv ℝ f z) (Pi.single j 1)), ?_⟩
  ext v
  have hkey : ∀ j : Fin n,
      (fderiv ℝ f z) (Pi.single j (v j)) = v j * (fderiv ℝ f z) (Pi.single j 1) :=
    fun j => fderiv_single_eq_mul j (h j) (v j)
  have hA : (fderiv ℝ f z) v = ∑ j : Fin n, v j * (fderiv ℝ f z) (Pi.single j 1) := by
    conv_lhs => rw [← Finset.univ_sum_single v]
    rw [map_sum]
    exact Finset.sum_congr rfl fun j _ => hkey j
  rw [hA]
  change ((∑ j : Fin n, (ContinuousLinearMap.proj j).smulRight
      ((fderiv ℝ f z) (Pi.single j 1))) : (Fin n → ℂ) →L[ℂ] ℂ) v
    = ∑ j : Fin n, v j * (fderiv ℝ f z) (Pi.single j 1)
  simp only [sum_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.proj_apply, smul_eq_mul]

end Work.CR.Flat.Cauchy
