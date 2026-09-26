import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.ModerateGrowth

namespace Work.Kernels.ClassicalFacts

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

/-- The modular discriminant `Δ = q ∏ (1 - qⁿ)²⁴` lies in the class `𝒫 = Work.Kernels.InP`:
it is holomorphic on `ℍ` and of moderate growth there.

Holomorphy is `CuspFormClass.holo` applied to the cusp form `CuspForm.discriminant`.
For the growth we use `CuspFormClass.exists_bound`, which for a cusp form of weight `k`
gives `‖f τ‖ ≤ C / (im τ) ^ (k / 2)`; for `k = 12` this reads
`‖Δ τ‖ ≤ C / (im τ) ^ 6 = C * ((im τ)⁻¹) ^ 6`, a moderate growth bound with exponents
`β = 6`, `γ = 0`.  (Cuspidality is used here in an essential way: a general modular form
of weight `12` is only bounded by `C * max 1 ((im τ)⁻¹ ^ 12)`, which is still moderate, so
the argument works either way, but the cuspidal bound is what is available and is sharper.) -/
lemma DeltaFun_mem_InP : Work.Kernels.InP Work.Kernels.DeltaFun := by
  obtain ⟨C, hC⟩ := CuspFormClass.exists_bound (CuspForm.discriminant)
  refine ⟨CuspFormClass.holo CuspForm.discriminant, ?_⟩
  refine ⟨max C 0, 6, 0, le_max_right _ _, by norm_num, le_rfl, fun τ _ => ?_⟩
  have h := hC τ
  have hk : ((12:ℤ) / 2 : ℝ) = (6:ℝ) := by norm_num
  rw [hk] at h
  -- Rewrite the reciprocal power: `(τ.im ^ 6)⁻¹ = (τ.im)⁻¹ ^ 6`.
  have h1 : ((τ.im) ^ (6:ℝ))⁻¹ = (τ.im)⁻¹ ^ (6:ℝ) :=
    (Real.inv_rpow τ.im_pos.le (6:ℝ)).symm
  rw [Real.rpow_zero]
  have h2 : (0:ℝ) ≤ max C 0 := le_max_right _ _
  calc ‖Work.Kernels.DeltaFun τ‖ = ‖CuspForm.discriminant τ‖ := rfl
    _ ≤ C / τ.im ^ (6:ℝ) := h
    _ = C * ((τ.im)⁻¹ ^ (6:ℝ)) := by rw [div_eq_mul_inv, h1]
    _ ≤ max C 0 * ((τ.im)⁻¹ ^ (6:ℝ)) :=
          mul_le_mul_of_nonneg_right (le_max_left C 0) (by positivity)
    _ ≤ max C 0 * ((τ.im)⁻¹ ^ (6:ℝ) + 1) :=
          mul_le_mul_of_nonneg_left (by linarith) h2

end Work.Kernels.ClassicalFacts
