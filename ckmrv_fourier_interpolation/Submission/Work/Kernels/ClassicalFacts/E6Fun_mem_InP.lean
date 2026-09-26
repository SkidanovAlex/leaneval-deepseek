import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.ModerateGrowth

namespace Work.Kernels.ClassicalFacts

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

/-- The modular form `E₆` is holomorphic on `ℍ` with at worst polynomial growth, i.e. it lies
in the class `𝒫 = Work.Kernels.InP` of CKMRV.  Concretely Mathlib's
`ModularFormClass.exists_bound` gives `‖E₆ τ‖ ≤ C * max 1 ((im τ)⁻¹ ^ 6)`, and the right-hand
side is bounded by `max C 0 * ((im τ)⁻¹ ^ 6 + ‖τ‖ ^ 0)`. -/
lemma E6Fun_mem_InP : Work.Kernels.InP Work.Kernels.E6Fun := by
  constructor
  · -- holomorphy
    exact ModularFormClass.holo ModularForm.E₆
  · -- moderate growth
    obtain ⟨C, hC⟩ :=
      ModularFormClass.exists_bound (k := 6) (by norm_num) (Γ := 𝒮ℒ) (ModularForm.E₆)
    refine ⟨max C 0, 6, 0, le_max_right _ _, by norm_num, by norm_num, fun τ _ => ?_⟩
    have h2 : 1 / τ.im ^ (6:ℤ) = ((τ.im:ℝ)^6)⁻¹ := by
      rw [show (6:ℤ) = ((6:ℕ):ℤ) by norm_num, zpow_natCast, one_div]
    have h1 : (τ.im)⁻¹ ^ (6:ℝ) = ((τ.im:ℝ)^6)⁻¹ := by
      rw [show (6:ℝ) = ((6:ℕ):ℝ) by norm_num, Real.rpow_natCast, inv_pow]
    have hmaxnn : (0:ℝ) ≤ max 1 (1 / τ.im ^ (6:ℤ)) := le_trans zero_le_one (le_max_left _ _)
    have hb : max (1:ℝ) (1 / τ.im ^ (6:ℤ)) ≤ (τ.im)⁻¹ ^ (6:ℝ) + ‖(τ:ℂ)‖ ^ (0:ℝ) := by
      have hu : (0:ℝ) ≤ ((τ.im:ℝ)^6)⁻¹ := inv_nonneg.mpr (pow_nonneg τ.im_pos.le 6)
      rw [Real.rpow_zero, h1, h2]
      exact max_le (by linarith) (by linarith)
    calc ‖Work.Kernels.E6Fun τ‖ ≤ C * max 1 (1 / τ.im ^ (6:ℤ)) := hC τ
      _ ≤ max C 0 * max 1 (1 / τ.im ^ (6:ℤ)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hmaxnn
      _ ≤ max C 0 * ((τ.im)⁻¹ ^ (6:ℝ) + ‖(τ:ℂ)‖ ^ (0:ℝ)) :=
            mul_le_mul_of_nonneg_left hb (le_max_right _ _)

end Work.Kernels.ClassicalFacts
