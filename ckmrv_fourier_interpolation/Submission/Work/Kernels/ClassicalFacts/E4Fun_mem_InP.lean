import Mathlib
import Submission.Work.Kernels.Classical
import Submission.Work.Kernels.ModerateGrowth

open UpperHalfPlane ModularForm ModularGroup Matrix
open scoped MatrixGroups ModularForm Modular Manifold Bundle

namespace Work.Kernels.ClassicalFacts

/-- The weight-four Eisenstein series `E₄` is a modular form of weight `4` for `𝒮ℒ = SL(2, ℤ)`,
so Mathlib's bound `ModularFormClass.exists_bound` gives
`‖E₄ τ‖ ≤ C * max 1 (1 / (im τ) ^ 4)`; this elementary inequality rewrites that bound in the
shape required by the moderate-growth condition `Work.Kernels.ModerateGrowthOn`. -/
private lemma max_one_inv_pow_four_le (t : ℝ) (ht : 0 < t) :
    max 1 (1 / t ^ (4:ℤ)) ≤ t⁻¹ ^ (4:ℝ) + 1 := by
  have h1 : (1 : ℝ) ≤ t⁻¹ ^ (4:ℝ) + 1 := by
    have : 0 ≤ t⁻¹ ^ (4:ℝ) := Real.rpow_nonneg (inv_nonneg.mpr ht.le) _
    linarith
  have h2 : 1 / t ^ (4:ℤ) ≤ t⁻¹ ^ (4:ℝ) + 1 := by
    have heq : t⁻¹ ^ (4:ℝ) = 1 / t ^ (4:ℤ) := by
      rw [show (4:ℝ) = ((4:ℕ):ℝ) from by norm_num, Real.rpow_natCast, inv_pow, inv_eq_one_div]
      norm_num
    rw [heq]
    have : 0 ≤ 1 / t ^ (4:ℤ) := by positivity
    linarith
  exact max_le h1 h2

/-- The classical weight-four Eisenstein series `E₄ = 1 + 240 ∑ σ₃(n) qⁿ` lies in the class `𝒫`:
it is holomorphic on `ℍ` and of moderate growth there.

Holomorphy is Mathlib's `ModularForm.holo'` for `ModularForm.E₄`.  For the growth we use the
level-one bound `ModularFormClass.exists_bound`, which for a weight-`k` modular form gives
`‖f τ‖ ≤ C * max 1 (1 / (im τ) ^ k)`; for `k = 4` this is a moderate growth bound with
exponents `β = 4`, `γ = 0`. -/
lemma E4Fun_mem_InP : Work.Kernels.InP Work.Kernels.E4Fun := by
  obtain ⟨C, hC⟩ := ModularFormClass.exists_bound (by norm_num : (0:ℤ) ≤ 4) (ModularForm.E₄)
  refine ⟨(ModularForm.E₄).holo', ?_⟩
  refine ⟨max C 0, 4, 0, le_max_right C 0, by norm_num, le_rfl, fun τ _ => ?_⟩
  have h1 : max 1 (1 / τ.im ^ (4:ℤ)) ≤ (τ.im)⁻¹ ^ (4:ℝ) + ‖(τ : ℂ)‖ ^ (0:ℝ) := by
    rw [Real.rpow_zero]
    exact max_one_inv_pow_four_le τ.im τ.im_pos
  calc ‖Work.Kernels.E4Fun τ‖ = ‖ModularForm.E₄ τ‖ := rfl
    _ ≤ C * max 1 (1 / τ.im ^ (4:ℤ)) := hC τ
    _ ≤ max C 0 * max 1 (1 / τ.im ^ (4:ℤ)) := by
          apply mul_le_mul_of_nonneg_right (le_max_left C 0)
          positivity
    _ ≤ max C 0 * ((τ.im)⁻¹ ^ (4:ℝ) + ‖(τ : ℂ)‖ ^ (0:ℝ)) :=
          mul_le_mul_of_nonneg_left h1 (le_max_right C 0)

end Work.Kernels.ClassicalFacts
