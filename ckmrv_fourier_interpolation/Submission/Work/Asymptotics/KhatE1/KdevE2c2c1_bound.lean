import Mathlib
import Submission.Work.Asymptotics.KhatE1.Kdev8CoeffAux
import Submission.Work.Asymptotics.KhatE1.KdevE2CoeffDefs

namespace Work.Asymptotics.KhatE1

open UpperHalfPlane

noncomputable section

/-- `KdevE2c2` is half of the `z²`-coefficient `z2coef` of `M2plus`. -/
lemma KdevE2c2_eq_z2coef (τ : UpperHalfPlane) :
    KdevE2c2 τ = z2coef τ / 2 := by
  rw [KdevE2c2, z2coef]
  simp only [Work.Kernels.E14Fun, Work.Kernels.jInvariantFun, Work.Kernels.phi2,
    Work.Asymptotics.Compact.phi2t, Work.Asymptotics.Compact.tailC]
  field_simp
  ring

/-- `KdevE2c1` is half of the `z¹`-coefficient `Kdev8Z1` of the bracket. -/
lemma KdevE2c1_eq_Kdev8Z1 (ℓ : Work.Kernels.LogLambdaData) (τ : UpperHalfPlane) :
    KdevE2c1 ℓ τ = Kdev8Z1 ℓ τ / 2 := by
  rw [KdevE2c1, Kdev8Z1, Work.Asymptotics.Compact.tailC, Work.Asymptotics.Compact.R8_q1]
  field_simp
  ring

/-- The `z²`- and `z¹`-coefficients `KdevE2c2`, `KdevE2c1` of the deviation `KdevE2` (see
`Submission/Work/Asymptotics/KhatE1/KdevE2CoeffDefs.lean`) satisfy the funnel bound
`O((scale τ)^N ‖q(τ)‖)`.

Both reduce to already-proved bounds: `KdevE2c2 τ = z2coef τ / 2` and
`KdevE2c1 ℓ τ = Kdev8Z1 ℓ τ / 2` (`field_simp [Work.Asymptotics.Compact.tailC_ne_zero]` then
`ring` from the definitions of `KdevE2c2`, `KdevE2c1` in `KdevE2CoeffDefs.lean`, of `z2coef` and
`Kdev8Z1` in `Submission/Work/Asymptotics/KhatE1/Kdev_cusp0_strip_sharp.lean`; note
`E14Fun = E4Fun^2 * E6Fun`, `Kernels.phi2 = Compact.phi2t`, `R8_q1 = 3400704E₄ - 3456 j E₄`),
while `Work.Asymptotics.KhatE1.z2coef_bound` and `Work.Asymptotics.KhatE1.Kdev8Z1_bound`
(proved, same file) give `‖z2coef τ‖ ≤ C (scale τ)^N ‖q τ‖` and
`‖Kdev8Z1 ℓ τ‖ ≤ C (scale τ)^N ‖q τ‖` on the funnel. -/
theorem KdevE2c2c1_bound (ℓ : Work.Kernels.LogLambdaData) :
    ∃ C N : ℝ, 0 < C ∧ 0 ≤ N ∧
      (∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
        ‖Work.Asymptotics.KhatE1.KdevE2c2 τ‖
          ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖) ∧
      (∀ τ : UpperHalfPlane, Work.Asymptotics.Funnel τ →
        ‖Work.Asymptotics.KhatE1.KdevE2c1 ℓ τ‖
          ≤ C * (Work.Kernels.scale τ) ^ N * ‖Work.Kernels.qParamFun τ‖) := by
  obtain ⟨C₁, N₁, hC₁, hN₁, h₁⟩ := z2coef_bound
  obtain ⟨C₂, N₂, hC₂, hN₂, h₂⟩ := Kdev8Z1_bound ℓ
  refine ⟨max C₁ C₂ + 1, max N₁ N₂, by positivity, le_trans hN₁ (le_max_left _ _), ?_, ?_⟩
  · intro τ hτ
    have hs : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hs0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one hs
    have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
    rw [KdevE2c2_eq_z2coef τ]
    calc ‖z2coef τ / 2‖
        = ‖z2coef τ‖ / 2 := by rw [norm_div]; norm_num
      _ ≤ (C₁ * ‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ N₁) / 2 :=
          div_le_div_of_nonneg_right (h₁ τ hτ) (by norm_num)
      _ = C₁ / 2 * ‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ N₁ := by ring
      _ ≤ (max C₁ C₂ + 1) * ‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max N₁ N₂) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_right (by linarith [le_max_left C₁ C₂]) hq0)
            (Real.rpow_le_rpow_of_exponent_le hs (le_max_left _ _))
            (Real.rpow_nonneg hs0 _) (mul_nonneg (by positivity) hq0)
      _ = (max C₁ C₂ + 1) * Work.Kernels.scale τ ^ (max N₁ N₂)
            * ‖Work.Kernels.qParamFun τ‖ := by ring
  · intro τ hτ
    have hs : (1 : ℝ) ≤ Work.Kernels.scale τ := Work.Kernels.one_le_scale τ
    have hs0 : (0 : ℝ) ≤ Work.Kernels.scale τ := le_trans zero_le_one hs
    have hq0 : (0 : ℝ) ≤ ‖Work.Kernels.qParamFun τ‖ := norm_nonneg _
    rw [KdevE2c1_eq_Kdev8Z1 ℓ τ]
    calc ‖Kdev8Z1 ℓ τ / 2‖
        = ‖Kdev8Z1 ℓ τ‖ / 2 := by rw [norm_div]; norm_num
      _ ≤ (C₂ * ‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ N₂) / 2 :=
          div_le_div_of_nonneg_right (h₂ τ hτ) (by norm_num)
      _ = C₂ / 2 * ‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ N₂ := by ring
      _ ≤ (max C₁ C₂ + 1) * ‖Work.Kernels.qParamFun τ‖ * Work.Kernels.scale τ ^ (max N₁ N₂) :=
          mul_le_mul
            (mul_le_mul_of_nonneg_right (by linarith [le_max_right C₁ C₂]) hq0)
            (Real.rpow_le_rpow_of_exponent_le hs (le_max_right _ _))
            (Real.rpow_nonneg hs0 _) (mul_nonneg (by positivity) hq0)
      _ = (max C₁ C₂ + 1) * Work.Kernels.scale τ ^ (max N₁ N₂)
            * ‖Work.Kernels.qParamFun τ‖ := by ring

end

end Work.Asymptotics.KhatE1
