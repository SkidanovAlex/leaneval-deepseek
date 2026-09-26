import Mathlib
import Submission.Work.Kernels.Kernels
import Submission.Work.Asymptotics.MiddleRange.exists_j_sub_lower_lambda_near_I
import Submission.Work.Asymptotics.MiddleRange.exists_lambdaFun_lipschitz
import Submission.Work.Rigidity.LambdaAnharmonic

namespace Work.Asymptotics

/-! ## `S` moves points near `i` by at most twice their distance to `i`

For the second `λ`-factor `λ τ + λ z - 1 = λ z - λ (S τ)` of the factorization of `j τ - j z` we
need `λ` to be applied at two points of `ℍ` that are both close to `i`; since the elliptic point
`i` is fixed by `S`, the point `S τ` is close to `i` as soon as `τ` is.  The explicit estimate
below (`‖S τ - i‖ ≤ 2 ‖τ - i‖` on the disc of radius `1/2`) is all that is used. -/

/-- On the Euclidean disc of radius `1/2` around `i`, the involution `S : τ ↦ -1/τ` does not move
points more than twice as far from `i`. -/
private lemma norm_S_smul_sub_I_le (τ : UpperHalfPlane) (h : ‖(τ : ℂ) - Complex.I‖ < 1 / 2) :
    ‖((ModularGroup.S • τ : UpperHalfPlane) : ℂ) - Complex.I‖ ≤ 2 * ‖(τ : ℂ) - Complex.I‖ := by
  have hτ : (τ : ℂ) ≠ 0 := UpperHalfPlane.ne_zero τ
  have hnorm : (1 : ℝ)/2 ≤ ‖(τ : ℂ)‖ := by
    have h1 : ‖(Complex.I : ℂ)‖ ≤ ‖(Complex.I : ℂ) - (τ : ℂ)‖ + ‖(τ : ℂ)‖ := by
      have h2 := norm_add_le ((Complex.I : ℂ) - (τ : ℂ)) (τ : ℂ)
      rw [sub_add_cancel] at h2
      exact h2
    rw [Complex.norm_I, norm_sub_rev] at h1
    linarith
  have hkey : ((ModularGroup.S • τ : UpperHalfPlane) : ℂ) - Complex.I
      = -((Complex.I * ((τ : ℂ) - Complex.I)) / (τ : ℂ)) := by
    rw [Work.Rigidity.coe_S_smul]
    field_simp
    rw [mul_sub, Complex.I_mul_I]
    ring
  rw [hkey, norm_neg, norm_div, norm_mul, Complex.norm_I, one_mul]
  rw [div_le_iff₀ (norm_pos_iff.mpr hτ)]
  nlinarith [norm_nonneg ((τ : ℂ) - Complex.I), hnorm]

/-- **The `j`-difference near `i` dominates `‖τ - z‖ ‖z - S τ‖.**

The exact factorization `j τ - j z = (λ τ - λ z)(λ τ + λ z - 1) Ψ` of
`Work.Asymptotics.MiddleRange.exists_j_sub_lower_lambda_near_I`, together with the local
bi-Lipschitzianity of `λ` at `i` (`Work.Asymptotics.MiddleRange.exists_lambdaFun_lipschitz`),
gives `‖j τ - j z‖ ≥ c₁ c₂² ‖τ - z‖ ‖z - S τ‖` on a neighbourhood of `(i, i)`: the second
`λ`-factor is `λ τ + λ z - 1 = λ z - λ (S τ)`, a difference of `λ` at the two points `z` and
`S τ`, both of which are close to `i` because `S i = i`. -/
theorem jDiff_lower_near_I :
    ∃ ρ c : ℝ, 0 < ρ ∧ 0 < c ∧ ∀ τ z : UpperHalfPlane,
      ‖(τ : ℂ) - Complex.I‖ < ρ → ‖(z : ℂ) - Complex.I‖ < ρ →
      c * ‖(τ : ℂ) - (z : ℂ)‖ * ‖(z : ℂ) - ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)‖ ≤
        ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := by
  obtain ⟨ρ₁, hρ₁, c₁, hc₁, hb₁⟩ :=
    Work.Asymptotics.MiddleRange.exists_j_sub_lower_lambda_near_I
  obtain ⟨ρ₂, hρ₂, c₂, hc₂, hb₂⟩ :=
    Work.Asymptotics.MiddleRange.exists_lambdaFun_lipschitz UpperHalfPlane.I
  have hρpos : 0 < min (min ρ₁ ρ₂) (min (ρ₂ / 2) (1 / 2)) :=
    lt_min (lt_min hρ₁ hρ₂) (lt_min (by linarith) (by norm_num))
  refine ⟨min (min ρ₁ ρ₂) (min (ρ₂ / 2) (1 / 2)), c₁ * c₂ ^ 2, hρpos, by positivity, ?_⟩
  intro τ z hτ hz
  have hτρ₁ : ‖(τ : ℂ) - Complex.I‖ < ρ₁ :=
    lt_of_lt_of_le hτ (le_trans (min_le_left _ _) (min_le_left _ _))
  have hzρ₁ : ‖(z : ℂ) - Complex.I‖ < ρ₁ :=
    lt_of_lt_of_le hz (le_trans (min_le_left _ _) (min_le_left _ _))
  have hτρ₂ : ‖(τ : ℂ) - Complex.I‖ < ρ₂ :=
    lt_of_lt_of_le hτ (le_trans (min_le_left _ _) (min_le_right _ _))
  have hzρ₂ : ‖(z : ℂ) - Complex.I‖ < ρ₂ :=
    lt_of_lt_of_le hz (le_trans (min_le_left _ _) (min_le_right _ _))
  have hτ2 : ‖(τ : ℂ) - Complex.I‖ < ρ₂ / 2 :=
    lt_of_lt_of_le hτ (le_trans (min_le_right _ _) (min_le_left _ _))
  have hτ12 : ‖(τ : ℂ) - Complex.I‖ < 1 / 2 :=
    lt_of_lt_of_le hτ (le_trans (min_le_right _ _) (min_le_right _ _))
  have hτρ₂' : ‖(τ : ℂ) - ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)‖ < ρ₂ := by
    rw [UpperHalfPlane.coe_I]; exact hτρ₂
  have hzρ₂' : ‖(z : ℂ) - ((UpperHalfPlane.I : UpperHalfPlane) : ℂ)‖ < ρ₂ := by
    rw [UpperHalfPlane.coe_I]; exact hzρ₂
  have hSτ : ‖((ModularGroup.S • τ : UpperHalfPlane) : ℂ) - Complex.I‖ < ρ₂ := by
    have h := norm_S_smul_sub_I_le τ hτ12
    linarith
  have h1 : c₂ * ‖(τ : ℂ) - (z : ℂ)‖ ≤
      ‖Work.Kernels.lambdaFun τ - Work.Kernels.lambdaFun z‖ := hb₂ τ z hτρ₂' hzρ₂'
  have h2 : c₂ * ‖(z : ℂ) - ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)‖ ≤
      ‖Work.Kernels.lambdaFun z - Work.Kernels.lambdaFun (ModularGroup.S • τ)‖ := by
    refine hb₂ z (ModularGroup.S • τ) hzρ₂' ?_
    rw [UpperHalfPlane.coe_I]; exact hSτ
  have h3 : Work.Kernels.lambdaFun τ + Work.Kernels.lambdaFun z - 1
      = Work.Kernels.lambdaFun z - Work.Kernels.lambdaFun (ModularGroup.S • τ) := by
    rw [Work.Rigidity.lambdaFun_S_eq]
    ring
  have hJ : c₁ * ‖Work.Kernels.lambdaFun τ - Work.Kernels.lambdaFun z‖ *
      ‖Work.Kernels.lambdaFun τ + Work.Kernels.lambdaFun z - 1‖
      ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := hb₁ τ z hτρ₁ hzρ₁
  calc c₁ * c₂ ^ 2 * ‖(τ : ℂ) - (z : ℂ)‖ *
        ‖(z : ℂ) - ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)‖
      = c₁ * (c₂ * ‖(τ : ℂ) - (z : ℂ)‖) *
          (c₂ * ‖(z : ℂ) - ((ModularGroup.S • τ : UpperHalfPlane) : ℂ)‖) := by ring
    _ ≤ c₁ * ‖Work.Kernels.lambdaFun τ - Work.Kernels.lambdaFun z‖ *
          ‖Work.Kernels.lambdaFun τ + Work.Kernels.lambdaFun z - 1‖ := by
        refine mul_le_mul (mul_le_mul_of_nonneg_left h1 hc₁.le) ?_ (by positivity) (by positivity)
        rw [h3]
        exact h2
    _ ≤ ‖Work.Kernels.jInvariantFun τ - Work.Kernels.jInvariantFun z‖ := hJ

end Work.Asymptotics
