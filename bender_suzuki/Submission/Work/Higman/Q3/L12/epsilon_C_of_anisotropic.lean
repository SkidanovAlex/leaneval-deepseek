import Mathlib
import Submission.Work.Higman.Family

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3.L12

theorem epsilon_C_of_anisotropic {F : Type*} [Field F] [CharP F 2] [Finite F]
    (θ : F ≃+* F) (ε : F)
    (hani : ∀ u : F × F, u ≠ 0 → Work.Higman.cCocycle F θ ε u u ≠ 0) :
    ∀ ρ : F, ε ≠ ρ⁻¹ + θ ρ ^ 2 * ρ := by
  -- Contrapositive: a `ρ` with `ε = ρ⁻¹ + (θ ρ)² ρ` gives a nonzero `u` with
  -- `cCocycle F θ ε u u = 0`, contradicting anisotropy.
  intro ρ hρ
  rcases eq_or_ne ρ 0 with h0 | hne
  · -- `ρ = 0` forces `ε = 0`; then `u = (1, 1)` is a zero of the squaring form.
    subst h0
    have hε0 : ε = 0 := by simpa using hρ
    have hval : Work.Higman.cCocycle F θ ε (1, 1) (1, 1) = 0 := by
      simp only [Work.Higman.cCocycle, hε0, zero_mul, mul_one, map_one]
      simp [CharTwo.add_self_eq_zero]
    exact hani (1, 1) (by simp) hval
  · -- `ρ ≠ 0`: the nonzero vector `u = (ρ², 1)` has vanishing squaring form.
    have hsqrt : Work.Higman.sqrtF F (ρ ^ 2) = ρ := by
      have h : ρ ^ 2 = (frobeniusEquiv F 2) ρ := by
        rw [frobeniusEquiv_apply, frobenius_def]
      rw [Work.Higman.sqrtF, h]
      exact Equiv.symm_apply_apply _ _
    have hgoal : ρ ^ 2 * θ (ρ ^ 2) + ε * ρ + 1 = 0 := by
      have hkey : ε * ρ = 1 + ρ ^ 2 * (θ ρ) ^ 2 := by
        rw [hρ, add_mul, inv_mul_cancel₀ hne]
        ring
      rw [map_pow, hkey]
      rw [show ρ ^ 2 * (θ ρ) ^ 2 + (1 + ρ ^ 2 * (θ ρ) ^ 2) + 1 =
        (ρ ^ 2 * (θ ρ) ^ 2 + ρ ^ 2 * (θ ρ) ^ 2) + (1 + 1) from by ring]
      rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
    have hval : Work.Higman.cCocycle F θ ε (ρ ^ 2, 1) (ρ ^ 2, 1) = 0 := by
      show ρ ^ 2 * θ (ρ ^ 2) + ε * (Work.Higman.sqrtF F (ρ ^ 2) * θ (1 * 1)) + 1 * 1 = 0
      rw [one_mul, map_one, mul_one, hsqrt, hgoal]
    exact hani (ρ ^ 2, 1) (by simp) hval

end Work.Higman.Q3.L12
