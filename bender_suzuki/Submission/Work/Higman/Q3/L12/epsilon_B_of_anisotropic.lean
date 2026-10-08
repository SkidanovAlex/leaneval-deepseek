import Mathlib
import Submission.Work.Higman.Family

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Higman.Q3.L12

theorem epsilon_B_of_anisotropic {F : Type*} [Field F] [CharP F 2] (θ : F ≃+* F) (ε : F)
    (hani : ∀ u : F × F, u ≠ 0 → Work.Higman.bCocycle F θ ε u u ≠ 0) :
    ε ≠ 0 ∧ ∀ ρ : F, ε ≠ ρ⁻¹ + θ ρ := by
  -- `ε ≠ 0` from the anisotropy of the squaring form on `(1, 1)`.
  have hε : ε ≠ 0 := by
    intro h
    have h1 : Work.Higman.bCocycle F θ ε (1, 1) (1, 1) = ε := by
      simp only [Work.Higman.bCocycle, map_one, mul_one]
      rw [add_right_comm, CharTwo.add_self_eq_zero, zero_add]
    exact hani (1, 1) (by simp) (by rw [h1, h])
  refine ⟨hε, ?_⟩
  intro ρ hρ
  rcases eq_or_ne ρ 0 with h0 | hne
  · -- `ρ = 0` forces `ε = 0`, contradicting the first conjunct.
    subst h0
    rw [inv_zero, map_zero, add_zero] at hρ
    exact hε hρ
  · -- `ρ ≠ 0`: the anisotropic vector `(ρ, 1)` would have vanishing squaring form.
    have hval : Work.Higman.bCocycle F θ ε (ρ, 1) (ρ, 1) = 0 := by
      have h1 : Work.Higman.bCocycle F θ ε (ρ, 1) (ρ, 1) = ρ * θ ρ + ε * ρ + 1 := by
        simp only [Work.Higman.bCocycle, map_one, mul_one]
      rw [h1, hρ, add_mul, inv_mul_cancel₀ hne]
      rw [mul_comm (θ ρ) ρ]
      rw [show ρ * θ ρ + (1 + ρ * θ ρ) + 1 = (ρ * θ ρ + ρ * θ ρ) + (1 + 1) from by ring,
        CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
    exact hani (ρ, 1) (by simp [hne]) hval

end Work.Higman.Q3.L12
