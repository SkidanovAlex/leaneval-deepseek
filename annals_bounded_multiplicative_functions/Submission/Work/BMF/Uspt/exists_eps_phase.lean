import Mathlib
import Submission.Work.BMF.vkford51_defs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.Uspt

/-- For every `b`, the `r`-th power `Yfun γ b ^ r` can be written as `ε b * ‖Yfun γ b‖ ^ r`
with a unimodular (hence norm `≤ 1`) phase `ε b`.  Concretely we take
`ε b = (‖Yfun γ b‖ / Yfun γ b) ^ r` (and `1` when `Yfun γ b = 0`). -/
theorem exists_eps_phase (k r M₁ M₂ : ℕ) (hr : 1 ≤ r) (γ : Fin k → ℝ) :
    ∃ ε : ℕ → ℂ, (∀ b, ‖ε b‖ ≤ 1) ∧
      ∀ b ∈ Finset.Icc 1 M₂,
        ε b * (Work.BMF.Yfun k M₁ γ b) ^ r = (((‖Work.BMF.Yfun k M₁ γ b‖ ^ r : ℝ)) : ℂ) := by
  have _ := hr
  refine ⟨fun b => if Work.BMF.Yfun k M₁ γ b = 0 then 1
      else ((‖Work.BMF.Yfun k M₁ γ b‖ : ℂ) / Work.BMF.Yfun k M₁ γ b) ^ r, ?_, ?_⟩
  · intro b
    dsimp only
    by_cases hy : Work.BMF.Yfun k M₁ γ b = 0
    · simp [hy]
    · rw [if_neg hy, norm_pow]
      apply pow_le_one₀ (norm_nonneg _)
      rw [norm_div]
      have h : ‖(((‖Work.BMF.Yfun k M₁ γ b‖ : ℝ) : ℂ))‖ = ‖Work.BMF.Yfun k M₁ γ b‖ := by
        simp
      rw [h]
      exact div_self_le_one _
  · intro b _
    dsimp only
    by_cases hy : Work.BMF.Yfun k M₁ γ b = 0
    · simp [hy, Complex.ofReal_pow]
    · rw [if_neg hy, ← mul_pow, div_mul_cancel₀ _ hy, Complex.ofReal_pow]

end Work.BMF.Uspt
