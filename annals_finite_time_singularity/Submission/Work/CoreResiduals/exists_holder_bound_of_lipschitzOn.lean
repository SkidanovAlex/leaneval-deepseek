import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.Stability.min_mul_le_max_mul_rpow

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.CoreResiduals

/-- A function that is `K`-Lipschitz in its second variable on the interval `[0, S]`
admits a `N₁`-Hölder bound with any exponent `α ≤ 1`.

The uniform constant is `N₁ = max K (2 * (K * S))`.  Indeed for `t, t' ∈ [0, S]`
the Lipschitz bound gives `‖f y t - f y t'‖ ≤ K * |t - t'|` *and* (using
`|t - t'| ≤ S`) the uniform bound `‖f y t - f y t'‖ ≤ 2 * (K * S)`; combining the
two with the elementary inequality `min (K * d) (2 * M) ≤ max K (2 * M) * d ^ α`
for `0 ≤ d` and `α ≤ 1` yields the claim. -/
theorem exists_holder_bound_of_lipschitzOn {X E : Type*} [NormedAddCommGroup E]
    {f : X → ℝ → E} {S K : ℝ} {α : NNReal} (hS : 0 ≤ S) (hK : 0 ≤ K) (hα : α ≤ 1)
    (h : ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ t' ∈ Set.Icc (0 : ℝ) S, ∀ y : X,
      ‖f y t - f y t'‖ ≤ K * |t - t'|) :
    ∃ N₁ : ℝ, ∀ y : X, ∀ t ∈ Set.Icc (0 : ℝ) S, ∀ t' ∈ Set.Icc (0 : ℝ) S,
      ‖f y t - f y t'‖ ≤ N₁ * |t - t'| ^ (α : ℝ) := by
  refine ⟨max K (2 * (K * S)), ?_⟩
  intro y t ht t' ht'
  have hd0 : 0 ≤ |t - t'| := abs_nonneg _
  have hdS : |t - t'| ≤ S := by
    rw [abs_sub_le_iff]
    exact ⟨by linarith [ht.2, ht'.1], by linarith [ht'.2, ht.1]⟩
  have hKS : 0 ≤ K * S := mul_nonneg hK hS
  have hb : ‖f y t - f y t'‖ ≤ K * |t - t'| := h t ht t' ht' y
  have hb2 : ‖f y t - f y t'‖ ≤ 2 * (K * S) := by
    calc ‖f y t - f y t'‖ ≤ K * |t - t'| := hb
      _ ≤ K * S := mul_le_mul_of_nonneg_left hdS hK
      _ ≤ 2 * (K * S) := by linarith
  exact le_trans (le_min hb hb2) (Work.Stability.min_mul_le_max_mul_rpow hK hKS hd0 hα)

end Work.CoreResiduals
