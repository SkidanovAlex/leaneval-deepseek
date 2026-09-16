import Mathlib
import Submission.Commons.Topology.Algebra.Valued.summable_of_tendsto_v_zero

open scoped WithZero

namespace Commons.Topology.Algebra.Valued

theorem summable_of_v_le_exp_tendsto {K : Type*} [Field K] [Valued K ℤᵐ⁰] [CompleteSpace K] [NonarchimedeanAddGroup K] {f : ℕ → K} {a : ℕ → ℤ} (ha : Filter.Tendsto a Filter.atTop Filter.atBot) (h : ∀ i : ℕ, Valued.v (f i) ≤ WithZero.exp (a i)) : Summable f := by
  apply summable_of_tendsto_v_zero
  intro n
  filter_upwards [Filter.tendsto_atBot.mp ha (n - 1)] with k hk
  calc Valued.v (f k) ≤ WithZero.exp (a k) := h k
    _ < WithZero.exp n := by rw [WithZero.exp_lt_exp]; omega

end Commons.Topology.Algebra.Valued
