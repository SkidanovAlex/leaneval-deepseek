import Mathlib.Topology.Algebra.InfiniteSum.Nonarchimedean
import Submission.Commons.Topology.Algebra.Valued.exp_balls_is_basis

open scoped Topology WithZero
open Filter

namespace Commons.Topology.Algebra.Valued

/-- In a complete non-archimedean valued field, a sequence is summable as soon as its
valuations tend to `0` (in the sense that for every integer exponent `n` the valuations are
eventually `< exp n`).  (Reduces to `NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero`
plus the fact that the balls `{x | v x < exp n}` form a basis of neighbourhoods of `0`.) -/
theorem summable_of_tendsto_v_zero {K : Type*} [Field K] [Valued K (WithZero (Multiplicative ℤ))]
    [CompleteSpace K] [NonarchimedeanAddGroup K] {f : ℕ → K}
    (h : ∀ n : ℤ, ∀ᶠ k in atTop, Valued.v (f k) < WithZero.exp n) : Summable f := by
  rw [NonarchimedeanAddGroup.summable_iff_tendsto_cofinite_zero]
  rw [Nat.cofinite_eq_atTop, tendsto_def]
  intro U hU
  obtain ⟨n, hn⟩ := exp_balls_is_basis (K := K) U hU
  filter_upwards [h n] with k hk
  exact hn hk

end Commons.Topology.Algebra.Valued