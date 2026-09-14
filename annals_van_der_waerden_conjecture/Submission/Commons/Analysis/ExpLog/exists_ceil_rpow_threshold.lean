import Mathlib.Algebra.Group.Nat.Defs
import Mathlib.Order.Filter.AtTopBot.Defs

open Filter

namespace Commons.Analysis.ExpLog

/-- For every `M ≥ 1` there is a function `B : ℕ → ℕ` such that eventually
`H ≤ (B H)^M` and eventually `M < B H`.  (The choice `B H = H + M + 1`
works for every `H`.) -/
theorem exists_ceil_rpow_threshold (M : ℕ) (hM : 1 ≤ M) :
    ∃ B : ℕ → ℕ, (∀ᶠ H : ℕ in atTop, H ≤ (B H) ^ M) ∧
      (∀ᶠ H : ℕ in atTop, M < B H) := by
  refine ⟨fun H => H + M + 1, ?_, ?_⟩
  · refine Filter.Eventually.of_forall ?_
    intro H
    have hle : H ≤ H + M + 1 := by omega
    have hMpos : M ≠ 0 := by omega
    exact hle.trans (Nat.le_self_pow hMpos (H + M + 1))
  · refine Filter.Eventually.of_forall ?_
    intro H
    change M < H + M + 1
    omega

end Commons.Analysis.ExpLog