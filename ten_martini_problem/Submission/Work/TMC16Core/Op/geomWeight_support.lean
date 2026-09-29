import Mathlib
import Submission.Work.TMC16Core.Defs

namespace Work.TMC16Core.Op

theorem geomWeight_support {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (n₀ : ℤ) (N : ℕ)
    (hb : n₀.natAbs ≤ N) :
    ∀ z : ℤ, (z = (N : ℤ) + 1 ∨ z = (N : ℤ) ∨ z = -((N : ℤ)) ∨ z = -((N : ℤ) + 1)) →
      ρ ^ ((z - n₀).natAbs) ≤ ρ ^ (N - n₀.natAbs) := by
  intro z hz
  -- For `0 < ρ ≤ 1` the map `k ↦ ρ ^ k` is antitone, so it suffices to compare exponents:
  -- the four admissible values of `z` all satisfy `N - |n₀| ≤ |z - n₀|`.
  refine pow_le_pow_of_le_one hρ0.le hρ1 ?_
  rcases hz with h | h | h | h <;> (rw [h]; omega)

end Work.TMC16Core.Op
