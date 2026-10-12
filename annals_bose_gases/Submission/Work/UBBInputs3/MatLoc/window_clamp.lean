import Mathlib.Data.Complex.Basic
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Submission.Work.UBBInputs3.MatLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

namespace Work.UBBInputs3.MatLoc

open Finset

/-- **Window clamping.**  If `φ : ℤ → ℂ` is supported in `iRange n = [0,n-1]` and in the
interval `[m-p, m+p]` of `2p+1 ≤ M` consecutive integers, then its support is contained in
some window `[n₀, n₀+M)` of `M` consecutive integers that itself lies in `[0,n]`.

We take `n₀ = max 0 (min (n-1) (m+p) - M + 1)`, i.e. the window placed as far to the right
as possible: it starts no later than `max 0 (m-p)`, ends strictly after `min (n-1) (m+p)`,
and is clamped to fit inside `[0,n]`. -/
theorem window_clamp (n M : ℕ) (hM : 1 ≤ M) (hMn : M ≤ n) (φ : ℤ → ℂ) (m : ℤ) (p : ℕ)
    (hp : 2 * p + 1 ≤ M)
    (hsupp : ∀ j, φ j ≠ 0 → j ∈ Work.UBBInputs3.iRange n)
    (hwin : ∀ j, φ j ≠ 0 → m - (p : ℤ) ≤ j ∧ j ≤ m + (p : ℤ)) :
    ∃ n₀ : ℤ, 0 ≤ n₀ ∧ n₀ + (M : ℤ) ≤ (n : ℤ) ∧
      ∀ j, φ j ≠ 0 → n₀ ≤ j ∧ j < n₀ + (M : ℤ) := by
  have hpc : (2 : ℤ) * (p : ℤ) + 1 ≤ (M : ℤ) := by exact_mod_cast hp
  have hMnZ : (M : ℤ) ≤ (n : ℤ) := by exact_mod_cast hMn
  refine ⟨max 0 (min ((n : ℤ) - 1) (m + (p : ℤ)) - (M : ℤ) + 1), le_max_left _ _, ?_, ?_⟩
  · -- `n₀ + M ≤ n`
    have h1 : min ((n : ℤ) - 1) (m + (p : ℤ)) - (M : ℤ) + 1 ≤ (n : ℤ) - (M : ℤ) := by
      have := min_le_left ((n : ℤ) - 1) (m + (p : ℤ))
      omega
    have h2 : (0 : ℤ) ≤ (n : ℤ) - (M : ℤ) := by omega
    have h3 : max 0 (min ((n : ℤ) - 1) (m + (p : ℤ)) - (M : ℤ) + 1) ≤ (n : ℤ) - (M : ℤ) :=
      max_le h2 h1
    omega
  · intro j hj
    have hjr := hsupp j hj
    rw [Work.UBBInputs3.iRange, Finset.mem_Icc] at hjr
    obtain ⟨hj0, hjn⟩ := hjr
    obtain ⟨hjm1, hjm2⟩ := hwin j hj
    constructor
    · -- `n₀ ≤ j`: the window starts no later than `max 0 (m-p) ≤ j`
      have h1 : min ((n : ℤ) - 1) (m + (p : ℤ)) ≤ m + (p : ℤ) := min_le_right _ _
      have h2 : m + (p : ℤ) - (M : ℤ) + 1 ≤ j := by omega
      have h3 : min ((n : ℤ) - 1) (m + (p : ℤ)) - (M : ℤ) + 1 ≤ j := by omega
      exact max_le hj0 h3
    · -- `j < n₀ + M`: the window ends strictly after `min (n-1) (m+p) ≥ j`
      have hv : j ≤ min ((n : ℤ) - 1) (m + (p : ℤ)) := le_min hjn hjm2
      have h3 : min ((n : ℤ) - 1) (m + (p : ℤ)) - (M : ℤ) + 1
          ≤ max 0 (min ((n : ℤ) - 1) (m + (p : ℤ)) - (M : ℤ) + 1) := le_max_right _ _
      omega

end Work.UBBInputs3.MatLoc
