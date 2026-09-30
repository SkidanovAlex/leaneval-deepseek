import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

open NumberField

/-- The logarithmic height `logHeight₁ y` dominates the sum of the contributions of all
finite places together with the contributions of all but one infinite place: the omitted
infinite place `v₀` contributes the nonnegative amount `v₀.mult * log⁺ (v₀ y)`.

This is the "monotonicity" half of the place decomposition of `logHeight₁`
(`NumberField.logHeight₁_eq`), as used in estimate (15) of Baker–Wüstholz. -/
theorem est15_mon1 {K : Type*} [Field K] [NumberField K]
    (v₀ : NumberField.InfinitePlace K) [DecidableEq (NumberField.InfinitePlace K)] (y : K) :
    (∑ w ∈ Finset.univ.erase v₀, ((w.mult : ℕ) : ℝ) * Real.posLog (w y))
      + (∑ᶠ w : NumberField.FinitePlace K, Real.posLog (w y))
      ≤ Height.logHeight₁ y := by
  rw [NumberField.logHeight₁_eq]
  have hsub : Finset.univ.erase v₀ ⊆ (Finset.univ : Finset (NumberField.InfinitePlace K)) := by
    intro x _; exact Finset.mem_univ x
  have hnn : ∀ x ∈ (Finset.univ : Finset (NumberField.InfinitePlace K)),
      x ∉ Finset.univ.erase v₀ → 0 ≤ ((x.mult : ℕ) : ℝ) * Real.posLog (x y) := by
    intro x _ hx
    have hx' : x = v₀ := by
      by_contra h
      exact hx (Finset.mem_erase.mpr ⟨h, Finset.mem_univ x⟩)
    subst hx'
    exact mul_nonneg (Nat.cast_nonneg _) Real.posLog_nonneg
  exact add_le_add (Finset.sum_le_sum_of_subset_of_nonneg hsub hnn) le_rfl

end Work.BW
