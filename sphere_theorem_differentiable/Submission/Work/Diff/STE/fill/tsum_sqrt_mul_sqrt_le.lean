import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.fill

theorem tsum_sqrt_mul_sqrt_le {α : Type*} {A B : α → ℝ}
    (hA : Summable A) (hB : Summable B) (hA0 : ∀ a, 0 ≤ A a) (hB0 : ∀ a, 0 ≤ B a) :
    (∑' a, Real.sqrt (A a) * Real.sqrt (B a)) ≤
      Real.sqrt (∑' a, A a) * Real.sqrt (∑' a, B a) := by
  -- Cauchy–Schwarz on every finite subset, then pass to the supremum of partial sums.
  have hf : ∀ a, 0 ≤ Real.sqrt (A a) * Real.sqrt (B a) :=
    fun a => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  refine Real.tsum_le_of_sum_le hf fun s => ?_
  calc ∑ a ∈ s, Real.sqrt (A a) * Real.sqrt (B a)
      ≤ Real.sqrt (∑ a ∈ s, A a) * Real.sqrt (∑ a ∈ s, B a) :=
        Real.sum_sqrt_mul_sqrt_le s hA0 hB0
    _ ≤ Real.sqrt (∑' a, A a) * Real.sqrt (∑' a, B a) := by
        refine mul_le_mul (Real.sqrt_le_sqrt (hA.sum_le_tsum s (fun i _ => hA0 i)))
          (Real.sqrt_le_sqrt (hB.sum_le_tsum s (fun i _ => hB0 i)))
          (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

end Work.Diff.STE.fill
