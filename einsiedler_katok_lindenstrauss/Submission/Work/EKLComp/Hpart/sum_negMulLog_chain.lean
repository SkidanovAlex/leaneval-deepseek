import Mathlib

namespace Work.EKLComp.Hpart

/-- Chain rule for the entropy function `x ↦ -x log x`: the total entropy of the
vector `c` equals the entropy of its total mass `∑ c` plus the mass-weighted
entropy of the normalized vector `c i / ∑ c`. -/
theorem sum_negMulLog_chain {ι : Type} [Fintype ι] (c : ι → ℝ) (hc : ∀ i, 0 ≤ c i) :
    ∑ i, Real.negMulLog (c i) =
      Real.negMulLog (∑ i, c i) + ∑ i, (∑ i, c i) * Real.negMulLog (c i / (∑ i, c i)) := by
  set S := ∑ i, c i with hSdef
  by_cases hS : S = 0
  · -- All entries vanish, and the total mass is `0`; both sides are `0`.
    have hcz : ∀ i, c i = 0 := by
      intro i
      exact (Finset.sum_eq_zero_iff_of_nonneg (s := Finset.univ)
        (fun j _ => hc j)).mp (hSdef ▸ hS) i (Finset.mem_univ i)
    rw [hS, Real.negMulLog_zero]
    simp [hcz]
  · -- Total mass nonzero: pull `c i = S * (c i / S)` out of `negMulLog` per term.
    have hci : ∀ i, S * (c i / S) = c i := fun i => mul_div_cancel₀ (c i) hS
    have hsum : (∑ i, Real.negMulLog (c i)) = ∑ i, Real.negMulLog (S * (c i / S)) := by
      apply Finset.sum_congr rfl
      intro i _
      rw [hci i]
    rw [hsum]
    simp only [Real.negMulLog_mul]
    rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.mul_sum]
    rw [← Finset.sum_div, ← hSdef, div_self hS, one_mul]

end Work.EKLComp.Hpart
