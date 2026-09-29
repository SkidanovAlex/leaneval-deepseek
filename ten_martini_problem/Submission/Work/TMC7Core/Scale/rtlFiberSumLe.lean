import Mathlib

namespace Work.TMC7Core.Scale

theorem rtlFiberSumLe (k S Sb : ℕ) (g : ℕ → ℕ) (W U : ℕ → ℝ)
    (hmap : ∀ t < S, g t < k)
    (hcard : ∀ i < k, ((Finset.range S).filter (fun t => g t = i)).card ≤ Sb)
    (hWnn : ∀ i < k, 0 ≤ W i) (hW : ∀ i < k, W i ≤ U i) :
    (∑ t ∈ Finset.range S, W (g t)) ≤ (Sb : ℝ) * ∑ i ∈ Finset.range k, U i := by
  -- Rewrite each value `W (g t)` as the indicator sum over the range `k`.
  have hA : (∑ t ∈ Finset.range S, W (g t))
      = ∑ t ∈ Finset.range S, ∑ i ∈ Finset.range k, (if g t = i then W i else 0) := by
    apply Finset.sum_congr rfl
    intro t ht
    rw [Finset.sum_ite_eq]
    rw [if_pos]
    exact Finset.mem_range.mpr (hmap t (Finset.mem_range.mp ht))
  -- Swap the order of summation.
  have hB : (∑ t ∈ Finset.range S, ∑ i ∈ Finset.range k, (if g t = i then W i else 0))
      = ∑ i ∈ Finset.range k, ∑ t ∈ Finset.range S, (if g t = i then W i else 0) :=
    Finset.sum_comm
  -- Bound each fiber block.
  have hC : ∀ i ∈ Finset.range k,
      (∑ t ∈ Finset.range S, (if g t = i then W i else 0)) ≤ (Sb : ℝ) * U i := by
    intro i hi
    have hik : i < k := Finset.mem_range.mp hi
    have hcardi : (((Finset.range S).filter (fun t => g t = i)).card : ℝ) ≤ (Sb : ℝ) := by
      exact_mod_cast hcard i hik
    have hUi : 0 ≤ U i := le_trans (hWnn i hik) (hW i hik)
    have hsumeq : (∑ t ∈ Finset.range S, (if g t = i then W i else 0))
        = (((Finset.range S).filter (fun t => g t = i)).card : ℝ) * W i := by
      rw [← Finset.sum_filter]
      rw [Finset.sum_const, nsmul_eq_mul]
    calc (∑ t ∈ Finset.range S, (if g t = i then W i else 0))
        = (((Finset.range S).filter (fun t => g t = i)).card : ℝ) * W i := hsumeq
      _ ≤ (((Finset.range S).filter (fun t => g t = i)).card : ℝ) * U i :=
          mul_le_mul_of_nonneg_left (hW i hik) (Nat.cast_nonneg _)
      _ ≤ (Sb : ℝ) * U i := mul_le_mul_of_nonneg_right hcardi hUi
  calc (∑ t ∈ Finset.range S, W (g t))
      = ∑ t ∈ Finset.range S, ∑ i ∈ Finset.range k, (if g t = i then W i else 0) := hA
    _ = ∑ i ∈ Finset.range k, ∑ t ∈ Finset.range S, (if g t = i then W i else 0) := hB
    _ ≤ ∑ i ∈ Finset.range k, Sb * U i := Finset.sum_le_sum hC
    _ = (Sb : ℝ) * ∑ i ∈ Finset.range k, U i := by rw [Finset.mul_sum]

end Work.TMC7Core.Scale
