import Mathlib
import Submission.Work.LinnikAreas.Density4.sum_range_inv_sq_le
import Submission.Work.LinnikAreas.Density4.weight_term_le_one
import Submission.Work.LinnikAreas.Density4.weight_tail_le_inv_sq

/-!
# A geometric/log weighted sum is bounded uniformly

The sum `Σ_{m < M} (log (2 + 2^m)) ^ (-A)` is bounded by `12`, uniformly in `M`,
for every `A ≥ 2`.

The argument is a split of the range at `m = 2`:

* each of the first two terms is `≤ 1` (`log (2 + 2^m) ≥ log 3 > 1`, exponent `-A ≤ 0`),
  see `weight_term_le_one`;
* for `m ≥ 2` the term is `≤ 4 / m^2`: here `log (2 + 2^m) ≥ log (2^m) = m log 2 ≥ m/2 > 1`,
  so `(log (2 + 2^m))^(-A) ≤ (log (2 + 2^m))^(-2) ≤ (m/2)^(-2) = 4/m^2`,
  see `weight_tail_le_inv_sq`;
* the shifted tail `Σ_{m ≥ 2} 4/m^2` is `≤ 4 · Σ_{N} 1/(N+2)^2 ≤ 4 · 1` by the telescoping
  bound `sum_range_inv_sq_le`.

Hence the sum is at most `2 + 4 = 6 ≤ 12`.
-/

namespace Work.LinnikAreas.Density4

theorem weight_geom_sum_bound (A : ℝ) (hA : 2 ≤ A) (M : ℕ) :
    (∑ m ∈ Finset.range M, (Real.log (2 + (2 : ℝ) ^ m)) ^ (-A)) ≤ 12 := by
  -- the first two terms are each ≤ 1
  have hterm1 : ∀ m : ℕ, (Real.log (2 + (2 : ℝ) ^ m)) ^ (-A) ≤ 1 :=
    fun m => weight_term_le_one A hA m
  -- every term with m ≥ 2 is ≤ 4/m²
  have hterm2 : ∀ m : ℕ, 2 ≤ m → (Real.log (2 + (2 : ℝ) ^ m)) ^ (-A) ≤ 4 / (m : ℝ) ^ 2 :=
    fun m hm => weight_tail_le_inv_sq A hA m hm
  by_cases hM : M ≤ 2
  · -- at most two terms, each ≤ 1
    calc (∑ m ∈ Finset.range M, (Real.log (2 + (2 : ℝ) ^ m)) ^ (-A))
        ≤ ∑ m ∈ Finset.range M, (1 : ℝ) := Finset.sum_le_sum (fun m _ => hterm1 m)
      _ = (M : ℝ) := by simp
      _ ≤ 12 := by
          have hM' : (M : ℝ) ≤ 2 := by exact_mod_cast hM
          linarith
  · -- split off the first two terms
    have hsplit : M = 2 + (M - 2) := by omega
    rw [hsplit, Finset.sum_range_add]
    have h2 : (∑ x ∈ Finset.range 2, (Real.log (2 + (2 : ℝ) ^ x)) ^ (-A)) ≤ 2 := by
      rw [Finset.sum_range_succ, Finset.sum_range_succ]
      simp only [Finset.sum_range_zero, zero_add]
      have h0 := hterm1 0
      have h1 := hterm1 1
      linarith
    have htail :
        (∑ x ∈ Finset.range (M - 2), (Real.log (2 + (2 : ℝ) ^ (2 + x))) ^ (-A)) ≤ 4 := by
      calc (∑ x ∈ Finset.range (M - 2), (Real.log (2 + (2 : ℝ) ^ (2 + x))) ^ (-A))
          ≤ ∑ x ∈ Finset.range (M - 2), 4 / (((2 + x : ℕ)) : ℝ) ^ 2 :=
            Finset.sum_le_sum (fun x _ => hterm2 (2 + x) (by omega))
        _ = 4 * ∑ x ∈ Finset.range (M - 2), (1 : ℝ) / ((x : ℝ) + 2) ^ 2 := by
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl
            intro x _
            push_cast
            ring
        _ ≤ 4 * 1 := by
            have h := sum_range_inv_sq_le (M - 2)
            linarith
        _ = 4 := by norm_num
    linarith

end Work.LinnikAreas.Density4
