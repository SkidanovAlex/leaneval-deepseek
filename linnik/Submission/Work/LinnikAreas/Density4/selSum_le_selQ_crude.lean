import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.natDiv_cast_mul_le
import Submission.Work.LinnikAreas.Density4.sum_abs_selLam_le

namespace Work.LinnikAreas.Density4

open scoped BigOperators
open Finset

noncomputable section

/-! ## The crude floor comparison for the truncated Selberg weight

We evaluate `∑_{n ≤ N} Λ_z(n)²` with `Λ_z(n) = ∑_{d ∣ n, d ≤ z} λ_d`,
`λ_d = selLam z d = μ(d)·log(z/d)`.  The swap identity
`Commons.NumberTheory.Moebius.sum_sq_truncated_eq_lcm_sum_general` turns the square into the
double sum `∑_{d,e ≤ z} λ_d λ_e ⌊N/[d,e]⌋`; replacing each floor by the real quotient costs
`|λ_d λ_e|` (`natDiv_cast_mul_le`); factoring `N` recognises the Selberg form `selQ z`, and the
bound `∑_{d ≤ z} |λ_d| ≤ z` (`sum_abs_selLam_le`) closes the estimate. -/

/-- **The LCM double sum bound.**  The double sum `∑_{d,e ≤ z} λ_d λ_e ⌊N/[d,e]⌋` obtained from
the swap identity is at most `N · selQ z + (∑_{d ≤ z} |λ_d|)²`.  Each `⌊N/[d,e]⌋` is replaced by
`N/[d,e]` at the cost of `|λ_d λ_e|`, the resulting first sum is `N · selQ z`, and the correction
sum is `(∑_{d ≤ z} |λ_d|)²`. -/
theorem selSum_lcm_double_le (z N : ℕ) :
    (∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
        selLam z d * selLam z e * ((N / Nat.lcm d e : ℕ) : ℝ))
      ≤ (N : ℝ) * selQ z + (∑ d ∈ Finset.Icc 1 z, |selLam z d|) ^ 2 := by
  calc
    (∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
        selLam z d * selLam z e * ((N / Nat.lcm d e : ℕ) : ℝ))
        ≤ ∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
            (selLam z d * selLam z e * ((N : ℝ) / (Nat.lcm d e : ℝ))
              + |selLam z d * selLam z e|) := by
          apply Finset.sum_le_sum; intro d _
          apply Finset.sum_le_sum; intro e _
          exact natDiv_cast_mul_le N (Nat.lcm d e) (selLam z d * selLam z e)
      _ = (∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
              selLam z d * selLam z e * ((N : ℝ) / (Nat.lcm d e : ℝ)))
            + (∑ d ∈ Finset.Icc 1 z, ∑ e ∈ Finset.Icc 1 z,
                |selLam z d * selLam z e|) := by
          rw [← Finset.sum_add_distrib]
          apply Finset.sum_congr rfl; intro d _
          rw [← Finset.sum_add_distrib]
      _ = (N : ℝ) * selQ z + (∑ d ∈ Finset.Icc 1 z, |selLam z d|) ^ 2 := by
          congr 1
          · rw [selQ, Finset.mul_sum]
            apply Finset.sum_congr rfl; intro d _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro e _
            ring
          · rw [pow_two, Finset.sum_mul]
            apply Finset.sum_congr rfl; intro d _
            rw [Finset.mul_sum]
            apply Finset.sum_congr rfl; intro e _
            rw [abs_mul]

/-- **Crude floor comparison underlying the case `z² ≤ N`.**  Expanding the square of the
truncated Selberg weight as `∑_{d,e ≤ z} λ_d λ_e ⌊N/[d,e]⌋` (available as
`Commons.NumberTheory.Moebius.log_moebius_lcm_sq_swap`) and replacing `⌊x⌋` by `x` at the cost
of `|λ_d λ_e|` at each term gives `∑_{n ≤ N} Λ_z(n)² ≤ N · selQ z + (∑_{d ≤ z} |λ_d|)²`, and
the second sum is `≤ z` (via `log z! ≥ z log z - z + 1`). -/
theorem selSum_le_selQ_crude (z N : ℕ) (hz : 1 ≤ z) :
    (∑ n ∈ Finset.Icc 1 N, (∑ d ∈ n.divisors.filter (fun d => d ≤ z), selLam z d) ^ 2)
      ≤ (N : ℝ) * selQ z + (z : ℝ) * (z : ℝ) := by
  rw [Commons.NumberTheory.Moebius.sum_sq_truncated_eq_lcm_sum_general N z (selLam z)]
  refine (selSum_lcm_double_le z N).trans ?_
  have hS : (∑ d ∈ Finset.Icc 1 z, |selLam z d|) ≤ (z : ℝ) := sum_abs_selLam_le z hz
  have hSnn : 0 ≤ ∑ d ∈ Finset.Icc 1 z, |selLam z d| :=
    Finset.sum_nonneg (fun d _ => abs_nonneg _)
  have hsq : (∑ d ∈ Finset.Icc 1 z, |selLam z d|) ^ 2 ≤ (z : ℝ) * (z : ℝ) := by
    have h := pow_le_pow_left₀ hSnn hS 2
    simpa only [pow_two] using h
  linarith

end

end Work.LinnikAreas.Density4