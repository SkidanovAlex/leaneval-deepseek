import Mathlib
import Submission.Work.LinnikAreas.Density4.sum_Icc_div_reindex

namespace Work.LinnikAreas.Density4

/-- Double-counting identity for the `τ`-weighted `3/2`-power sum.  Writing `G n = (n:ℝ)^(-(3/2))`, the left side groups the pairs `(a,b)` with `a*b = e` by `e` (giving `τ(e)·G e`), while the right side enumerates the region `{(a,b) : a ≥ 1, b ≥ 1, a*b ≤ N}` as `a` first and `b ≤ N/a`.  The sides are equal because for `e ∈ [1,N]` the map `d ↦ (d, e/d)` is a bijection `e.divisors ≃ {(a,b) ∈ [1,N]² : a*b = e}` (both coordinates are `≤ e ≤ N`), and for `a ≥ 1` one has `a*b ≤ N ↔ b ≤ N/a`.

Proof sketch (all inside `Finset`): let `C := (Finset.Icc 1 N) ×ˢ (Finset.Icc 1 N)`.  For `e ∈ Icc 1 N`, `C.filter (fun p => p.1*p.2 = e) = e.divisorsAntidiagonal` (use `Nat.mem_divisorsAntidiagonal`), so by `Finset.sum_boole` and `Nat.map_div_right_divisors` (`e.divisorsAntidiagonal.card = e.divisors.card`), `(e.divisors.card : ℝ) = ∑ p ∈ C, if p.1*p.2 = e then (1:ℝ) else 0`.  Then multiply by `e^(-3/2)`, use `Finset.sum_mul`, `Finset.sum_comm`, and `Finset.sum_ite_eq` to evaluate the inner sum `∑ e ∈ Icc 1 N, (if p.1*p.2 = e then G e else 0) = if p.1*p.2 ∈ Icc 1 N then G (p.1*p.2) else 0`.  Finally `Finset.sum_filter` + `Finset.sum_product` turn this into the double sum over `a`, and the inner `b`-summand's filter `{b ∈ Icc 1 N | a*b ≤ N}` equals `Icc 1 (N/a)` for `a ≥ 1` via `Nat.le_div_iff_mul_le`. -/
theorem tau_divisor_sum_eq_hyperbola (N : ℕ) :
    (∑ e ∈ Finset.Icc 1 N, (e.divisors.card : ℝ) * (e : ℝ) ^ (-(3 / 2 : ℝ)))
      = ∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), ((a * b : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
  -- Rewrite the RHS double sum so that the outer index set carries a `filter … True`,
  -- matching the shape of `sum_Icc_div_reindex`.
  rw [show (∑ a ∈ Finset.Icc 1 N, ∑ b ∈ Finset.Icc 1 (N / a), ((a * b : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))
        = ∑ a ∈ (Finset.Icc 1 N).filter (fun _ => True),
            ∑ b ∈ Finset.Icc 1 (N / a), ((a * b : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) from by
        rw [Finset.filter_true]]
  -- Reindex `(a,b) ↦ (n = a*b, a)`: the region `{(a,b) : a ≥ 1, b ≥ 1, a*b ≤ N}`.
  rw [sum_Icc_div_reindex N (fun _ => True) (fun a b => ((a * b : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)))]
  simp only [Finset.filter_true]
  -- Per `n ∈ Icc 1 N`, the inner divisor sum is the constant `G n` repeated `τ(n)` times.
  refine Finset.sum_congr rfl (fun n _ => ?_)
  have hterm : ∀ d ∈ n.divisors,
      ((d * (n / d) : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) = (n : ℝ) ^ (-(3 / 2 : ℝ)) := by
    intro d hd
    rw [Nat.mem_divisors] at hd
    rw [Nat.mul_div_cancel' hd.1]
  rw [Finset.sum_congr rfl hterm, Finset.sum_const, nsmul_eq_mul]

end Work.LinnikAreas.Density4
