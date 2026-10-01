import Mathlib
import Submission.Work.LinnikAreas.Density4.coprime_indicator_moebius
import Submission.Work.LinnikAreas.Density4.sum_Icc_filter_dvd_reindex
import Submission.Work.LinnikAreas.Density4.sum_moebius_div_eq_coprime_count
import Submission.Work.LinnikAreas.Density4.sum_sq_dvd_filter_coprime_reindex

namespace Work.LinnikAreas.Density4

/-- Count of `n ∈ [1, X]` with `(n, r) = 1` and `d² ∣ n`, as a Möbius sum over the divisors
of `r`. Route:

* rewrite the conjunction indicator `[(n,r)=1 ∧ d²∣n]` as the product of the two indicators and
  apply `sum_sq_dvd_filter_coprime_reindex`, which reindexes the multiples of `d²` and splits off
  the indicator `[d ⊥ r]`;
* the remaining sum is the Möbius count `sum_moebius_div_eq_coprime_count` at `X / d²`;
* finally rewrite the floors `(X/d²)/m₀ = X/(m₀·d²)` by `Nat.div_div_eq_div_mul`. -/
theorem sq_dvd_count_coprime (X d r : ℕ) (hd : 1 ≤ d) (hr : 1 ≤ r) :
    (∑ n ∈ (Finset.Icc 1 X).filter (fun n => Nat.Coprime n r ∧ d ^ 2 ∣ n), (1 : ℝ))
      = if Nat.Coprime d r then
          ∑ m₀ ∈ r.divisors, (ArithmeticFunction.moebius m₀ : ℝ) * ((X / (m₀ * d ^ 2) : ℕ) : ℝ)
        else 0 := by
  classical
  -- Step 1: the conjunction indicator is the product of the two indicators, so the count over
  -- `{d² ∣ n}` with the coprimality indicator equals the count over the conjunction.
  have hstep1 :
      (∑ n ∈ (Finset.Icc 1 X).filter (fun n => Nat.Coprime n r ∧ d ^ 2 ∣ n), (1 : ℝ))
        = ∑ n ∈ (Finset.Icc 1 X).filter (fun n => d ^ 2 ∣ n),
            (if Nat.Coprime n r then (1 : ℝ) else 0) := by
    rw [Finset.sum_filter, Finset.sum_filter]
    refine Finset.sum_congr rfl (fun n _ => ?_)
    by_cases h1 : Nat.Coprime n r <;> by_cases h2 : d ^ 2 ∣ n <;> simp_all
  rw [hstep1]
  -- Step 2: reindex the multiples of `d²`, splitting off `[d ⊥ r]`.
  rw [sum_sq_dvd_filter_coprime_reindex X r d hr hd]
  by_cases hdr : Nat.Coprime d r
  · simp only [if_pos hdr, one_mul]
    -- Step 3: Möbius count of the coprime `k ≤ X / d²`.
    rw [← sum_moebius_div_eq_coprime_count r (X / d ^ 2) hr]
    -- Step 4: floors `(X/d²)/m₀ = X/(m₀·d²)`.
    apply Finset.sum_congr rfl
    intro b _
    have hdiv : (X / d ^ 2) / b = X / (b * d ^ 2) := by
      rw [Nat.div_div_eq_div_mul, mul_comm (d ^ 2) b]
    rw [hdiv]
  · simp only [if_neg hdr, zero_mul]

end Work.LinnikAreas.Density4
