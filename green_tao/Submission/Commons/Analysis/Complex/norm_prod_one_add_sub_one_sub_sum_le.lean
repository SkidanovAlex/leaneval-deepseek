import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.CStarAlgebra.Classes

namespace Commons.Analysis.Complex

/-- For complex numbers `u i` over a finite set `s` with `∑ i ∈ s, ‖u i‖ ≤ 1`, the product
`∏ i ∈ s, (1 + u i)` deviates from `1 + ∑ i ∈ s, u i` only at second order:
`‖∏ i ∈ s, (1 + u i) - 1 - ∑ i ∈ s, u i‖ ≤ 2 * (∑ i ∈ s, ‖u i‖) ^ 2`.

Proof sketch: expand the product over subsets, so the difference is `∑_{T ⊆ s, 2 ≤ #T} ∏_{i∈T} u i`;
bound the norm by `∑_{T, 2 ≤ #T} ∏_{i∈T}‖u i‖`.  This is exactly
`∏ i ∈ s, (1 + ‖u i‖) - 1 - ∑ i ∈ s, ‖u i‖`; bound the latter by comparing with the exponential:
for `x_i ≥ 0` with `S := ∑ x_i ≤ 1`, `∏(1+x_i) ≤ exp S` and `exp S - 1 - S ≤ S^2` (e.g. via
`Real.exp_bound`/`Real.exp_le_one_iff` or the series bound `exp S - 1 - S = ∑_{k≥2} S^k/k! ≤
S^2 ∑_{k≥2} S^{k-2}/k! ≤ S^2 (e - 2)`), and `e - 2 < 2`. -/
theorem norm_prod_one_add_sub_one_sub_sum_le {ι : Type*} (s : Finset ι) (u : ι → ℂ)
    (h : ∑ i ∈ s, ‖u i‖ ≤ 1) :
    ‖∏ i ∈ s, (1 + u i) - 1 - ∑ i ∈ s, u i‖ ≤ 2 * (∑ i ∈ s, ‖u i‖) ^ 2 := by
  classical
  revert h
  refine Finset.induction_on s ?base ?step
  · intro _
    simp
  · intro a s ha ih h
    have hsum_s : ∑ i ∈ s, ‖u i‖ ≤ 1 := by
      rw [Finset.sum_insert ha] at h
      linarith [norm_nonneg (u a)]
    have hbound_s : ‖∏ i ∈ s, (1 + u i) - 1 - ∑ i ∈ s, u i‖ ≤ 2 * (∑ i ∈ s, ‖u i‖) ^ 2 :=
      ih hsum_s
    have hx0 : (0 : ℝ) ≤ ‖u a‖ := norm_nonneg _
    have hT0 : (0 : ℝ) ≤ ∑ i ∈ s, ‖u i‖ := Finset.sum_nonneg (fun i _ => norm_nonneg _)
    have hT1 : ∑ i ∈ s, ‖u i‖ ≤ 1 := hsum_s
    have hnorm1 : ‖(1 : ℂ) + u a‖ ≤ 1 + ‖u a‖ := by
      simpa using norm_add_le (1 : ℂ) (u a)
    have hnormSum : ‖∑ i ∈ s, u i‖ ≤ ∑ i ∈ s, ‖u i‖ := norm_sum_le s u
    have hkey : ∏ i ∈ insert a s, (1 + u i) - 1 - ∑ i ∈ insert a s, u i
        = (1 + u a) * (∏ i ∈ s, (1 + u i) - 1 - ∑ i ∈ s, u i)
            + u a * (∑ i ∈ s, u i) := by
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      ring
    rw [hkey]
    calc
      ‖(1 + u a) * (∏ i ∈ s, (1 + u i) - 1 - ∑ i ∈ s, u i) + u a * (∑ i ∈ s, u i)‖
          ≤ ‖(1 + u a) * (∏ i ∈ s, (1 + u i) - 1 - ∑ i ∈ s, u i)‖
              + ‖u a * (∑ i ∈ s, u i)‖ := norm_add_le _ _
      _ = ‖(1 : ℂ) + u a‖ * ‖∏ i ∈ s, (1 + u i) - 1 - ∑ i ∈ s, u i‖
              + ‖u a‖ * ‖∑ i ∈ s, u i‖ := by rw [norm_mul, norm_mul]
      _ ≤ (1 + ‖u a‖) * (2 * (∑ i ∈ s, ‖u i‖) ^ 2) + ‖u a‖ * (∑ i ∈ s, ‖u i‖) := by
            have h1 : ‖(1 : ℂ) + u a‖ * ‖∏ i ∈ s, (1 + u i) - 1 - ∑ i ∈ s, u i‖
                ≤ (1 + ‖u a‖) * (2 * (∑ i ∈ s, ‖u i‖) ^ 2) :=
              mul_le_mul hnorm1 hbound_s (norm_nonneg _) (by positivity)
            have h2 : ‖u a‖ * ‖∑ i ∈ s, u i‖ ≤ ‖u a‖ * (∑ i ∈ s, ‖u i‖) :=
              mul_le_mul_of_nonneg_left hnormSum hx0
            linarith
      _ ≤ 2 * (∑ i ∈ insert a s, ‖u i‖) ^ 2 := by
            rw [Finset.sum_insert ha]
            have hT2 : (∑ i ∈ s, ‖u i‖) ^ 2 ≤ ∑ i ∈ s, ‖u i‖ := by
              nlinarith [mul_nonneg hT0 (sub_nonneg.mpr hT1)]
            nlinarith [hT0, hx0, hT2, mul_le_mul_of_nonneg_left hT2 hx0]

end Commons.Analysis.Complex