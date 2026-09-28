import Mathlib
import Submission.Work.HP.MDEstimates.pSeries_tail_tsum_le

namespace Work.HP.HP2

open MeasureTheory Set

/-- For `s > 1` and `N ≥ 1`, the partial sum `∑_{N ≤ k < M} k^{-s}` is bounded by
`N^{-s} + N^{1-s}/(s-1)`: the term `k = N` is isolated (its `N^{-s}` is the extra
summand on the right) and the remaining sum is compared with the integral of the
antitone function `x ↦ x^{-s}` from `N` to `∞`. -/
theorem sum_Ico_rpow_neg_le (s : ℝ) (hs : 1 < s) (N M : ℕ) (hN : 1 ≤ N) :
    (∑ k ∈ Finset.Ico N M, (k : ℝ) ^ (-s))
      ≤ (N : ℝ) ^ (-s) + (N : ℝ) ^ (1 - s) / (s - 1) := by
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast hN
  -- `x ↦ x^{-s}` is antitone on `[N, M-1]`
  have hanti_all : AntitoneOn (fun x : ℝ => x ^ (-s)) (Ioi 0) :=
    Real.antitoneOn_rpow_Ioi_of_exponent_nonpos (by linarith)
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Icc (N : ℝ) ((M - 1 : ℕ) : ℝ)) :=
    hanti_all.mono (by intro x hx; exact lt_of_lt_of_le hNpos hx.1)
  -- it is integrable and nonnegative on `(N, ∞)`
  have hint : IntegrableOn (fun x : ℝ => x ^ (-s)) (Ioi (N : ℝ)) :=
    integrableOn_Ioi_rpow_of_lt (by linarith) hNpos
  have hnonneg : ∀ t ∈ Ioi (N : ℝ), 0 ≤ t ^ (-s) := by
    intro t ht
    exact Real.rpow_nonneg (le_of_lt (lt_trans hNpos ht)) _
  -- evaluation of the improper integral
  have hInt : (∫ x in Ioi (N : ℝ), x ^ (-s)) = (N : ℝ) ^ (1 - s) / (s - 1) := by
    rw [integral_Ioi_rpow_of_lt (a := -s) (c := (N : ℝ)) (by linarith) hNpos]
    rw [show (-s + 1 : ℝ) = 1 - s by ring, show (1 : ℝ) - s = -(s - 1) by ring]
    rw [neg_div_neg_eq]
  by_cases hMN : M ≤ N
  · -- empty range
    rw [Finset.Ico_eq_empty_of_le hMN, Finset.sum_empty]
    have h1 : (0 : ℝ) ≤ (N : ℝ) ^ (-s) := Real.rpow_nonneg (le_of_lt hNpos) _
    have h2 : (0 : ℝ) ≤ (N : ℝ) ^ (1 - s) / (s - 1) :=
      div_nonneg (Real.rpow_nonneg (le_of_lt hNpos) _) (by linarith)
    linarith
  · have hNM : N < M := not_le.mp hMN -- isolate the `k = N` term
    have hsplit : (∑ k ∈ Finset.Ico N M, (k : ℝ) ^ (-s))
        = (N : ℝ) ^ (-s) + ∑ k ∈ Finset.Ico (N + 1) M, (k : ℝ) ^ (-s) :=
      Finset.sum_eq_sum_Ico_succ_bot hNM (fun k : ℕ => (k : ℝ) ^ (-s))
    -- reindex `∑_{k=N+1}^{M-1}` as `∑_{n=N}^{M-2} (n+1)^{-s}`
    have hM1 : M - 1 + 1 = M := Nat.sub_add_cancel (by omega)
    have hreindex : (∑ n ∈ Finset.Ico N (M - 1), ((n + 1 : ℕ) : ℝ) ^ (-s))
        = ∑ k ∈ Finset.Ico (N + 1) M, (k : ℝ) ^ (-s) := by
      have h := Finset.sum_Ico_add' (fun k : ℕ => (k : ℝ) ^ (-s)) N (M - 1) 1
      rw [hM1] at h
      exact h
    -- integral comparison for the tail sum
    have hbound : (∑ k ∈ Finset.Ico (N + 1) M, (k : ℝ) ^ (-s))
        ≤ ∫ x in Ioi (N : ℝ), x ^ (-s) := by
      rw [← hreindex]
      exact hanti.sum_Ico_le_integral hint hnonneg
    rw [hsplit]
    calc (N : ℝ) ^ (-s) + ∑ k ∈ Finset.Ico (N + 1) M, (k : ℝ) ^ (-s)
        ≤ (N : ℝ) ^ (-s) + ∫ x in Ioi (N : ℝ), x ^ (-s) := by linarith
      _ = (N : ℝ) ^ (-s) + (N : ℝ) ^ (1 - s) / (s - 1) := by rw [hInt]

end Work.HP.HP2
