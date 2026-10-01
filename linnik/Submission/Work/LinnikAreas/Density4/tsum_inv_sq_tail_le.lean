import Mathlib
import Submission.Work.LinnikAreas.Density4.SqfreeCoprimeDefs

namespace Work.LinnikAreas.Density4

/-- The tail of the series `∑ 1/n^2` starting at `K+1` is at most `1/K`, for `K ≥ 1`.

The proof compares with the telescoping series `1/(n-1) - 1/n = 1/((n-1)n)`:
for `n ≥ 2` one has `1/n^2 ≤ 1/((n-1)n)`, and `∑_{n=K+1}^∞ (1/(n-1) - 1/n) = 1/K`. -/
theorem tsum_inv_sq_tail_le (K : ℕ) (hK : 1 ≤ K) :
    (∑' i : ℕ, (1 : ℝ) / (((i + (K + 1) : ℕ) : ℝ)) ^ 2) ≤ 1 / (K : ℝ) := by
  -- The telescoping majorant `G i = 1/(i+K) - 1/(i+K+1)`.
  have hG_hasSum :
      HasSum (fun i : ℕ => (1 : ℝ) / (((i + K : ℕ) : ℝ)) - 1 / (((i + K : ℕ) : ℝ) + 1))
        (1 / (K : ℝ)) := by
    refine (hasSum_iff_tendsto_nat_of_nonneg ?_ (1 / (K : ℝ))).2 ?_
    · -- each term of the majorant is nonnegative
      intro i
      apply sub_nonneg.mpr
      apply one_div_le_one_div_of_le
      · have : (0 : ℕ) < i + K := by omega
        exact_mod_cast this
      · linarith
    · -- partial sums telescope to `1/K - 1/(n+K)`
      have htel : ∀ n : ℕ, ∑ i ∈ Finset.range n,
          ((1 : ℝ) / (((i + K : ℕ) : ℝ)) - 1 / (((i + K : ℕ) : ℝ) + 1))
          = 1 / (K : ℝ) - 1 / (((n + K : ℕ) : ℝ)) := by
        intro n
        induction n with
        | zero => simp
        | succ n ih =>
          rw [Finset.sum_range_succ, ih]
          have hcast : (((n + 1) + K : ℕ) : ℝ) = ((n + K : ℕ) : ℝ) + 1 := by
            push_cast; ring
          rw [hcast]
          ring
      have hfun : (fun n : ℕ => ∑ i ∈ Finset.range n,
          ((1 : ℝ) / (((i + K : ℕ) : ℝ)) - 1 / (((i + K : ℕ) : ℝ) + 1)))
          = fun n : ℕ => 1 / (K : ℝ) - 1 / (((n + K : ℕ) : ℝ)) := by
        funext n; exact htel n
      rw [hfun]
      have hlim : Filter.Tendsto (fun n : ℕ => 1 / ((n + K : ℕ) : ℝ)) Filter.atTop (nhds 0) :=
        (tendsto_one_div_atTop_nhds_zero_nat (𝕜 := ℝ)).comp (Filter.tendsto_add_atTop_nat K)
      simpa using (tendsto_const_nhds (x := (1 : ℝ) / (K : ℝ))).sub hlim
  have hG_summable :
      Summable (fun i : ℕ => (1 : ℝ) / (((i + K : ℕ) : ℝ)) - 1 / (((i + K : ℕ) : ℝ) + 1)) :=
    hG_hasSum.summable
  have hG_tsum :
      (∑' i : ℕ, ((1 : ℝ) / (((i + K : ℕ) : ℝ)) - 1 / (((i + K : ℕ) : ℝ) + 1)))
        = 1 / (K : ℝ) :=
    hG_hasSum.tsum_eq
  -- pointwise comparison `1/n^2 ≤ 1/((n-1)n)` for `n = i+K+1 ≥ 2`
  have hpoint : ∀ i : ℕ,
      (1 : ℝ) / ((((i + (K + 1) : ℕ)) : ℝ)) ^ 2
        ≤ (1 : ℝ) / (((i + K : ℕ) : ℝ)) - 1 / (((i + K : ℕ) : ℝ) + 1) := by
    intro i
    have hmpos : (0 : ℝ) < ((i + K : ℕ) : ℝ) := by
      have : (0 : ℕ) < i + K := by omega
      exact_mod_cast this
    have hcast : ((i + (K + 1) : ℕ) : ℝ) = ((i + K : ℕ) : ℝ) + 1 := by
      push_cast; ring
    rw [hcast]
    have hmul : ((i + K : ℕ) : ℝ) * (((i + K : ℕ) : ℝ) + 1) ≤ (((i + K : ℕ) : ℝ) + 1) ^ 2 := by
      nlinarith
    have hpos2 : (0 : ℝ) < ((i + K : ℕ) : ℝ) * (((i + K : ℕ) : ℝ) + 1) := by positivity
    have hstep : (1 : ℝ) / ((((i + K : ℕ) : ℝ) + 1) ^ 2)
        ≤ 1 / (((i + K : ℕ) : ℝ) * (((i + K : ℕ) : ℝ) + 1)) :=
      one_div_le_one_div_of_le hpos2 hmul
    have hsub : (1 : ℝ) / (((i + K : ℕ) : ℝ)) - 1 / (((i + K : ℕ) : ℝ) + 1)
        = 1 / (((i + K : ℕ) : ℝ) * (((i + K : ℕ) : ℝ) + 1)) := by
      field_simp
      ring
    rw [hsub]
    exact hstep
  have hU_summable : Summable (fun i : ℕ => (1 : ℝ) / ((((i + (K + 1) : ℕ)) : ℝ)) ^ 2) :=
    Summable.of_nonneg_of_le (fun i => by positivity) hpoint hG_summable
  calc (∑' i : ℕ, (1 : ℝ) / (((i + (K + 1) : ℕ) : ℝ)) ^ 2)
      ≤ (∑' i : ℕ, ((1 : ℝ) / (((i + K : ℕ) : ℝ)) - 1 / (((i + K : ℕ) : ℝ) + 1))) :=
        Summable.tsum_le_tsum hpoint hU_summable hG_summable
    _ = 1 / (K : ℝ) := hG_tsum

end Work.LinnikAreas.Density4
