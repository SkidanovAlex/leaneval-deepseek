import Mathlib
import Submission.Work.ChenPlan.H2.Level
import Submission.Work.ChenPlan.H2.WindowCells
import Submission.Work.ChenPlan.H2.utab_table_sum_le
import Submission.Work.ChenPlan.H2.log_cellEndpoints_le_model
import Submission.Work.ChenPlan.H2.cellF_mass_le_endpoints
import Submission.Work.Sieve.RosserLinear.primeRecipsLocalUpper

namespace Work.ChenPlan.H2

open Finset Filter
open scoped BigOperators

noncomputable section

/-- `max 0 (a + c) = max 0 a + c` for `c ≥ 0` (the `max 0` of a shifted argument). -/
private lemma max_zero_add_le (a c : ℝ) (hc : 0 ≤ c) : max 0 (a + c) ≤ max 0 a + c :=
  max_le (add_nonneg (le_max_left (0 : ℝ) a) hc) (by linarith [le_max_right (0 : ℝ) a])

/-- The window main term of Chen's `h2`.

Route.  Split the window primes `q ∈ winPrimes M Y` (`M = siftM x`, `Y = winY x`) by the cell
index `k q = min (⌊(sVal B x q - 3/2) * 20⌋₊) 70`, so that `Utab (sVal B x q) = utabQ (k q)`.
For `q` in cell `k` one has `sVal B x q ∈ [3/2 + k/20, 3/2 + (k+1)/20)`, i.e.
`q ∈ (L_{k+1}, L_k]` where `L_j = lvlD B x * (siftM x)^(-(3/2 + j/20))`; hence the cell is
contained in the integer interval with lower end `max M (⌊L_{k+1}⌋₊+1)` and upper end
`min (Y-1) ⌊L_k⌋₊`.  The mass of that cell is bounded by

`log (log (min Y ⌊L_k⌋₊+1) / log (max M ⌊L_{k+1}⌋₊+1)) + err`,

via `Work.Sieve.RosserLinear.primeRecipsLocalUpper`.  Comparing the resulting sum with the model
value at `σ = 5`, `w = 10/3` (using `5 - 1/100000 ≤ sigM B x` and `wVal x ≤ 10/3 + 1/100000`,
both eventual: `eventually_sigM_ge` and `eventually_wVal_le` from
`Work.ChenPlan.H2.Level`) and concluding with `Work.ChenPlan.H2.utab_table_sum_le` gives the
claim. -/
theorem window_Ut_sum_le (B : ℝ) (hB : 0 < B) :
    ∀ᶠ x : ℕ in Filter.atTop,
      (∑ q ∈ Submission.winPrimes (Work.ChenPlan.H2.siftM x) (Work.ChenPlan.H2.winY x),
          Submission.ChenPlan.Utab (Work.ChenPlan.H2.sVal B x q) / ((q : ℝ) - 1))
        ≤ 39 / 25 - 1 / 1000 := by
  filter_upwards [log_cellEndpoints_le_model B hB, cellF_mass_le_endpoints B hB,
    eventually_sigM_ge B hB (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num) (by norm_num),
    eventually_wVal_le (show (0 : ℝ) < 1 / 10 ^ 8 by norm_num),
    Filter.eventually_ge_atTop 8] with x hAx hA2x hσge hwle hx8
  have hx1 : 1 ≤ x := by omega
  have hσle : sigM B x ≤ 5 := sigM_le_five B hB hx8
  have hlvl : 0 < lvlD B x := lvlD_pos hB (by omega)
  have hM : 1 < (siftM x : ℝ) := one_lt_siftM hx1
  have hY1 : 0 < winY x - 1 := winY_sub_one_pos hx1
  -- every window prime has `sVal ≥ 3/2`
  have h32 : ∀ q ∈ Submission.winPrimes (siftM x) (winY x), 3 / 2 ≤ sVal B x q := by
    intro q hq
    obtain ⟨hqp, hq3, hqM, hqY⟩ := Submission.mem_winPrimes.mp hq
    have hqpos : 0 < q := by omega
    have h1 := sVal_ge_sigM_sub_wVal (B := B) hqpos (by omega : q ≤ winY x - 1) hM hlvl hY1
    have h2 : (3 : ℝ) / 2 ≤ sigM B x - wVal x := by linarith
    linarith
  rw [sum_winPrimes_eq_sum_cellF B x
    (fun q => Submission.ChenPlan.Utab (sVal B x q) / ((q : ℝ) - 1))]
  have hstep : (∑ k ∈ Finset.range 71, ∑ q ∈ cellF B x k,
        Submission.ChenPlan.Utab (sVal B x q) / ((q : ℝ) - 1))
      ≤ ∑ k ∈ Finset.range 71, (utabQ k : ℝ)
          * (max 0 (Real.log (mnum k / mden k)) + 2 * ((1 : ℝ) / 10000000)) := by
    refine Finset.sum_le_sum (fun k hk => ?_)
    have hk70 : k ≤ 70 := by have := Finset.mem_range.mp hk; omega
    have hinner : (∑ q ∈ cellF B x k, Submission.ChenPlan.Utab (sVal B x q) / ((q : ℝ) - 1))
        = (utabQ k : ℝ) * (∑ q ∈ cellF B x k, 1 / ((q : ℝ) - 1)) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl (fun q hq => ?_)
      obtain ⟨hwq, hkq⟩ := mem_cellF.mp hq
      rw [Utab_sVal_eq_utabQ B x q (h32 q hwq), hkq]
      ring
    rw [hinner]
    have hmass := hA2x k hk70
    have hend := hAx k hk70
    have hmass' : (∑ q ∈ cellF B x k, 1 / ((q : ℝ) - 1))
        ≤ max 0 (Real.log (mnum k / mden k)) + 2 * ((1 : ℝ) / 10000000) := by
      have h1 : max 0 (Real.log (Real.log (((cellHi B x k) + 1 : ℕ) : ℝ)
            / Real.log ((cellLo B x k : ℕ) : ℝ)))
          ≤ max 0 (Real.log (mnum k / mden k)) + ((1 : ℝ) / 10000000) := by
        have hle : max 0 (Real.log (Real.log (((cellHi B x k) + 1 : ℕ) : ℝ)
              / Real.log ((cellLo B x k : ℕ) : ℝ)))
            ≤ max 0 (max 0 (Real.log (mnum k / mden k)) + ((1 : ℝ) / 10000000)) :=
          max_le_max (le_refl (0 : ℝ)) hend
        have h2 := max_zero_add_le (max 0 (Real.log (mnum k / mden k))) ((1 : ℝ) / 10000000)
          (by norm_num)
        rw [max_eq_right (le_max_left (0 : ℝ) (Real.log (mnum k / mden k)))] at h2
        linarith
      linarith
    exact mul_le_mul_of_nonneg_left hmass' (utabQ_nonneg k)
  have hfin : (∑ k ∈ Finset.range 71, (utabQ k : ℝ)
        * (max 0 (Real.log (mnum k / mden k)) + 2 * ((1 : ℝ) / 10000000)))
      ≤ 39 / 25 - 1 / 1000 := by
    have hexp : (∑ k ∈ Finset.range 71, (utabQ k : ℝ)
          * (max 0 (Real.log (mnum k / mden k)) + 2 * ((1 : ℝ) / 10000000)))
        = (∑ k ∈ Finset.range 71, (utabQ k : ℝ) * max 0 (Real.log (mnum k / mden k)))
          + (∑ k ∈ Finset.range 71, (utabQ k : ℝ)) * (2 * ((1 : ℝ) / 10000000)) := by
      calc (∑ k ∈ Finset.range 71, (utabQ k : ℝ)
            * (max 0 (Real.log (mnum k / mden k)) + 2 * ((1 : ℝ) / 10000000)))
          = ∑ k ∈ Finset.range 71, ((utabQ k : ℝ) * max 0 (Real.log (mnum k / mden k))
              + (utabQ k : ℝ) * (2 * ((1 : ℝ) / 10000000))) :=
            Finset.sum_congr rfl (fun k _ => by ring)
        _ = (∑ k ∈ Finset.range 71, (utabQ k : ℝ) * max 0 (Real.log (mnum k / mden k)))
              + ∑ k ∈ Finset.range 71, (utabQ k : ℝ) * (2 * ((1 : ℝ) / 10000000)) :=
            Finset.sum_add_distrib
        _ = (∑ k ∈ Finset.range 71, (utabQ k : ℝ) * max 0 (Real.log (mnum k / mden k)))
              + (∑ k ∈ Finset.range 71, (utabQ k : ℝ)) * (2 * ((1 : ℝ) / 10000000)) := by
            rw [Finset.sum_mul]
    rw [hexp]
    have htab : (∑ k ∈ Finset.range 71, (utabQ k : ℝ) * max 0 (Real.log (mnum k / mden k)))
        ≤ 1.551 := by
      simpa [mnum, mden] using utab_table_sum_le
    have h2 : (∑ k ∈ Finset.range 71, (utabQ k : ℝ)) * (2 * ((1 : ℝ) / 10000000))
        ≤ 100 * (2 * ((1 : ℝ) / 10000000)) :=
      mul_le_mul_of_nonneg_right sum_utabQ_le (by norm_num)
    linarith
  exact le_trans hstep hfin

end

end Work.ChenPlan.H2
