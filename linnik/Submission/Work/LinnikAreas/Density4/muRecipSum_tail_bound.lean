import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Commons.NumberTheory.Moebius.log_weighted_moebius_recip_bound
import Submission.Commons.Analysis.Asymptotics.sum_exp_neg_sqrt_log_div_le

namespace Work.LinnikAreas.Density4

open Finset
open scoped BigOperators

/-- Splitting the exponential decay factor: for `i ≥ N ≥ 1`,
`exp(-(c √log i)) ≤ exp(-(c/2 √log N)) · exp(-(c/2 √log i))`. -/
lemma exp_neg_sqrt_log_tail_split {c : ℝ} (hc : 0 < c) {N i : ℕ} (hN : 1 ≤ N) (hNi : N ≤ i) :
    Real.exp (-(c * Real.sqrt (Real.log (i:ℝ))))
      ≤ Real.exp (-(c / 2 * Real.sqrt (Real.log (N:ℝ)))) *
        Real.exp (-(c / 2 * Real.sqrt (Real.log (i:ℝ)))) := by
  rw [← Real.exp_add]
  refine Real.exp_le_exp.mpr ?_
  have hNpos : (0:ℝ) < (N:ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hlog : Real.log (N:ℝ) ≤ Real.log (i:ℝ) :=
    Real.log_le_log hNpos (by exact_mod_cast hNi)
  have hsqrt : Real.sqrt (Real.log (N:ℝ)) ≤ Real.sqrt (Real.log (i:ℝ)) := Real.sqrt_le_sqrt hlog
  have hkey : c / 2 * Real.sqrt (Real.log (N:ℝ)) ≤ c / 2 * Real.sqrt (Real.log (i:ℝ)) :=
    mul_le_mul_of_nonneg_left hsqrt (by positivity)
  linarith

/-- Tail bound for the Abel sum of `muRecipSum`.
Hints: `Commons.NumberTheory.Moebius.muRecipSum_decay` (fed by
`Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay`) gives constants `0 < c₁`, `0 < K₁` with
`|muRecipSum i| ≤ K₁ * exp(-(c₁ * sqrt (log i)))` for all `i ≥ 1`; and
`Commons.NumberTheory.Moebius.log_succ_sub_log_le_inv` gives `log((i+1)/i) ≤ 1/i`.
The remaining step (a *tail* estimate with decay, not just boundedness) can be got from the
committed bounded-sum lemma `Commons.Analysis.Asymptotics.sum_exp_neg_sqrt_log_div_le` by writing
`exp(-(c₁√log i)) = exp(-((c₁/2)√log i)) * exp(-((c₁/2)√log i)) ≤ exp(-((c₁/2)√log i)) * exp(-((c₁/2)√log N))`
for `i ≥ N`; then take `c := c₁/2`. -/
theorem muRecipSum_tail_bound : ∃ C c : ℝ, 0 < c ∧ 0 < C ∧
    ∀ N M : ℕ, 2 ≤ N → N ≤ M →
      (∑ i ∈ Finset.Ico N M, |Commons.NumberTheory.Moebius.muRecipSum i| *
          Real.log (((i:ℝ) + 1) / (i:ℝ)))
        ≤ C * Real.exp (-(c * Real.sqrt (Real.log (N:ℝ)))) := by
  obtain ⟨c₁, K₁, hc₁pos, hK₁pos, hdec⟩ :=
    Commons.NumberTheory.Moebius.moebius_recip_sum_exp_decay
  have hmu := Commons.NumberTheory.Moebius.muRecipSum_decay hc₁pos hK₁pos hdec
  obtain ⟨K, hKpos, hKbound⟩ :=
    Commons.Analysis.Asymptotics.sum_exp_neg_sqrt_log_div_le (c₁ / 2) (by positivity)
  refine ⟨max K₁ 1 * K, c₁ / 2, by positivity, ?_, ?_⟩
  · exact mul_pos (lt_of_lt_of_le hK₁pos (le_max_left _ _)) hKpos
  · intro N M hN hNM
    have hApos : (0:ℝ) < max K₁ 1 := lt_of_lt_of_le hK₁pos (le_max_left _ _)
    have hAe : ∀ x : ℝ, (0:ℝ) ≤ max K₁ 1 * Real.exp x :=
      fun x => le_of_lt (mul_pos hApos (Real.exp_pos x))
    have hN1 : 1 ≤ N := by omega
    have hsub : Finset.Ico N M ⊆ Finset.Icc 1 M := by
      intro i hi
      rw [Finset.mem_Ico] at hi
      rw [Finset.mem_Icc]
      omega
    have hsum_le :
        (∑ i ∈ Finset.Ico N M,
            Real.exp (-(c₁ / 2 * Real.sqrt (Real.log (i:ℝ)))) / (i:ℝ)) ≤ K := by
      calc (∑ i ∈ Finset.Ico N M,
              Real.exp (-(c₁ / 2 * Real.sqrt (Real.log (i:ℝ)))) / (i:ℝ))
          ≤ ∑ i ∈ Finset.Icc 1 M,
              Real.exp (-(c₁ / 2 * Real.sqrt (Real.log (i:ℝ)))) / (i:ℝ) :=
            Finset.sum_le_sum_of_subset_of_nonneg hsub (fun i _ _ => by positivity)
        _ ≤ K := hKbound M
    calc (∑ i ∈ Finset.Ico N M, |Commons.NumberTheory.Moebius.muRecipSum i| *
            Real.log (((i:ℝ) + 1) / (i:ℝ)))
        ≤ ∑ i ∈ Finset.Ico N M, (max K₁ 1) *
            Real.exp (-(c₁ / 2 * Real.sqrt (Real.log (N:ℝ)))) *
            (Real.exp (-(c₁ / 2 * Real.sqrt (Real.log (i:ℝ)))) / (i:ℝ)) := by
          refine Finset.sum_le_sum fun i hi => ?_
          rw [Finset.mem_Ico] at hi
          obtain ⟨hNi, _⟩ := hi
          have hi1 : 1 ≤ i := by omega
          have himu := hmu i hi1
          have hlog_nonneg : 0 ≤ Real.log (((i:ℝ) + 1) / (i:ℝ)) := by
            refine Real.log_nonneg ?_
            rw [one_le_div (by positivity : (0:ℝ) < (i:ℝ))]
            linarith
          have hlog_le : Real.log (((i:ℝ) + 1) / (i:ℝ)) ≤ 1 / (i:ℝ) := by
            rw [Real.log_div (by positivity) (by positivity)]
            exact Commons.NumberTheory.Moebius.log_succ_sub_log_le_inv hi1
          have hstep1 : |Commons.NumberTheory.Moebius.muRecipSum i| *
                Real.log (((i:ℝ) + 1) / (i:ℝ)) ≤
              (max K₁ 1) * Real.exp (-(c₁ * Real.sqrt (Real.log (i:ℝ)))) *
                (1 / (i:ℝ)) :=
            mul_le_mul himu hlog_le hlog_nonneg
              (hAe (-(c₁ * Real.sqrt (Real.log (i:ℝ)))))
          have hexp := exp_neg_sqrt_log_tail_split hc₁pos (N := N) (i := i) hN1 hNi
          have hstep2 : (max K₁ 1) * Real.exp (-(c₁ * Real.sqrt (Real.log (i:ℝ)))) *
                (1 / (i:ℝ))
              ≤ (max K₁ 1) * Real.exp (-(c₁ / 2 * Real.sqrt (Real.log (N:ℝ)))) *
                (Real.exp (-(c₁ / 2 * Real.sqrt (Real.log (i:ℝ)))) / (i:ℝ)) := by
            calc (max K₁ 1) * Real.exp (-(c₁ * Real.sqrt (Real.log (i:ℝ)))) * (1 / (i:ℝ))
                = (max K₁ 1) *
                    (Real.exp (-(c₁ * Real.sqrt (Real.log (i:ℝ)))) * (1 / (i:ℝ))) := by ring
              _ ≤ (max K₁ 1) *
                    (Real.exp (-(c₁ / 2 * Real.sqrt (Real.log (N:ℝ)))) *
                      Real.exp (-(c₁ / 2 * Real.sqrt (Real.log (i:ℝ)))) * (1 / (i:ℝ))) :=
                  mul_le_mul_of_nonneg_left
                    (mul_le_mul_of_nonneg_right hexp (by positivity)) hApos.le
              _ = (max K₁ 1) * Real.exp (-(c₁ / 2 * Real.sqrt (Real.log (N:ℝ)))) *
                    (Real.exp (-(c₁ / 2 * Real.sqrt (Real.log (i:ℝ)))) / (i:ℝ)) := by ring
          exact hstep1.trans hstep2
      _ = (max K₁ 1) * Real.exp (-(c₁ / 2 * Real.sqrt (Real.log (N:ℝ)))) *
            (∑ i ∈ Finset.Ico N M,
              Real.exp (-(c₁ / 2 * Real.sqrt (Real.log (i:ℝ)))) / (i:ℝ)) := by
          rw [Finset.mul_sum]
      _ ≤ (max K₁ 1) * Real.exp (-(c₁ / 2 * Real.sqrt (Real.log (N:ℝ)))) * K :=
          mul_le_mul_of_nonneg_left hsum_le
            (hAe (-(c₁ / 2 * Real.sqrt (Real.log (N:ℝ)))))
      _ = (max K₁ 1 * K) * Real.exp (-(c₁ / 2 * Real.sqrt (Real.log (N:ℝ)))) := by ring

end Work.LinnikAreas.Density4
