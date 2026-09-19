import Mathlib
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_eq_lim_log_sub_sum_inv
import Submission.Commons.Analysis.SpecialFunctions.Gamma.digamma_logRem_kernel_exp_integrable

noncomputable section

open Filter
open scoped Topology BigOperators

namespace Commons.Analysis.SpecialFunctions.Gamma

/-- Gauss' limit formula, one step shifted: the same identity with `log (n + 2)`
in place of `log (n + 1)` (a subsequence of the commons limit formula). -/
lemma digamma_partialSum_shifted (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun n : ℕ =>
      ((Real.log (((n + 1 : ℕ) : ℝ) + 1) : ℂ) -
        ∑ k ∈ Finset.range (n + 2), ((z + (k : ℂ))⁻¹)))
      atTop (𝓝 (Complex.digamma z)) := by
  exact (digamma_eq_lim_log_sub_sum_inv z hz).comp (tendsto_add_atTop_nat 1)

/-- `log (n + 2) - log (n + 1) → 0` (real version). -/
lemma tendsto_log_succ2_sub_succ1 :
    Tendsto (fun n : ℕ =>
      Real.log (((n + 1 : ℕ) : ℝ) + 1) - Real.log ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) := by
  have h0 : Tendsto (fun n : ℕ =>
      Real.log (((n + 1 : ℕ) : ℝ) + 1) - Real.log ((n + 1 : ℕ) : ℝ)) atTop (𝓝 (0 : ℝ)) := by
    exact (tendsto_log_succ_sub_log.comp (tendsto_add_atTop_nat 1))
  refine h0.congr' ?_
  filter_upwards with n
  have hy : ((n + 1 : ℕ) : ℝ) = (n : ℝ) + 1 := by norm_num
  rw [hy]

theorem digamma_partialSum (z : ℂ) (hz : 0 < z.re) :
    Tendsto (fun n : ℕ =>
      ((Real.log (n + 1 : ℝ) : ℂ)) - ∑ k ∈ Finset.range (n + 2), ((z + (k : ℂ))⁻¹))
      atTop (𝓝 (Complex.digamma z)) := by
  have hA' : Tendsto (fun n : ℕ =>
      ((Real.log (((n + 1 : ℕ) : ℝ) + 1) : ℂ) -
        ∑ k ∈ Finset.range (n + 2), ((z + (k : ℂ))⁻¹)))
      atTop (𝓝 (Complex.digamma z)) := digamma_partialSum_shifted z hz
  have hd_real : Tendsto (fun n : ℕ =>
      Real.log (((n + 1 : ℕ) : ℝ) + 1) - Real.log ((n : ℝ) + 1)) atTop (𝓝 (0 : ℝ)) :=
    tendsto_log_succ2_sub_succ1
  have hD : Tendsto (fun n : ℕ =>
      ((Real.log (((n + 1 : ℕ) : ℝ) + 1) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ)))
      atTop (𝓝 (0 : ℂ)) := by
    have h0c : Tendsto
        (Complex.ofReal ∘ fun n : ℕ =>
          Real.log (((n + 1 : ℕ) : ℝ) + 1) - Real.log ((n : ℝ) + 1))
        atTop (𝓝 (0 : ℂ)) :=
      (Complex.continuous_ofReal.tendsto (0 : ℝ)).comp hd_real
    refine h0c.congr' ?_
    filter_upwards with n
    dsimp
    rw [Complex.ofReal_sub]
  have hR : Tendsto (fun n : ℕ =>
      (((Real.log (((n + 1 : ℕ) : ℝ) + 1) : ℂ) -
        ∑ k ∈ Finset.range (n + 2), ((z + (k : ℂ))⁻¹)) -
        ((Real.log (((n + 1 : ℕ) : ℝ) + 1) : ℂ) - (Real.log ((n : ℝ) + 1) : ℂ))))
      atTop (𝓝 (Complex.digamma z)) := by
    simpa using hA'.sub hD
  refine hR.congr' ?_
  filter_upwards with n
  ring

end Commons.Analysis.SpecialFunctions.Gamma
