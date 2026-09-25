import Mathlib
import Submission.Work.RHContract.Corpus

namespace Work.RHContract.Identity.TailSplit

/-- Auxiliary: the derivative/integral pair for the `t ↦ t · k(t)` piece.  Since
`t * k(t) = t⁻¹ / log t + t⁻¹ / (log t)^2`, its integral over `(2, x]` is
`log (log x) - 1 / log x - (log (log 2) - 1 / log 2)`. -/
private theorem integral_id_mul_kW (x : ℝ) (hx : 2 ≤ x) :
    ∫ t in Set.Ioc (2 : ℝ) x, t * Work.RHContract.kW t
      = Real.log (Real.log x) - 1 / Real.log x
        - (Real.log (Real.log 2) - 1 / Real.log 2) := by
  rw [← intervalIntegral.integral_of_le hx]
  have hlog_cont : ContinuousOn Real.log (Set.Icc (2:ℝ) x) :=
    Real.continuousOn_log.mono (fun t ht => by
      have h0 : (0:ℝ) < t := by linarith [(Set.mem_Icc.mp ht).1]
      simpa using h0.ne')
  have hpoint : Set.EqOn (fun t : ℝ => t * Work.RHContract.kW t)
      (fun t => t⁻¹ / Real.log t + t⁻¹ / (Real.log t)^2) (Set.uIcc (2:ℝ) x) := by
    intro t ht
    rw [Set.uIcc_of_le hx] at ht
    have ht0 : t ≠ 0 := by linarith [(Set.mem_Icc.mp ht).1]
    have hlog : Real.log t ≠ 0 :=
      ne_of_gt (Real.log_pos (by linarith [(Set.mem_Icc.mp ht).1] : (1:ℝ) < t))
    simp only [Work.RHContract.kW]
    field_simp
  rw [intervalIntegral.integral_congr hpoint]
  have hint1 : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t) MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    apply ContinuousOn.div
    · apply ContinuousOn.inv₀ continuousOn_id
      intro t ht; simp only [id_eq]; linarith [(Set.mem_Icc.mp ht).1]
    · exact hlog_cont
    · intro t ht
      exact ne_of_gt (Real.log_pos (by linarith [(Set.mem_Icc.mp ht).1] : (1:ℝ) < t))
  have hint2 : IntervalIntegrable (fun t : ℝ => t⁻¹ / Real.log t ^ 2) MeasureTheory.volume 2 x := by
    apply ContinuousOn.intervalIntegrable
    rw [Set.uIcc_of_le hx]
    apply ContinuousOn.div
    · apply ContinuousOn.inv₀ continuousOn_id
      intro t ht; simp only [id_eq]; linarith [(Set.mem_Icc.mp ht).1]
    · exact hlog_cont.pow 2
    · intro t ht
      exact pow_ne_zero 2
        (ne_of_gt (Real.log_pos (by linarith [(Set.mem_Icc.mp ht).1] : (1:ℝ) < t)))
  rw [intervalIntegral.integral_add hint1 hint2]
  rw [integral_inv_div_log (by norm_num : (1:ℝ) < 2) (by linarith : (1:ℝ) < x)]
  rw [integral_inv_div_log_sq (by norm_num : (1:ℝ) < 2) (by linarith : (1:ℝ) < x)]
  rw [one_div, one_div]
  ring

theorem integral_psi_mul_kW_eq (x : ℝ) (hx : 2 ≤ x)
    (hint : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Chebyshev.psi t - t) * Work.RHContract.kW t) (Set.Ioi 2)) :
    (∫ t in Set.Ioc (2 : ℝ) x, Chebyshev.psi t * Work.RHContract.kW t)
      = (∫ t in Set.Ioi 2, (Chebyshev.psi t - t) * Work.RHContract.kW t)
        - Work.RHContract.psiTail x
        + (Real.log (Real.log x) - 1 / Real.log x
            - (Real.log (Real.log 2) - 1 / Real.log 2)) := by
  -- `t ↦ t * k(t)` is continuous, hence integrable on the bounded interval `(2, x]`.
  have hlog_cont : ContinuousOn Real.log (Set.Icc (2:ℝ) x) :=
    Real.continuousOn_log.mono (fun t ht => by
      have h0 : (0:ℝ) < t := by linarith [(Set.mem_Icc.mp ht).1]
      simpa using h0.ne')
  have hh_cont : ContinuousOn (fun t : ℝ => t * Work.RHContract.kW t) (Set.Icc (2:ℝ) x) := by
    apply ContinuousOn.mul continuousOn_id
    apply ContinuousOn.div
    · exact hlog_cont.add continuousOn_const
    · exact (continuousOn_id.pow 2).mul (hlog_cont.pow 2)
    · intro t ht
      have h0 : (0:ℝ) < t := by linarith [(Set.mem_Icc.mp ht).1]
      have hl : (0:ℝ) < Real.log t := Real.log_pos (by linarith [(Set.mem_Icc.mp ht).1])
      exact mul_ne_zero (pow_ne_zero 2 h0.ne') (pow_ne_zero 2 hl.ne')
  have hh_int : MeasureTheory.IntegrableOn (fun t : ℝ => t * Work.RHContract.kW t) (Set.Ioc 2 x) :=
    (hh_cont.integrableOn_compact isCompact_Icc).mono_set Set.Ioc_subset_Icc_self
  have hg_int : MeasureTheory.IntegrableOn
      (fun t : ℝ => (Chebyshev.psi t - t) * Work.RHContract.kW t) (Set.Ioc 2 x) :=
    hint.mono_set Set.Ioc_subset_Ioi_self
  -- Split `∫_{(2,x]}(ψ - id)·k` off the full tail `∫_{(2,∞)}`.
  have hg : ∫ t in Set.Ioc (2:ℝ) x, (Chebyshev.psi t - t) * Work.RHContract.kW t
      = (∫ t in Set.Ioi 2, (Chebyshev.psi t - t) * Work.RHContract.kW t)
        - Work.RHContract.psiTail x := by
    rw [Work.RHContract.psiTail]
    exact ((intervalIntegral.integral_Ioi_sub_Ioi hint hx).trans
      (intervalIntegral.integral_of_le hx)).symm
  -- Split the integrand `ψ·k = (ψ - id)·k + id·k` on `(2, x]`.
  have hsplit : (∫ t in Set.Ioc (2:ℝ) x, Chebyshev.psi t * Work.RHContract.kW t)
      = (∫ t in Set.Ioc (2:ℝ) x, (Chebyshev.psi t - t) * Work.RHContract.kW t)
        + (∫ t in Set.Ioc (2:ℝ) x, t * Work.RHContract.kW t) := by
    rw [← MeasureTheory.integral_add hg_int hh_int]
    apply MeasureTheory.setIntegral_congr_fun measurableSet_Ioc
    intro t ht
    ring
  rw [hsplit, hg, integral_id_mul_kW x hx]

end Work.RHContract.Identity.TailSplit
