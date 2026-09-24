import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiLevelCore
import Submission.Work.NumberTheory.Chen.APSwitchUpper.integral_oddSum_Icc
import Submission.Work.NumberTheory.Chen.APSwitchUpper.integral_L1lo
import Submission.Work.NumberTheory.Chen.APSwitchUpper.logPad2_L1_lower

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory

/-- **Lower bound for `Aprime 4`.**  On `[2,4]` the integrand `log (3/(u-1))/u` dominates the
elementary rational function `(2·((4-u)/(u+2)) + (2/3)·((4-u)/(u+2))³)/u`, whose integral over
`[2,4]` is `-5/4 + (64/3)·log 2 - 12·log 3`. -/
lemma Aprime_four_lower :
    (-5 / 4 + (64 / 3 : ℝ) * Real.log 2 - 12 * Real.log 3) ≤ Aprime 4 := by
  rw [Aprime]
  have hcont_h : ContinuousOn (fun u : ℝ => Real.log (3 / (u - 1)) / u) (Set.uIcc (2 : ℝ) 4) := by
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
    refine ContinuousOn.div ?_ continuousOn_id (fun x hx => ?_)
    · refine ContinuousOn.log (ContinuousOn.div continuousOn_const
        (continuousOn_id.sub continuousOn_const) ?_) ?_
      · intro x hx; rw [Set.mem_Icc] at hx; linarith [hx.1]
      · intro x hx; rw [Set.mem_Icc] at hx
        have hx1 : 0 < x - 1 := by linarith [hx.1]
        exact ne_of_gt (by positivity)
    · rw [Set.mem_Icc] at hx; linarith [hx.1]
  have hcont_g : ContinuousOn
      (fun u : ℝ => (2 * ((4 - u) / (u + 2)) + (2 / 3 : ℝ) * ((4 - u) / (u + 2)) ^ 3) / u)
      (Set.uIcc (2 : ℝ) 4) := by
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
    apply ContinuousOn.div
    · apply ContinuousOn.add
      · apply ContinuousOn.const_mul
        apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro x hx; linarith [(Set.mem_Icc.mp hx).1]
      · apply ContinuousOn.const_mul
        apply ContinuousOn.pow
        apply ContinuousOn.div
        · fun_prop
        · fun_prop
        · intro x hx; linarith [(Set.mem_Icc.mp hx).1]
    · fun_prop
    · intro x hx; linarith [(Set.mem_Icc.mp hx).1]
  have hle := intervalIntegral.integral_mono_on (f := fun u : ℝ =>
        (2 * ((4 - u) / (u + 2)) + (2 / 3 : ℝ) * ((4 - u) / (u + 2)) ^ 3) / u)
      (g := fun u : ℝ => Real.log (3 / (u - 1)) / u)
      (a := (2 : ℝ)) (b := (4 : ℝ)) (μ := volume) (by norm_num)
      hcont_g.intervalIntegrable hcont_h.intervalIntegrable
      (fun x hx => by
        rw [Set.mem_Icc] at hx
        have hx0 : (0 : ℝ) < x := by linarith [hx.1]
        have hbase := logPad2_L1_lower x hx.1 hx.2
        simpa using div_le_div_of_nonneg_right hbase hx0.le)
  rw [integral_L1lo] at hle
  exact hle

theorem Cv_lower (n : ℕ) :
    (3 + Cv n) * (-5 / 4 + (64 / 3 : ℝ) * Real.log 2 - 12 * Real.log 3)
      + (Tv (n + 1) - 4) * Real.log 2 + 2 ≤ Cv (n + 1) := by
  -- The integral of the first odd level on `[2,4]`.
  have hcc : (∫ u in (2 : ℝ)..4, oddSum (n + 1) u)
      = (3 + Cv n) * Aprime 4 + (Tv (n + 1) - 4) * Real.log 2 + 2 :=
    integral_oddSum_Icc n
  -- `Cv (n+1)` dominates the integral over the sub-interval `[2,4]`.
  have hM : (4 : ℝ) ≤ ((2 * (n + 1) + 4 : ℕ) : ℝ) := by
    have h : (4 : ℕ) ≤ 2 * (n + 1) + 4 := by omega
    exact_mod_cast h
  have hlow : (∫ u in (2 : ℝ)..4, oddSum (n + 1) u) ≤ Cv (n + 1) := by
    have hsplit := intervalIntegral.integral_add_adjacent_intervals
      (oddSum_intervalIntegrable (n + 1) (2 : ℝ) 4)
      (oddSum_intervalIntegrable (n + 1) (4 : ℝ) ((2 * (n + 1) + 4 : ℕ) : ℝ))
    have hnonneg : 0 ≤ ∫ u in (4 : ℝ)..((2 * (n + 1) + 4 : ℕ) : ℝ), oddSum (n + 1) u :=
      intervalIntegral.integral_nonneg_of_forall hM (fun u => oddSum_nonneg (n + 1) u)
    rw [Cv]
    linarith
  have h3 : (0 : ℝ) ≤ 3 + Cv n := by linarith [Cv_nonneg n]
  have hmul := mul_le_mul_of_nonneg_left Aprime_four_lower h3
  calc (3 + Cv n) * (-5 / 4 + (64 / 3 : ℝ) * Real.log 2 - 12 * Real.log 3)
        + (Tv (n + 1) - 4) * Real.log 2 + 2
      ≤ (3 + Cv n) * Aprime 4 + (Tv (n + 1) - 4) * Real.log 2 + 2 := by linarith
    _ = ∫ u in (2 : ℝ)..4, oddSum (n + 1) u := hcc.symm
    _ ≤ Cv (n + 1) := hlow

end Work.NumberTheory.Chen.APSwitchUpper
