/-
# `APSwitchUpper.integral_oddSum_Icc` — the integral of the first odd level on `[2,4]`

The level constants `Cv n = ∫_2^{2n+4} oddSum n` and `Tv n = ∫_3^{2n+3} evenSum n`
(`APSwitchUpper/riPhi_le_env.lean`) control the delay calculus of the Rosser–Iwaniec
profile family.  Here we compute the integral of the *first odd level* across the
support corner `[2,4]`:

  `∫_2^4 oddSum (n+1) = (3 + Cv n) · A'(4) + (Tv (n+1) − 4) · log 2 + 2`,

where `A'(x) = ∫_2^x log(3/(u−1))/u du` (`APSwitchUpper/riPhiEnvDefs.lean`).

The computation goes through the closed form of `oddSum (n+1)` on `[2,4]`: combining the
summed odd recursion `s · oddSum (n+1) s = ∫_{s-1}^{2n+5} evenSum (n+1)` with the
even formula `evenSum (n+1) t = ((3−t) + Cv n)/t` on `[1,3]` gives

  `u · oddSum (n+1) u = (3 + Cv n) · log(3/(u−1)) − 4 + u + Tv (n+1)`  for `2 ≤ u ≤ 4`,

and integrating the right side (i.e. `(3+Cv n)·log(3/(u−1))/u + (Tv(n+1)−4)/u + 1`)
over `[2,4]` produces the stated identity.
-/
import Mathlib
import Submission.Work.NumberTheory.Chen.APSwitchUpper.riPhiLevelCore

namespace Work.NumberTheory.Chen.APSwitchUpper

open MeasureTheory

/-- **Closed form of `u · oddSum (n+1) u` on `[2,4]`.**  Decomposing the summed odd
recursion at the point `3` and using the even formula on `[1,3]`. -/
lemma mul_oddSum_formula (n : ℕ) {u : ℝ} (h2 : 2 ≤ u) (h4 : u ≤ 4) :
    u * oddSum (n + 1) u = (3 + Cv n) * Real.log (3 / (u - 1)) - 4 + u + Tv (n + 1) := by
  have hu3 : u - 1 ≤ 3 := by linarith
  rw [oddSum_mul_integral (n + 1) h2]
  rw [← intervalIntegral.integral_add_adjacent_intervals
      (evenSum_intervalIntegrable (n + 1) (u - 1) 3)
      (evenSum_intervalIntegrable (n + 1) 3 _)]
  have hTv : (∫ t in (3 : ℝ)..((2 * (n + 1) + 3 : ℕ) : ℝ), evenSum (n + 1) t)
      = Tv (n + 1) := rfl
  rw [hTv]
  have hcongr : (∫ t in (u - 1)..(3 : ℝ), evenSum (n + 1) t)
      = ∫ t in (u - 1)..(3 : ℝ), ((3 + Cv n) * t⁻¹ - 1) := by
    refine intervalIntegral.integral_congr ?_
    intro t ht
    rw [Set.uIcc_of_le hu3, Set.mem_Icc] at ht
    have ht1 : (1 : ℝ) ≤ t := by linarith [ht.1]
    have ht0 : t ≠ 0 := by linarith [ht.1]
    rw [evenSum_formula n ht1 ht.2]
    field_simp
    ring
  rw [hcongr]
  have hint1 : IntervalIntegrable (fun t : ℝ => (3 + Cv n) * t⁻¹) volume (u - 1) 3 := by
    refine ContinuousOn.intervalIntegrable ?_
    refine continuousOn_const.mul ?_
    exact continuousOn_id.inv₀ (fun x hx => by
      rw [Set.uIcc_of_le hu3, Set.mem_Icc] at hx
      simp only [id_eq]
      linarith [hx.1])
  have hint2 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (u - 1) 3 := intervalIntegrable_const
  rw [intervalIntegral.integral_sub hint1 hint2,
    intervalIntegral.integral_const_mul, integral_one,
    integral_inv_of_pos (by linarith) (by norm_num)]
  linarith

theorem integral_oddSum_Icc (n : ℕ) :
    ∫ u in (2 : ℝ)..4, oddSum (n + 1) u
      = (3 + Cv n) * Aprime 4 + (Tv (n + 1) - 4) * Real.log 2 + 2 := by
  have hform : ∀ u ∈ Set.uIcc (2 : ℝ) 4, oddSum (n + 1) u
      = (3 + Cv n) * (Real.log (3 / (u - 1)) / u) + (Tv (n + 1) - 4) * u⁻¹ + 1 := by
    intro u hu
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4), Set.mem_Icc] at hu
    have hu0 : u ≠ 0 := by linarith [hu.1]
    have hdiv : oddSum (n + 1) u
        = ((3 + Cv n) * Real.log (3 / (u - 1)) - 4 + u + Tv (n + 1)) / u := by
      rw [eq_div_iff hu0, mul_comm]
      exact mul_oddSum_formula n hu.1 hu.2
    rw [hdiv]
    field_simp
    ring
  rw [intervalIntegral.integral_congr hform]
  have hcont : ContinuousOn (fun u : ℝ => Real.log (3 / (u - 1)) / u) (Set.uIcc (2 : ℝ) 4) := by
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4)]
    refine ContinuousOn.div ?_ continuousOn_id (fun x hx => ?_)
    · refine ContinuousOn.log (ContinuousOn.div continuousOn_const
        (continuousOn_id.sub continuousOn_const) ?_) ?_
      · intro x hx; rw [Set.mem_Icc] at hx; linarith [hx.1]
      · intro x hx; rw [Set.mem_Icc] at hx
        have hx1 : 0 < x - 1 := by linarith [hx.1]
        exact ne_of_gt (by positivity)
    · rw [Set.mem_Icc] at hx; linarith [hx.1]
  have hI1 : IntervalIntegrable (fun u : ℝ => (3 + Cv n) * (Real.log (3 / (u - 1)) / u))
      volume (2 : ℝ) 4 := (hcont.const_mul (3 + Cv n)).intervalIntegrable
  have hI2 : IntervalIntegrable (fun u : ℝ => (Tv (n + 1) - 4) * u⁻¹) volume (2 : ℝ) 4 := by
    refine ((ContinuousOn.inv₀ (f := fun x : ℝ => x) continuousOn_id ?_).const_mul
      (Tv (n + 1) - 4)).intervalIntegrable
    intro x hx
    rw [Set.uIcc_of_le (by norm_num : (2 : ℝ) ≤ 4), Set.mem_Icc] at hx
    linarith [hx.1]
  have hI3 : IntervalIntegrable (fun _ : ℝ => (1 : ℝ)) volume (2 : ℝ) 4 := intervalIntegrable_const
  rw [intervalIntegral.integral_add (hI1.add hI2) hI3, intervalIntegral.integral_add hI1 hI2,
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul,
    integral_inv_of_pos (by norm_num : (0 : ℝ) < 2) (by norm_num : (0 : ℝ) < 4), integral_one]
  have hApr : (∫ u in (2 : ℝ)..4, Real.log (3 / (u - 1)) / u) = Aprime 4 := rfl
  rw [hApr]
  norm_num

end Work.NumberTheory.Chen.APSwitchUpper
