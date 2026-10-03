import Mathlib
import Submission.Commons.Analysis.Integral.intervalIntegral_tsum_of_dominated
import Submission.Work.FIArea6Road.ZsfunTermNorm
import Submission.Work.FIArea6Road.ZsfunTermContinuous
import Submission.Work.FIArea6Road.ZsfunTermIntegralBound

namespace Work.FIArea6Road

/-- Reverse triangle inequality, in the form needed for lower bounds on norms. -/
lemma norm_sub_le_norm_add (x y : ℂ) : ‖x‖ - ‖y‖ ≤ ‖x + y‖ := by
  have h := norm_sub_norm_le x (-y)
  rwa [norm_neg, sub_neg_eq_add] at h

/-- Bohr-type mean value lower bound for the Dirichlet series `∑ a n · n ^ (-s)`
on the vertical line `Re s = σ > 1`. -/
theorem ZsfunBohrMean {a : ℕ → ℂ} (h1 : a 1 = 1)
    {σ T : ℝ} (hσ : 1 < σ) (hT : 0 < T)
    (hsumm : Summable (fun n : ℕ => ‖a n‖ * (n : ℝ) ^ (-σ))) :
    1 - 2 * (∑' n : ℕ, ‖a n‖ * (n : ℝ) ^ (-σ)) / (T * Real.log 2)
      ≤ ‖(1 / T) * ∫ t in (0 : ℝ)..T,
          (∑' n : ℕ, a n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ := by
  have hσpos : 0 < σ := by linarith
  have hlog2 : 0 < Real.log 2 := Real.log_pos (by norm_num)
  set u : ℕ → ℝ := fun n => ‖a n‖ * (n : ℝ) ^ (-σ) with hu
  have hsum_u : Summable u := by rw [hu]; exact hsumm
  set f : ℕ → ℝ → ℂ := fun n t => a n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)) with hf
  -- continuity and domination, for the Weierstrass M-test
  have hcont : ∀ n, Continuous (f n) := fun n => by
    rw [hf]; exact ZsfunTermContinuous a hσpos n
  have hbd : ∀ n y, y ∈ Set.Icc (0 : ℝ) T → ‖f n y‖ ≤ u n := fun n y _ => by
    rw [hf, hu]; exact ZsfunTermNorm a hσ y n
  -- interchange of the interval integral with the series
  have hint : ∫ t in (0 : ℝ)..T, (∑' n, f n t) = ∑' n, (∫ t in (0 : ℝ)..T, f n t) :=
    Commons.Analysis.Integral.intervalIntegral_tsum_of_dominated hT.le f u hcont hsum_u hbd
  -- summability of the term-by-term integrals
  have hF : Summable fun n => ∫ t in (0 : ℝ)..T, f n t := by
    refine Summable.of_norm_bounded (hsum_u.mul_left T) fun n => ?_
    calc ‖∫ t in (0 : ℝ)..T, f n t‖ ≤ u n * |T - 0| := by
          refine intervalIntegral.norm_integral_le_of_norm_le_const fun x _ => ?_
          rw [hf, hu]; exact ZsfunTermNorm a hσ x n
      _ = T * u n := by rw [sub_zero, abs_of_pos hT, mul_comm]
  have hsplit := Summable.sum_add_tsum_nat_add (f := fun n => ∫ t in (0 : ℝ)..T, f n t) 2 hF
  have hsum2 : (∑ i ∈ Finset.range 2, (∫ t in (0 : ℝ)..T, f i t))
      = (∫ t in (0 : ℝ)..T, f 0 t) + (∫ t in (0 : ℝ)..T, f 1 t) := by
    simp [Finset.sum_range_succ]
  -- the terms with n = 0 and n = 1
  have hF0 : (∫ t in (0 : ℝ)..T, f 0 t) = 0 := by
    have hz : ∀ t : ℝ, f 0 t = 0 := by
      intro t
      have hy : (-((σ : ℂ) + (t : ℂ) * Complex.I)) ≠ 0 := by
        intro h
        have hre : (-((σ : ℂ) + (t : ℂ) * Complex.I)).re = 0 := by rw [h]; simp
        simp at hre
        linarith
      rw [hf]
      simp only [Nat.cast_zero, Complex.zero_cpow hy, mul_zero]
    simp [hz]
  have hF1 : (∫ t in (0 : ℝ)..T, f 1 t) = a 1 * (T : ℂ) := by
    have hc : (∫ t in (0 : ℝ)..T, f 1 t) = ∫ t in (0 : ℝ)..T, (a 1) := by
      apply intervalIntegral.integral_congr
      intro t _
      simp [hf]
    rw [hc, intervalIntegral.integral_const, Complex.real_smul, sub_zero]
    ring
  have hF1norm : ‖∫ t in (0 : ℝ)..T, f 1 t‖ = T := by
    rw [hF1, h1, one_mul]
    simp [abs_of_pos hT]
  -- the tail bound
  have htail_summable : Summable fun k => u (k + 2) := (summable_nat_add_iff 2).mpr hsum_u
  have hc : ∀ k : ℕ, ‖∫ t in (0 : ℝ)..T, f (k + 2) t‖ ≤ u (k + 2) * (2 / Real.log 2) := by
    intro k
    have h := ZsfunTermIntegralBound a hσ hT (n := k + 2) (by omega)
    rw [hf, hu]
    exact h
  have htail_bound : ‖∑' k, (∫ t in (0 : ℝ)..T, f (k + 2) t)‖
      ≤ (2 / Real.log 2) * (∑' k, u (k + 2)) := by
    have hsum_norm : Summable fun k => ‖∫ t in (0 : ℝ)..T, f (k + 2) t‖ :=
      Summable.of_nonneg_of_le (fun k => norm_nonneg _) hc
        (htail_summable.mul_right (2 / Real.log 2))
    calc ‖∑' k, (∫ t in (0 : ℝ)..T, f (k + 2) t)‖
        ≤ ∑' k, ‖∫ t in (0 : ℝ)..T, f (k + 2) t‖ := norm_tsum_le_tsum_norm hsum_norm
      _ ≤ ∑' k, u (k + 2) * (2 / Real.log 2) :=
          Summable.tsum_le_tsum hc hsum_norm (htail_summable.mul_right (2 / Real.log 2))
      _ = (∑' k, u (k + 2)) * (2 / Real.log 2) := by rw [tsum_mul_right]
      _ = (2 / Real.log 2) * (∑' k, u (k + 2)) := by rw [mul_comm]
  -- the tail is dominated by the full sum
  have htail_le : ∑' k, u (k + 2) ≤ ∑' n, u n := by
    have h := Summable.sum_add_tsum_nat_add (f := u) 2 hsum_u
    have h2 : (∑ i ∈ Finset.range 2, u i) = u 0 + u 1 := by simp [Finset.sum_range_succ]
    rw [h2] at h
    have h0 : 0 ≤ u 0 := by rw [hu]; positivity
    have h1' : 0 ≤ u 1 := by rw [hu]; positivity
    linarith
  -- lower bound for the norm of the integral of the whole series
  have hkey : T - (2 / Real.log 2) * (∑' k, u (k + 2))
      ≤ ‖∑' n, (∫ t in (0 : ℝ)..T, f n t)‖ := by
    rw [← hsplit, hsum2]
    have hF0norm : ‖∫ t in (0 : ℝ)..T, f 0 t‖ = 0 := by rw [hF0, norm_zero]
    have hA : T ≤ ‖(∫ t in (0 : ℝ)..T, f 0 t) + (∫ t in (0 : ℝ)..T, f 1 t)‖ := by
      have h1 := norm_sub_le_norm_add (∫ t in (0 : ℝ)..T, f 1 t) (∫ t in (0 : ℝ)..T, f 0 t)
      rw [hF1norm, hF0norm, sub_zero, add_comm] at h1
      exact h1
    have hB := norm_sub_le_norm_add
      ((∫ t in (0 : ℝ)..T, f 0 t) + (∫ t in (0 : ℝ)..T, f 1 t))
      (∑' k, (∫ t in (0 : ℝ)..T, f (k + 2) t))
    linarith [hA, hB, htail_bound]
  have hmain : T - (2 / Real.log 2) * (∑' n, u n)
      ≤ ‖∫ t in (0 : ℝ)..T, (∑' n, f n t)‖ := by
    rw [hint]
    have hc2 : 0 < 2 / Real.log 2 := by positivity
    have hstep : T - (2 / Real.log 2) * (∑' n, u n)
        ≤ T - (2 / Real.log 2) * (∑' k, u (k + 2)) := by
      have hmul := mul_le_mul_of_nonneg_left htail_le hc2.le
      linarith
    exact le_trans hstep hkey
  -- convert to the explicit form appearing in the statement
  have hSu : (∑' n, u n) = ∑' n : ℕ, ‖a n‖ * (n : ℝ) ^ (-σ) := by rw [hu]
  have hPf : (∫ t in (0 : ℝ)..T, (∑' n, f n t))
      = ∫ t in (0 : ℝ)..T, (∑' n : ℕ, a n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))) := by
    rw [hf]
  rw [hSu, hPf] at hmain
  -- the identity for the left-hand side
  have hLHS : 1 - 2 * (∑' n : ℕ, ‖a n‖ * (n : ℝ) ^ (-σ)) / (T * Real.log 2)
      = (1 / T) * (T - (2 / Real.log 2) * (∑' n : ℕ, ‖a n‖ * (n : ℝ) ^ (-σ))) := by
    field_simp
    try ring
  -- the norm of the scaled integral
  have hnorm : ‖(1 / T) * ∫ t in (0 : ℝ)..T,
        (∑' n : ℕ, a n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖
      = (1 / T) * ‖∫ t in (0 : ℝ)..T,
        (∑' n : ℕ, a n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ := by
    rw [norm_mul]
    congr 1
    simp [abs_of_pos hT]
  have hom : (1 / T) * (T - (2 / Real.log 2) * (∑' n : ℕ, ‖a n‖ * (n : ℝ) ^ (-σ)))
      ≤ ‖(1 / T) * ∫ t in (0 : ℝ)..T,
          (∑' n : ℕ, a n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I)))‖ := by
    rw [hnorm]
    exact mul_le_mul_of_nonneg_left hmain (by positivity)
  rw [hSu, hLHS]
  exact hom

end Work.FIArea6Road
