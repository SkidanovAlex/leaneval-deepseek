import Mathlib
import Submission.Work.Pert.V5.Basics

namespace Work.Pert.V5

/-- **The route-P arithmetic gate.**  With the pin `Ξ + 2 Rde ≤ M + 2 Kp L` (`L = 1 + log (2+M)`)
the route-P cost `C₂ 2^6 (1+Ξ) L + 2^24 (1 + 1/rr) Lg` fits into the three allowance slots
`C₂ 2^40 K L + 2^40 K L + Kp 2^38 K L`, where `K = 1 + Ξ + 1/Ξ + 1/rr` and
`Lg = 1 + log (2 + 16 (M + 2 + Ξ))`.

The only non-trivial input is the logarithmic comparison
`log (2 + 16 (M+2+Ξ)) ≤ 5 + L + Kp L`, which follows from the pin by
`2 + 16 (M+2+Ξ) ≤ 32 ((M+2) + Kp L)`, then
`log (32 ((M+2) + Kp L)) ≤ log 32 + log (M+2) + log (1 + Kp L) ≤ 5 + (L-1) + Kp L`. -/
theorem P_le_B_pin {Ξ rr M Kp Rde C₂ : ℝ} (hΞ : 0 < Ξ) (hrr : 0 < rr) (hM : 2 ^ 10 ≤ M)
    (hKp : 0 ≤ Kp) (hRde : 0 < Rde) (hC₂ : 0 < C₂)
    (hpin : Ξ + 2 * Rde ≤ M + 2 * Kp * (1 + Real.log (2 + M))) :
    C₂ * 2 ^ 6 * (1 + Ξ) * (1 + Real.log (2 + M))
        + 2 ^ 24 * (1 + 1 / rr) * (1 + Real.log (2 + 16 * (M + 2 + Ξ)))
      ≤ C₂ * 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
        + 2 ^ 40 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M))
        + Kp * 2 ^ 38 * (1 + Ξ + 1 / Ξ + 1 / rr) * (1 + Real.log (2 + M)) := by
  set L : ℝ := 1 + Real.log (2 + M) with hLdef
  set K : ℝ := 1 + Ξ + 1 / Ξ + 1 / rr with hKdef
  set Lg : ℝ := 1 + Real.log (2 + 16 * (M + 2 + Ξ)) with hLgdef
  have hM1024 : (1024 : ℝ) ≤ M := by norm_num at hM ⊢; exact hM
  have hL1 : 1 ≤ L := by
    rw [hLdef]
    have h : 0 ≤ Real.log (2 + M) := Real.log_nonneg (by linarith)
    linarith
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL1
  have hKpos : 0 < K := by
    rw [hKdef]
    have h1 : 0 < 1 / Ξ := by positivity
    have h2 : 0 < 1 / rr := by positivity
    linarith
  have hXK : 1 + Ξ ≤ K := by
    rw [hKdef]
    have h1 : 0 ≤ 1 / Ξ := by positivity
    have h2 : 0 ≤ 1 / rr := by positivity
    linarith
  have hAK : 1 + 1 / rr ≤ K := by
    rw [hKdef]
    have h1 : 0 ≤ 1 / Ξ := by positivity
    linarith
  have hKL : 0 ≤ Kp * L := mul_nonneg hKp (le_of_lt hLpos)
  -- the pin, in terms of `L`
  have hΞle : Ξ ≤ M + 2 * Kp * L := by
    rw [hLdef]
    linarith [hpin, hRde]
  -- the logarithmic comparison
  have harg_pos : (0 : ℝ) < 2 + 16 * (M + 2 + Ξ) := by linarith
  have hstep1 : 2 + 16 * (M + 2 + Ξ) ≤ 32 * ((M + 2) + Kp * L) := by nlinarith [hΞle]
  have h32pos : (0 : ℝ) < (M + 2) + Kp * L := by linarith
  have hstep2 : Real.log (2 + 16 * (M + 2 + Ξ)) ≤ Real.log (32 * ((M + 2) + Kp * L)) :=
    Real.log_le_log harg_pos hstep1
  have hstep3 : Real.log (32 * ((M + 2) + Kp * L))
      = Real.log 32 + Real.log ((M + 2) + Kp * L) :=
    Real.log_mul (by norm_num) (ne_of_gt h32pos)
  have hstep4 : Real.log ((M + 2) + Kp * L) ≤ Real.log ((M + 2) * (1 + Kp * L)) := by
    apply Real.log_le_log
    · linarith
    · nlinarith [hKL, hM1024]
  have hstep5 : Real.log ((M + 2) * (1 + Kp * L))
      = Real.log (M + 2) + Real.log (1 + Kp * L) :=
    Real.log_mul (by linarith) (by linarith)
  have hstep6 : Real.log (1 + Kp * L) ≤ Kp * L := by
    have h := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 1 + Kp * L by linarith)
    linarith
  have hlog32 : Real.log 32 ≤ 5 := by
    have h : Real.log ((32 : ℝ)) = 5 * Real.log 2 := by
      rw [show (32 : ℝ) = 2 ^ 5 by norm_num, Real.log_pow]
      norm_num
    have h2 : Real.log (2 : ℝ) ≤ 1 := by
      have := Real.log_le_sub_one_of_pos (show (0 : ℝ) < 2 by norm_num)
      linarith
    linarith
  have hlogM : Real.log (M + 2) = L - 1 := by
    rw [hLdef, show (2 : ℝ) + M = M + 2 by ring]
    ring
  have hchain : Real.log (2 + 16 * (M + 2 + Ξ)) ≤ 5 + (L - 1) + Kp * L := by
    linarith [hstep2, hstep3, hstep4, hstep5, hstep6, hlog32, hlogM]
  have hLg_le : Lg ≤ 2 ^ 16 * L + 2 ^ 14 * (Kp * L) := by
    rw [hLgdef]
    have h5 : 5 + L + Kp * L ≤ 2 ^ 16 * L + 2 ^ 14 * (Kp * L) := by
      nlinarith [hL1, hKL, hLpos]
    linarith [hchain, h5]
  have hLgpos : 0 < Lg := by
    rw [hLgdef]
    have h : 0 ≤ Real.log (2 + 16 * (M + 2 + Ξ)) := Real.log_nonneg (by linarith)
    linarith
  -- the `C₂`-slot dominates the first term
  have h1 : C₂ * 2 ^ 6 * (1 + Ξ) * L ≤ C₂ * 2 ^ 40 * K * L := by
    have hA : C₂ * 2 ^ 6 ≤ C₂ * 2 ^ 40 :=
      mul_le_mul_of_nonneg_left (by norm_num : (2 : ℝ) ^ 6 ≤ (2 : ℝ) ^ 40) (le_of_lt hC₂)
    have hB : C₂ * 2 ^ 6 * (1 + Ξ) ≤ C₂ * 2 ^ 40 * K :=
      mul_le_mul hA hXK (by positivity) (by positivity)
    exact mul_le_mul_of_nonneg_right hB (le_of_lt hLpos)
  -- the last two slots dominate the second term
  have h2 : 2 ^ 24 * (1 + 1 / rr) * Lg ≤ 2 ^ 40 * K * L + Kp * 2 ^ 38 * K * L := by
    have hAB : 2 ^ 24 * (1 + 1 / rr) ≤ 2 ^ 24 * K :=
      mul_le_mul_of_nonneg_left hAK (by norm_num)
    have h2a : 2 ^ 24 * (1 + 1 / rr) * Lg
        ≤ (2 ^ 24 * K) * (2 ^ 16 * L + 2 ^ 14 * (Kp * L)) :=
      mul_le_mul hAB hLg_le (le_of_lt hLgpos) (by positivity)
    have h2b : (2 ^ 24 * K) * (2 ^ 16 * L + 2 ^ 14 * (Kp * L))
        = 2 ^ 40 * K * L + Kp * 2 ^ 38 * K * L := by
      ring
    rw [h2b] at h2a
    exact h2a
  linarith [h1, h2]

end Work.Pert.V5
