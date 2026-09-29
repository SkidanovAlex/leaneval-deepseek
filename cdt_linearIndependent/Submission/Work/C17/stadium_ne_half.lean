import Mathlib
import Submission.Work.C17.logPw_setup

/-!
# `Work.C17.stadium_ne_half`

The stadium `stadiumSet c δ ρ` (the union of the discs joining a disc of radius `δ` around the
real cusp `c` to the disc of radius `ρ = 1/64` around `p₀ = 1/4 + i/5`) does not contain the
point `1/2`.  The point `1/2` stays at distance `≥ 1/64` from every point of the segment
`[c, p₀]`, while every disc of the stadium has radius `≤ 1/64`.

The distance computation is the elementary real inequality `stadium_core` below.
-/

namespace Work.C17

open Complex

noncomputable section

/-- **Elementary distance bound.** For `3/4 ≤ c < 1` and `t ∈ [0,1]`, the point `1/2`
is at distance `≥ 1/64` from `(1-t)c + t·(1/4 + i/5)`: if `t ≥ 1/8` the imaginary part
`t/5 ≥ 1/40` already gives the bound, while if `t < 1/8` the real part of the difference is
`≥ (7/8)·(3/4) - 1/2 = 5/32`. -/
theorem stadium_core {c t : ℝ} (hc : 3 / 4 ≤ c) (hc1 : c < 1) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    (1 / 64 : ℝ) ^ 2 ≤ ((1 - t) * c + t * (1 / 4) - 1 / 2) ^ 2 + (t / 5) ^ 2 := by
  rcases le_or_gt (1 / 8) t with h | h
  · have h1 : (1 / 64 : ℝ) ≤ t / 5 := by linarith
    have h2 : (1 / 64 : ℝ) ^ 2 ≤ (t / 5) ^ 2 := by nlinarith [h1, ht0]
    nlinarith [h2]
  · have h1 : (7 / 8 : ℝ) ≤ 1 - t := by linarith
    have h2 : (7 / 8 : ℝ) * (3 / 4) ≤ (1 - t) * c :=
      mul_le_mul h1 hc (by norm_num) (by linarith)
    have h3 : (5 / 32 : ℝ) ≤ (1 - t) * c + t * (1 / 4) - 1 / 2 := by linarith
    nlinarith [sq_nonneg ((1 - t) * c + t * (1 / 4) - 1 / 2 - 5 / 32), h3]

theorem stadium_ne_half {c δ ρ : ℝ} (hc : 3 / 4 ≤ c) (hc1 : c < 1)
    (hδ : δ = min ((1 - c) / 2) (1 / 64)) (hρ : ρ = 1 / 64) :
    ∀ z ∈ stadiumSet c δ ρ, z ≠ 1 / 2 := by
  intro z hz h
  obtain ⟨t, ht, hzball⟩ := hz
  rw [Set.mem_Icc] at ht
  obtain ⟨ht0, ht1⟩ := ht
  subst h
  rw [Metric.mem_ball, dist_eq_norm] at hzball
  -- every stadium disc has radius `≤ 1/64`
  have hdle : (1 - t) * δ + t * ρ ≤ 1 / 64 := by
    rw [hδ, hρ]
    have h1 : (1 - t) * min ((1 - c) / 2) (1 / 64) ≤ (1 - t) * (1 / 64) :=
      mul_le_mul_of_nonneg_left (min_le_right _ _) (by linarith)
    linarith
  -- `1/2` is at distance `≥ 1/64` from the centre of that disc
  have hcore := stadium_core hc hc1 ht0 ht1
  have hre : ((1 / 2 : ℂ) - (((((1 - t) * c : ℝ)) : ℂ) + (t : ℂ) * p0C)).re
      = 1 / 2 - ((1 - t) * c + t * (1 / 4)) := by
    simp [p0C]
  have him : ((1 / 2 : ℂ) - (((((1 - t) * c : ℝ)) : ℂ) + (t : ℂ) * p0C)).im
      = -(t / 5) := by
    simp [p0C]
    ring
  have hns : (1 / 64 : ℝ) ^ 2
      ≤ ‖(1 / 2 : ℂ) - (((((1 - t) * c : ℝ)) : ℂ) + (t : ℂ) * p0C)‖ ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    nlinarith [hcore]
  have hge : (1 / 64 : ℝ)
      ≤ ‖(1 / 2 : ℂ) - (((((1 - t) * c : ℝ)) : ℂ) + (t : ℂ) * p0C)‖ := by
    have := (sq_le_sq.mp hns)
    simpa using this
  linarith

end

end Work.C17
