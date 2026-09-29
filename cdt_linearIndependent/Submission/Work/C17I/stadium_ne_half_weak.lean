import Mathlib
import Submission.Work.C17.logPw_setup

/-!
# `Work.C17I.stadium_ne_half_weak`

The weak form of `Work.C17.stadium_ne_half`: for

* `c ≥ 1 - 1/100000` (the cusp value `x_s = xsOf m n` is close to `1`, from below or above),
* `δ ≤ (1-c)/2` (any radius for the disc around `c` at most half the distance to `1`),
* `ρ ≤ 1/20` (any radius for the disc around `p₀ = 1/4 + i/5` at most `1/20`),

the stadium `stadiumSet c δ ρ = ⋃_{t ∈ [0,1]} ball ((1-t)c + t·p₀) ((1-t)δ + tρ)` does not
contain the point `1/2`.

The point `1/2` is at distance `≥ 1/8` from the segment joining `c` to `p₀`, while every stadium
disc has radius `≤ 1/20`; the elementary real estimate is `stadium_core_weak` below, which
combines the imaginary part `t/5` of `1/2 - ((1-t)c + t·p₀)` (dominating for `t ≥ 1/8`) with the
real part `(1-t)(1/2 - c) + t/4` (dominating for `t ≤ 1/8`, where it is `≤ -1/16`).

The key point is that the bound is only linear in the deficit `1 - c`: the *radius* is bounded
by `(1-t)/200000 + t/20`, i.e. `δ ≤ (1-c)/2 ≤ 1/200000` is used directly, without any
`min` with `1/64`.
-/

namespace Work.C17I

/-- **Numerical core of `stadium_ne_half_weak`.**  For `c ≥ 1 - 1/100000` and `t ∈ [0,1]`
the point `1/2` is at distance at least `(1-t)/200000 + t/20` from `(1-t)c + t·p₀`, where
`p₀ = 1/4 + i/5`; equivalently, in the coordinates of the two terms
`re = (1-t)(1/2-c) + t/4`, `im = -t/5` of the difference. -/
theorem stadium_core_weak {c t : ℝ} (hc : 1 - 1 / 100000 ≤ c) (ht0 : 0 ≤ t) (ht1 : t ≤ 1) :
    ((1 - t) / 200000 + t / 20) ^ 2
      ≤ ((1 - t) * (1 / 2 - c) + t * (1 / 4)) ^ 2 + (t / 5) ^ 2 := by
  rcases le_or_gt (1 / 8) t with h | h
  · -- `t ≥ 1/8`: the imaginary part `t/5` alone dominates `(1-t)/200000 + t/20`.
    have hRle : (1 - t) / 200000 + t / 20 ≤ t / 5 := by linarith
    have hRnn : (0 : ℝ) ≤ (1 - t) / 200000 + t / 20 := by
      have h1 : (0 : ℝ) ≤ 1 - t := sub_nonneg.mpr ht1
      have h2 : (0 : ℝ) ≤ t := ht0
      positivity
    nlinarith [sq_nonneg ((1 - t) * (1 / 2 - c) + t * (1 / 4))]
  · -- `t ≤ 1/8`: the real part is `≤ -1/16`, while the bound is `≤ 1/16`.
    have h1 : 7 / 8 ≤ 1 - t := by linarith
    have h2 : 1 / 2 - c ≤ 0 := by linarith
    have h3 : 1 / 2 - c ≤ -1 / 2 + 1 / 100000 := by linarith
    have h4 : (1 - t) * (1 / 2 - c) ≤ (7 / 8) * (1 / 2 - c) :=
      mul_le_mul_of_nonpos_right h1 h2
    have h5 : (7 / 8) * (1 / 2 - c) ≤ (7 / 8) * (-1 / 2 + 1 / 100000) := by linarith
    have hbr : (1 - t) * (1 / 2 - c) + t * (1 / 4) ≤ -1 / 16 := by linarith
    have hRsm : (1 - t) / 200000 + t / 20 ≤ 1 / 16 := by linarith
    nlinarith [sq_nonneg ((1 - t) * (1 / 2 - c) + t * (1 / 4)), sq_nonneg (t / 5), ht0, ht1]

theorem stadium_ne_half_weak {c δ ρ : ℝ} (hc : 1 - 1 / 100000 ≤ c) (hδ : δ ≤ (1 - c) / 2)
    (hρ : ρ ≤ 1 / 20) :
    ∀ z ∈ Work.C17.stadiumSet c δ ρ, z ≠ 1 / 2 := by
  intro z hz hz12
  obtain ⟨t, ht, hzball⟩ := hz
  rw [Set.mem_Icc] at ht
  obtain ⟨ht0, ht1⟩ := ht
  rw [hz12] at hzball
  rw [Metric.mem_ball, dist_eq_norm] at hzball
  -- the numerical core, with `t` the stadium parameter
  have hcore := stadium_core_weak hc ht0 ht1
  -- the real and imaginary parts of `1/2 - ((1-t)c + t·p₀)`
  have hre : ((1 / 2 : ℂ) - (((((1 - t) * c : ℝ)) : ℂ) + (t : ℂ) * Work.C17.p0C)).re
      = (1 - t) * (1 / 2 - c) + t * (1 / 4) := by
    simp [Work.C17.p0C]
    ring
  have him : ((1 / 2 : ℂ) - (((((1 - t) * c : ℝ)) : ℂ) + (t : ℂ) * Work.C17.p0C)).im
      = -(t / 5) := by
    simp [Work.C17.p0C]
    ring
  have hsq : ‖(1 / 2 : ℂ) - (((((1 - t) * c : ℝ)) : ℂ) + (t : ℂ) * Work.C17.p0C)‖ ^ 2
      = ((1 - t) * (1 / 2 - c) + t * (1 / 4)) ^ 2 + (t / 5) ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply, hre, him]
    ring
  -- so `1/2` is at distance at least `(1-t)/200000 + t/20` from the centre
  have hdle : (1 - t) / 200000 + t / 20
      ≤ ‖(1 / 2 : ℂ) - (((((1 - t) * c : ℝ)) : ℂ) + (t : ℂ) * Work.C17.p0C)‖ := by
    have hRnn : (0 : ℝ) ≤ (1 - t) / 200000 + t / 20 := by linarith
    have h2 : ((1 - t) / 200000 + t / 20) ^ 2
        ≤ ‖(1 / 2 : ℂ) - (((((1 - t) * c : ℝ)) : ℂ) + (t : ℂ) * Work.C17.p0C)‖ ^ 2 := by
      rw [hsq]
      exact hcore
    have h3 := sq_le_sq.mp h2
    simpa [abs_of_nonneg hRnn, abs_of_nonneg (norm_nonneg _)] using h3
  -- ... while the radius of the `t`-th disc is at most `(1-t)/200000 + t/20`
  have hrle : (1 - t) * δ + t * ρ ≤ (1 - t) / 200000 + t / 20 := by
    have h1c : (1 - c) / 2 ≤ 1 / 200000 := by linarith
    have h2 : (1 - t) * δ ≤ (1 - t) * ((1 - c) / 2) :=
      mul_le_mul_of_nonneg_left hδ (by linarith)
    have h3 : t * ρ ≤ t * (1 / 20) := mul_le_mul_of_nonneg_left hρ ht0
    have h4 : (1 - t) * ((1 - c) / 2) ≤ (1 - t) * (1 / 200000) :=
      mul_le_mul_of_nonneg_left h1c (by linarith)
    linarith
  linarith

end Work.C17I
