import Mathlib
import Submission.Work.FITop.Defs

namespace Work.FIArea7

/-- Real-arithmetic core of `Work.FIArea7.area7_small_theta`: the two side conditions
`θ²τX ≤ 1` and `τX² ≤ N` force `τ(θ²N + θ√N + 1) ≤ 3N/X` (with `τ ≥ 0`, `X ≥ 1`).
The constant `3` is sharp: `X = 1, θ = 1, τ = 1, N = 1` gives equality. -/
theorem smallTheta_tau_sum_bound {Pa : Work.FITop.Params} {X : ℕ}
    (hX : 1 ≤ X) (hτnn : 0 ≤ Pa.τ) (hθ : Pa.θ ^ 2 * Pa.τ * (X : ℝ) ≤ 1)
    (hτ : Pa.τ * (X : ℝ) ^ 2 ≤ Pa.N) :
    Pa.τ * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1) ≤ 3 * Pa.N / (X : ℝ) := by
  have hx1 : (1 : ℝ) ≤ (X : ℝ) := by exact_mod_cast hX
  have hxpos : (0 : ℝ) < (X : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  have hxnn : (0 : ℝ) ≤ (X : ℝ) := le_of_lt hxpos
  -- `N ≥ 0` is forced by `τ ≥ 0` and `τX² ≤ N`.
  have hn0 : 0 ≤ Pa.N := by
    have h := mul_nonneg hτnn (sq_nonneg (X : ℝ))
    linarith [hτ, h]
  have hx2le3 : (X : ℝ) ^ 2 ≤ (X : ℝ) ^ 3 := by
    have := pow_le_pow_right₀ hx1 (show 2 ≤ 3 by norm_num)
    simpa using this
  have hxle2 : (X : ℝ) ≤ (X : ℝ) ^ 2 := by
    have := pow_le_pow_right₀ hx1 (show 1 ≤ 2 by norm_num)
    simpa using this
  -- ### Bound on the `θ²N` term
  have hA : Pa.τ * (Pa.θ ^ 2 * Pa.N) ≤ Pa.N / (X : ℝ) := by
    rw [le_div_iff₀ hxpos]
    have hm := mul_le_mul_of_nonneg_right hθ hn0
    nlinarith [hm]
  -- ### Bound on the constant term
  have hC : Pa.τ ≤ Pa.N / (X : ℝ) := by
    rw [le_div_iff₀ hxpos]
    have h := mul_le_mul_of_nonneg_left hxle2 hτnn
    linarith [hτ, h]
  -- ### Bound on the `θ√N` term
  -- `(τθ)² X³ ≤ N` by multiplying the two hypotheses.
  have hv2 : (Pa.τ * Pa.θ) ^ 2 * (X : ℝ) ^ 3 ≤ Pa.N := by
    have hm := mul_le_mul hθ hτ (mul_nonneg hτnn (sq_nonneg (X : ℝ))) (by norm_num : (0 : ℝ) ≤ 1)
    nlinarith [hm]
  have hsquares : (|Pa.τ * Pa.θ| * Real.sqrt Pa.N * (X : ℝ)) ^ 2 ≤ Pa.N ^ 2 := by
    have h1 : (Pa.τ * Pa.θ) ^ 2 * Pa.N * (X : ℝ) ^ 2 ≤ (Pa.τ * Pa.θ) ^ 2 * Pa.N * (X : ℝ) ^ 3 :=
      mul_le_mul_of_nonneg_left hx2le3 (mul_nonneg (sq_nonneg _) hn0)
    have h2 : (Pa.τ * Pa.θ) ^ 2 * Pa.N * (X : ℝ) ^ 3 ≤ Pa.N ^ 2 := by
      have := mul_le_mul_of_nonneg_right hv2 hn0
      nlinarith [this]
    have key : (|Pa.τ * Pa.θ| * Real.sqrt Pa.N * (X : ℝ)) ^ 2
        = (Pa.τ * Pa.θ) ^ 2 * Pa.N * (X : ℝ) ^ 2 := by
      rw [mul_pow, mul_pow, sq_abs, Real.sq_sqrt hn0]
    rw [key]
    linarith [h1, h2]
  have hB' : |Pa.τ * Pa.θ| * Real.sqrt Pa.N * (X : ℝ) ≤ Pa.N := by
    have hnn : 0 ≤ |Pa.τ * Pa.θ| * Real.sqrt Pa.N * (X : ℝ) :=
      mul_nonneg (mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)) hxnn
    have h := sq_le_sq.mp hsquares
    rwa [abs_of_nonneg hnn, abs_of_nonneg hn0] at h
  have hB : Pa.τ * Pa.θ * Real.sqrt Pa.N * (X : ℝ) ≤ Pa.N := by
    have hsp : 0 ≤ Real.sqrt Pa.N * (X : ℝ) := mul_nonneg (Real.sqrt_nonneg _) hxnn
    calc Pa.τ * Pa.θ * Real.sqrt Pa.N * (X : ℝ)
        = (Pa.τ * Pa.θ) * (Real.sqrt Pa.N * (X : ℝ)) := by ring
      _ ≤ |Pa.τ * Pa.θ| * (Real.sqrt Pa.N * (X : ℝ)) :=
            mul_le_mul_of_nonneg_right (le_abs_self _) hsp
      _ = |Pa.τ * Pa.θ| * Real.sqrt Pa.N * (X : ℝ) := by ring
      _ ≤ Pa.N := hB'
  have hBd : Pa.τ * (Pa.θ * Real.sqrt Pa.N) ≤ Pa.N / (X : ℝ) := by
    rw [le_div_iff₀ hxpos]
    nlinarith [hB]
  -- ### Assembly
  have hdecomp : Pa.τ * (Pa.θ ^ 2 * Pa.N + Pa.θ * Real.sqrt Pa.N + 1)
      = Pa.τ * (Pa.θ ^ 2 * Pa.N) + Pa.τ * (Pa.θ * Real.sqrt Pa.N) + Pa.τ * 1 := by ring
  rw [hdecomp]
  have h3 : 3 * Pa.N / (X : ℝ) = Pa.N / (X : ℝ) + Pa.N / (X : ℝ) + Pa.N / (X : ℝ) := by ring
  linarith [hA, hBd, hC, h3]

end Work.FIArea7
