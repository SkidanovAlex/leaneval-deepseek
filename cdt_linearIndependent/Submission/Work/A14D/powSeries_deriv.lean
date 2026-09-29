import Mathlib
import Submission.Work.A14D.summable_add_one_pow_mul_geometric
import Submission.Work.A14D.norm_derivTerm_le

/-!
# Term-by-term differentiation of a power series with controlled coefficient growth

If `‖a n‖ ≤ C * R ^ n * (n + 1) ^ k` for all `n`, then the power series `∑ a n * z ^ n`
converges on the disc `‖z‖ < 1 / R`, defines an analytic function there, and may be
differentiated term by term:

`(∑ a n * z ^ n)' = ∑ (n + 1) * a (n + 1) * z ^ n`.

The proof uses the uniform-convergence theorem for series of differentiable functions
(`hasDerivAt_tsum_of_isPreconnected`) on the ball of radius `ρ` with `‖w‖ < ρ` and `R * ρ < 1`.
The dominating summable sequences are provided by
`Work.A14D.summable_add_one_pow_mul_geometric`, the pointwise bound on the differentiated
terms by `Work.A14D.norm_derivTerm_le`.
-/

namespace Work.A14D

open scoped Topology
open Filter Metric

theorem powSeries_deriv (a : ℕ → ℂ) {C R : ℝ} {k : ℕ} (hC : 0 ≤ C) (hR : 0 < R)
    (ha : ∀ n : ℕ, ‖a n‖ ≤ C * R ^ n * ((n : ℝ) + 1) ^ k)
    (w : ℂ) (hw : R * ‖w‖ < 1) :
    HasDerivAt (fun z : ℂ => ∑' n : ℕ, a n * z ^ n)
      (∑' n : ℕ, ((n : ℂ) + 1) * a (n + 1) * w ^ n) w := by
  -- Choose a radius `ρ` with `‖w‖ < ρ` and `R * ρ < 1`: the series and its termwise
  -- derivative then converge uniformly on the ball of radius `ρ`.
  obtain ⟨ρ, hρw, hρ0, hRρ⟩ : ∃ ρ : ℝ, ‖w‖ < ρ ∧ 0 < ρ ∧ R * ρ < 1 := by
    refine ⟨(R⁻¹ + ‖w‖) / 2, ?_, ?_, ?_⟩
    · have hwlt : ‖w‖ < R⁻¹ := by
        rw [inv_eq_one_div, lt_div_iff₀ hR]; rwa [mul_comm]
      linarith
    · have hwlt : ‖w‖ < R⁻¹ := by
        rw [inv_eq_one_div, lt_div_iff₀ hR]; rwa [mul_comm]
      have : 0 < R⁻¹ := inv_pos.mpr hR
      linarith [norm_nonneg w]
    · have h1 : R * ((R⁻¹ + ‖w‖) / 2) = (1 + R * ‖w‖) / 2 := by
        rw [← mul_div_assoc, mul_add, mul_inv_cancel₀ (ne_of_gt hR)]
      rw [h1]; linarith
  have hs0 : (0 : ℝ) ≤ R * ρ := le_of_lt (mul_pos hR hρ0)
  have hs1 : R * ρ < 1 := hRρ
  -- Summability of the original series on the ball.
  have hsum_ball : ∀ z : ℂ, ‖z‖ < ρ → Summable (fun n : ℕ => a n * z ^ n) := by
    intro z hz
    refine Summable.of_norm_bounded
      (g := fun n : ℕ => C * (((n : ℝ) + 1) ^ k * (R * ρ) ^ n)) ?_ ?_
    · exact Summable.mul_left C (summable_add_one_pow_mul_geometric k hs0 hs1)
    · intro n
      have hzle : ‖z‖ ≤ ρ := le_of_lt hz
      have hzn : (0 : ℝ) ≤ ‖z‖ ^ n := pow_nonneg (norm_nonneg z) n
      have hA : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ k := by positivity
      calc ‖a n * z ^ n‖ = ‖a n‖ * ‖z‖ ^ n := by rw [norm_mul, norm_pow]
        _ ≤ (C * R ^ n * ((n : ℝ) + 1) ^ k) * ‖z‖ ^ n :=
              mul_le_mul_of_nonneg_right (ha n) hzn
        _ = C * (((n : ℝ) + 1) ^ k * (R * ‖z‖) ^ n) := by rw [mul_pow]; ring
        _ ≤ C * (((n : ℝ) + 1) ^ k * (R * ρ) ^ n) := by
              apply mul_le_mul_of_nonneg_left _ hC
              apply mul_le_mul_of_nonneg_left _ hA
              exact pow_le_pow_left₀ (mul_nonneg hR.le (norm_nonneg z))
                (mul_le_mul_of_nonneg_left hzle hR.le) n
  have hwmem : w ∈ Metric.ball (0 : ℂ) ρ := by
    rw [Metric.mem_ball, Complex.dist_eq, sub_zero]; exact hρw
  -- Convergence of the shifted series at the point `0`.
  have hg0 : Summable (fun n : ℕ => a (n + 1) * (0 : ℂ) ^ (n + 1)) := by
    have h : (fun n : ℕ => a (n + 1) * (0 : ℂ) ^ (n + 1)) = fun _ => 0 := by
      funext n
      rw [zero_pow (Nat.succ_ne_zero n), mul_zero]
    rw [h]; exact summable_zero
  -- Termwise derivative of `z ↦ a (n+1) * z ^ (n+1)`.
  have hderiv : ∀ n : ℕ, ∀ y ∈ Metric.ball (0 : ℂ) ρ,
      HasDerivAt (fun z : ℂ => a (n + 1) * z ^ (n + 1)) (((n : ℂ) + 1) * a (n + 1) * y ^ n) y := by
    intro n y _
    have h := (hasDerivAt_pow (n + 1) y).const_mul (a (n + 1))
    have h2 : a (n + 1) * (↑(n + 1) * y ^ (n + 1 - 1)) = (↑n + 1) * a (n + 1) * y ^ n := by
      rw [Nat.add_sub_cancel]; push_cast; ring
    rwa [h2] at h
  -- Summable majorant for the derivative.
  have hu : Summable (fun n : ℕ => C * R * 2 ^ k * (((n : ℝ) + 1) ^ (k + 1) * (R * ρ) ^ n)) :=
    Summable.mul_left (C * R * 2 ^ k)
      (summable_add_one_pow_mul_geometric (k + 1) hs0 hs1)
  -- Uniform bound for the termwise derivatives on the ball.
  have hbound : ∀ n : ℕ, ∀ y ∈ Metric.ball (0 : ℂ) ρ,
      ‖((n : ℂ) + 1) * a (n + 1) * y ^ n‖
        ≤ C * R * 2 ^ k * (((n : ℝ) + 1) ^ (k + 1) * (R * ρ) ^ n) := by
    intro n y hy
    have hy' : ‖y‖ ≤ ρ := le_of_lt (by simpa [Metric.mem_ball, Complex.dist_eq] using hy)
    exact norm_derivTerm_le a hC hR ha hρ0.le n hy'
  -- Uniform convergence on the ball gives term-by-term differentiation.
  have hmain : HasDerivAt (fun z : ℂ => ∑' (n : ℕ), a (n + 1) * z ^ (n + 1))
      (∑' (n : ℕ), ((n : ℂ) + 1) * a (n + 1) * w ^ n) w :=
    hasDerivAt_tsum_of_isPreconnected
      (u := fun n : ℕ => C * R * 2 ^ k * (((n : ℝ) + 1) ^ (k + 1) * (R * ρ) ^ n))
      hu Metric.isOpen_ball Metric.isPreconnected_ball hderiv hbound
      (Metric.mem_ball_self hρ0) hg0 hwmem
  -- Reassemble `∑ a n * z ^ n = a 0 + ∑ a (n+1) * z ^ (n+1)` near `w`.
  refine (hmain.const_add (a 0)).congr_of_eventuallyEq ?_
  filter_upwards [Metric.isOpen_ball.mem_nhds hwmem] with z hz
  have hz' : ‖z‖ < ρ := by simpa [Metric.mem_ball, Complex.dist_eq] using hz
  have hs := (hsum_ball z hz').tsum_eq_zero_add
  simpa using hs

end Work.A14D
