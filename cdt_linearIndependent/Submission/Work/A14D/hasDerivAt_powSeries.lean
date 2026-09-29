import Mathlib
import Submission.Work.A14D.powSeries_deriv

/-!
# Term-by-term differentiation of a power series convergent on a disc

Given a power series `∑ c n * z ^ n` that at every point of the open disc `‖z‖ < r` sums
to the value `F z` (hypothesis `h`), the function `F` is complex differentiable at every point
of the disc, with derivative the term-by-term derivative series
`∑ (n + 1) * c (n + 1) * z ^ n`.

The point is that convergence at a *single* radius `ρ` with `‖z‖ < ρ < r` bounds the
coefficients geometrically, which then lets the controlled-growth theorem
`Work.A14D.powSeries_deriv` (with growth exponent `k = 0`) be applied.  Since the disc of radius
`r` is a neighbourhood of `z`, the abstract power series agrees with `F` there, and
`HasDerivAt.congr_of_eventuallyEq` transfers the derivative.
-/

namespace Work.A14D

theorem hasDerivAt_powSeries (c : ℕ → ℂ) {r : ℝ} (hr : 0 < r) (F : ℂ → ℂ)
    (h : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => c n * z ^ n) (F z)) :
    ∀ z : ℂ, ‖z‖ < r →
      HasDerivAt F (∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * z ^ n) z := by
  intro z hz
  -- Choose an intermediate radius `ρ` with `‖z‖ < ρ < r`.
  set ρ : ℝ := (‖z‖ + r) / 2 with hρdef
  have hzρ : ‖z‖ < ρ := by rw [hρdef]; linarith [norm_nonneg z]
  have hρr : ρ < r := by rw [hρdef]; linarith [norm_nonneg z]
  have hρ0 : 0 < ρ := by rw [hρdef]; linarith [norm_nonneg z]
  have hρnorm : ‖(ρ : ℂ)‖ = ρ := by simp [abs_of_pos hρ0]
  -- Convergence at the point `ρ` (viewed as a complex number).
  have hρc : HasSum (fun n : ℕ => c n * (ρ : ℂ) ^ n) (F (ρ : ℂ)) := by
    refine h (ρ : ℂ) ?_
    rw [hρnorm]; exact hρr
  -- The terms are bounded, absolutely, by a single `M`.
  have hsumm : Summable (fun n : ℕ => c n * (ρ : ℂ) ^ n) := hρc.summable
  have habs : Summable (fun n : ℕ => ‖c n * (ρ : ℂ) ^ n‖) := hsumm.norm
  set M : ℝ := ∑' n : ℕ, ‖c n * (ρ : ℂ) ^ n‖ with hMdef
  have hM0 : 0 ≤ M := by rw [hMdef]; exact tsum_nonneg (fun n => norm_nonneg _)
  -- Geometric coefficient bound: `‖c n‖ ≤ M * (1/ρ)^n`.
  have hbound : ∀ n : ℕ, ‖c n‖ ≤ M * (1 / ρ) ^ n := by
    intro n
    have hn : ‖c n * (ρ : ℂ) ^ n‖ ≤ M := by
      rw [hMdef]; exact habs.le_tsum n (fun j _ => norm_nonneg _)
    rw [norm_mul, norm_pow, hρnorm] at hn
    have hρnp : 0 < ρ ^ n := pow_pos hρ0 n
    have h1 : M * (1 / ρ) ^ n = M / ρ ^ n := by rw [one_div_pow, mul_one_div]
    rw [h1, le_div_iff₀ hρnp]
    exact hn
  have hR0 : 0 < 1 / ρ := one_div_pos.mpr hρ0
  have hw : (1 / ρ) * ‖z‖ < 1 := by
    have he : (1 / ρ) * ‖z‖ = ‖z‖ / ρ := by field_simp
    rw [he, div_lt_one hρ0]; exact hzρ
  have ha : ∀ n : ℕ, ‖c n‖ ≤ M * (1 / ρ) ^ n * ((n : ℝ) + 1) ^ 0 := by
    intro n; simpa using hbound n
  -- Term-by-term differentiation of the abstract power series.
  have hmain : HasDerivAt (fun y : ℂ => ∑' n : ℕ, c n * y ^ n)
      (∑' n : ℕ, ((n : ℂ) + 1) * c (n + 1) * z ^ n) z :=
    powSeries_deriv c (C := M) (R := 1 / ρ) (k := 0) hM0 hR0 ha z hw
  -- On the disc of radius `r` (a neighbourhood of `z`), `F` is that power series.
  refine hmain.congr_of_eventuallyEq ?_
  have hzmem : z ∈ Metric.ball (0 : ℂ) r := by
    rw [Metric.mem_ball, dist_zero_right]; exact hz
  filter_upwards [Metric.isOpen_ball.mem_nhds hzmem] with y hy
  have hy' : ‖y‖ < r := by rwa [Metric.mem_ball, dist_zero_right] at hy
  exact ((h y hy').tsum_eq).symm

end Work.A14D
