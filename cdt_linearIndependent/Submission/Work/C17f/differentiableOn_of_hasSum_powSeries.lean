import Mathlib

/-!
# Differentiability of a function given by a pointwise convergent power series

If `F z = ∑ₙ cₙ zⁿ` for every `z` with `‖z‖ < r` (in the sense of `HasSum`), then `F` is
differentiable on the open ball of radius `r` around `0`.

The proof uses that convergence of the series at a *single* point `s` of modulus `< r`
forces the radius of convergence of the associated formal multilinear series
`FormalMultilinearSeries.ofScalars ℂ c` to be at least `s`, since then
`‖cₙ‖ sⁿ = ‖cₙ sⁿ‖ → 0`. Hence around each point of the ball we have a genuine
power series expansion, making `F` analytic (and in particular differentiable) there.
-/

open scoped NNReal ENNReal Topology
open Filter

namespace Work.C17f

theorem differentiableOn_of_hasSum_powSeries {c : ℕ → ℂ} {r : ℝ} {F : ℂ → ℂ}
    (h : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n : ℕ => c n * z ^ n) (F z)) :
    DifferentiableOn ℂ F (Metric.ball 0 r) := by
  intro z hz
  rw [Metric.mem_ball, dist_zero_right] at hz
  -- Pick a radius `s` with `‖z‖ < s < r`; the series converges at the point `(s : ℂ)`.
  set s : ℝ := (‖z‖ + r) / 2 with hsdef
  have hzs : ‖z‖ < s := by rw [hsdef]; linarith [norm_nonneg z]
  have hsr : s < r := by rw [hsdef]; linarith [norm_nonneg z]
  have hs0 : 0 < s := by rw [hsdef]; linarith [norm_nonneg z]
  set q : ℝ≥0 := ⟨s, hs0.le⟩ with hqdef
  have hq : (q : ℝ) = s := rfl
  have hsz : ‖(s : ℂ)‖ = s := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hs0.le]
  have hsum : HasSum (fun n : ℕ => c n * (s : ℂ) ^ n) (F (s : ℂ)) :=
    h (s : ℂ) (by rw [hsz]; exact hsr)
  -- Convergence gives `‖cₙ‖ sⁿ = ‖cₙ sⁿ‖ → 0`, hence the radius of convergence is `≥ s`.
  have hlim : Tendsto (fun n : ℕ => ‖c n * (s : ℂ) ^ n‖) atTop (𝓝 (0 : ℝ)) := by
    have h0 := hsum.summable.tendsto_atTop_zero
    simpa using h0.norm
  have heq : (fun n : ℕ => ‖FormalMultilinearSeries.ofScalars ℂ c n‖ * (q : ℝ) ^ n)
      = (fun n : ℕ => ‖c n * (s : ℂ) ^ n‖) := by
    funext n
    rw [FormalMultilinearSeries.ofScalars_norm, hq, norm_mul, norm_pow, hsz]
  have hlim' : Tendsto (fun n : ℕ => ‖FormalMultilinearSeries.ofScalars ℂ c n‖ * (q : ℝ) ^ n)
      atTop (𝓝 (0 : ℝ)) := by
    rw [heq]; exact hlim
  have hrad : (q : ℝ≥0∞) ≤ (FormalMultilinearSeries.ofScalars ℂ c).radius :=
    FormalMultilinearSeries.le_radius_of_tendsto _ hlim'
  -- Assemble the power series expansion of `F` around `0` with radius `q`.
  have hp : HasFPowerSeriesOnBall F (FormalMultilinearSeries.ofScalars ℂ c) 0 (q : ℝ≥0∞) := by
    refine ⟨hrad, ?_, ?_⟩
    · exact_mod_cast hs0
    · intro y hy
      rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right] at hy
      have hyr : ‖y‖ < r := by rw [hq] at hy; exact lt_trans hy hsr
      have hh := h y hyr
      simpa [FormalMultilinearSeries.ofScalars_apply_eq, mul_comm] using hh
  have hmem : z ∈ Metric.eball (0 : ℂ) (q : ℝ≥0∞) := by
    rw [Metric.eball_coe, Metric.mem_ball, dist_zero_right]
    rw [hq]; exact hzs
  exact (hp.analyticAt_of_mem hmem).differentiableAt.differentiableWithinAt

end Work.C17f
