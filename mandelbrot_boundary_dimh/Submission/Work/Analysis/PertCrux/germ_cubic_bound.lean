import Mathlib
import Submission.Work.Interfaces.Parabolic

namespace Work.Analysis.PertCrux

open Filter

/-- A complex-differentiable function on an open set is analytic, so a parabolic germ
`f₀ = z + z² + O(z³)` admits a third-order Taylor expansion with a remainder that is
analytic (hence bounded) near `0`. -/
theorem germ_cubic_bound {f₀ : ℂ → ℂ} {D₀ : Set ℂ} (hd : MandelDim.IsParabolicGerm f₀ D₀) :
    ∃ C : ℝ, 0 ≤ C ∧ ∃ r : ℝ, 0 < r ∧
      ∀ z : ℂ, ‖z‖ ≤ r → ‖f₀ z - z - z ^ 2‖ ≤ C * ‖z‖ ^ 3 := by
  obtain ⟨hDopen, h0D, hdiff, hf0, hd1, hd2⟩ := hd
  -- `f₀` is complex differentiable on the neighbourhood `D₀` of `0`, hence analytic at `0`.
  have hana : AnalyticAt ℂ f₀ 0 := hdiff.analyticAt (hDopen.mem_nhds h0D)
  -- Third-order Taylor expansion: `f₀ z = f₀ 0 + z f₀'(0) + (z²/2) f₀''(0) + z³ F z`
  -- with `F` analytic at `0`.
  obtain ⟨F, hFa, hF⟩ := hana.exists_eq_sum_add_pow_mul 3
  -- The normalising conditions `f₀ 0 = 0`, `f₀'(0) = 1`, `f₀''(0) = 2` turn the polynomial
  -- part into `z + z²`.
  have hF3 : ∀ z : ℂ, f₀ z - z - z ^ 2 = z ^ 3 * F z := by
    intro z
    have h := hF z
    have hsum : (∑ i ∈ Finset.range 3, (z ^ i / (i.factorial : ℂ)) • iteratedDeriv i f₀ 0)
        = z + z ^ 2 := by
      simp [Finset.sum_range_succ, iteratedDeriv_zero, iteratedDeriv_succ', hf0, hd1, hd2]
    rw [hsum] at h
    rw [h]
    ring
  -- `F` is continuous at `0`, so it is bounded by `‖F 0‖ + 1` near `0`.
  obtain ⟨δ, hδ0, hδ⟩ := (Metric.continuousAt_iff.mp hFa.continuousAt) 1 zero_lt_one
  refine ⟨‖F 0‖ + 1, by positivity, δ / 2, by positivity, fun z hz => ?_⟩
  have hzd : dist z 0 < δ := by rw [dist_eq_norm, sub_zero]; linarith
  have hFz : ‖F z‖ ≤ ‖F 0‖ + 1 := by
    have h1 : ‖F z - F 0‖ < 1 := by have := hδ hzd; rwa [dist_eq_norm] at this
    calc ‖F z‖ = ‖(F z - F 0) + F 0‖ := by rw [sub_add_cancel]
      _ ≤ ‖F z - F 0‖ + ‖F 0‖ := norm_add_le _ _
      _ ≤ ‖F 0‖ + 1 := by linarith
  rw [hF3 z, norm_mul, norm_pow]
  calc ‖z‖ ^ 3 * ‖F z‖ ≤ ‖z‖ ^ 3 * (‖F 0‖ + 1) :=
        mul_le_mul_of_nonneg_left hFz (by positivity)
    _ = (‖F 0‖ + 1) * ‖z‖ ^ 3 := by ring

end Work.Analysis.PertCrux
