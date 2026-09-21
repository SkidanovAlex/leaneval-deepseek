import Mathlib
import Submission.Commons.Geometry.Ulam.body_of_revolution_cap_volume_half_of_interval

namespace Commons.Geometry.Ulam

open MeasureTheory Set Filter
open scoped Topology Interval ContDiff RealInnerProductSpace BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1000000

lemma odd_cap_centroid_moment_at_zero_general {n : ℕ} {f : ℝ → ℝ} {A B : ℝ} (hAB : A < B)
    (hf_nonneg : ∀ t ∈ Set.Icc A B, 0 ≤ f t) :
    (∫ t in A..B,
        ∫ z in (-f t)..0, t * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2))) =
      (1 / 2 : ℝ) * ∫ t in A..B,
        ∫ z in (-f t)..(f t), t * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)) := by
  let W : ℝ → ℝ → ℝ := fun t z => (f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)
  have hinner : ∀ t ∈ Set.Icc A B,
      (∫ z in (-f t)..0, t * W t z) =
        (1 / 2 : ℝ) * ∫ z in (-f t)..(f t), t * W t z := by
    intro t ht
    have hft_nonneg : 0 ≤ f t := hf_nonneg t ht
    have hg_cont : Continuous (fun z : ℝ => W t z) := by
      dsimp [W]
      continuity
    have hg_even : ∀ z : ℝ, W t (-z) = W t z := by
      intro z
      dsimp [W]
      have harg : f t ^ 2 - (-z) ^ 2 = f t ^ 2 - z ^ 2 := by ring
      rw [harg]
    have hhalf := (intervalIntegral_half_even hft_nonneg hg_cont hg_even).2
    calc
      (∫ z in (-f t)..0, t * W t z) = t * ∫ z in (-f t)..0, W t z := by
        rw [intervalIntegral.integral_const_mul]
      _ = t * ((1 / 2 : ℝ) * ∫ z in (-f t)..(f t), W t z) := by
        rw [hhalf]
        ring
      _ = (1 / 2 : ℝ) * (t * ∫ z in (-f t)..(f t), W t z) := by ring
      _ = (1 / 2 : ℝ) * ∫ z in (-f t)..(f t), t * W t z := by
        rw [intervalIntegral.integral_const_mul]
  have hcongr : (∫ t in A..B,
        ∫ z in (-f t)..0, t * W t z) =
      ∫ t in A..B, ((1 / 2 : ℝ) * ∫ z in (-f t)..(f t), t * W t z) := by
    apply intervalIntegral.integral_congr
    intro t ht
    have htIcc : t ∈ Set.Icc A B := by
      simpa [Set.uIcc_of_le hAB.le] using ht
    exact hinner t htIcc
  calc
    (∫ t in A..B, ∫ z in (-f t)..0, t * W t z)
        = ∫ t in A..B, ((1 / 2 : ℝ) * ∫ z in (-f t)..(f t), t * W t z) := hcongr
    _ = (1 / 2 : ℝ) * ∫ t in A..B, ∫ z in (-f t)..(f t), t * W t z := by
        rw [intervalIntegral.integral_const_mul]
    _ = (1 / 2 : ℝ) * ∫ t in A..B,
        ∫ z in (-f t)..(f t), t * ((f t ^ 2 - z ^ 2) ^ (n - 1) * Real.sqrt (f t ^ 2 - z ^ 2)) := by
        simp [W]

end Commons.Geometry.Ulam
