import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.GalBasis.cc

/-- Refined layer estimate. `sin(2θ) ≥ (4/π)θ` on `[0, π/4]` together with the exact integral
`∫_t^{2t} θ^{-γ} = t^{1-γ}(2^{1-γ}-1)/(1-γ)` gives the stated bound. -/
theorem layer_pow_int_lt_one {γ t : ℝ} (hγ0 : 0 ≤ γ) (ht : 0 < t) (ht2 : 2 * t ≤ Real.pi / 4)
    (hγ : γ < 1) :
    ∫ θ in t..(2 * t), (Real.sin (2 * θ)) ^ (-γ)
      ≤ (Real.pi / 4) ^ γ * (t ^ (1 - γ) * (2 ^ (1 - γ) - 1) / (1 - γ)) := by
  have ht0 : t ≤ 2 * t := by linarith
  -- Pointwise bound on the interval: `sin(2θ)^{-γ} ≤ (π/4)^γ θ^{-γ}`.
  have hpt : ∀ θ ∈ Set.Icc t (2 * t),
      (Real.sin (2 * θ)) ^ (-γ) ≤ (Real.pi / 4) ^ γ * θ ^ (-γ) := by
    intro θ hθ
    have hθpos : 0 < θ := lt_of_lt_of_le ht hθ.1
    have hmul : 2 / Real.pi * (2 * θ) ≤ Real.sin (2 * θ) :=
      Real.mul_le_sin (by linarith) (by linarith [hθ.2, ht2, Real.pi_pos])
    have hle : 4 * θ / Real.pi ≤ Real.sin (2 * θ) := by
      have : 4 * θ / Real.pi = 2 / Real.pi * (2 * θ) := by ring
      rw [this]; exact hmul
    have hpos : 0 < 4 * θ / Real.pi := by positivity
    have h1 := Real.rpow_le_rpow_of_nonpos hpos hle (neg_nonpos.mpr hγ0)
    have h2 : 4 * θ / Real.pi = (Real.pi / 4)⁻¹ * θ := by
      rw [inv_div]; ring
    rw [h2, Real.mul_rpow (inv_nonneg.mpr (by positivity)) hθpos.le, Real.inv_rpow (by positivity),
      ← Real.rpow_neg (by positivity : (0:ℝ) ≤ Real.pi / 4), neg_neg] at h1
    exact h1
  have hint1 : IntervalIntegrable (fun θ : ℝ => (Real.sin (2 * θ)) ^ (-γ))
      MeasureTheory.volume t (2 * t) := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.rpow_const ?_ ?_
    · exact (Real.continuous_sin.comp (continuous_const.mul continuous_id)).continuousOn
    · intro θ hθ
      left
      rw [Set.uIcc_of_le ht0] at hθ
      refine ne_of_gt (Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1])
        (by linarith [hθ.2, ht2, Real.pi_pos]))
  have hint2 : IntervalIntegrable (fun θ : ℝ => (Real.pi / 4) ^ γ * θ ^ (-γ))
      MeasureTheory.volume t (2 * t) := by
    apply ContinuousOn.intervalIntegrable
    refine ContinuousOn.mul continuousOn_const ?_
    refine ContinuousOn.rpow_const continuousOn_id ?_
    intro θ hθ
    left
    rw [Set.uIcc_of_le ht0] at hθ
    exact ne_of_gt (lt_of_lt_of_le ht hθ.1)
  have hmono := intervalIntegral.integral_mono_on ht0 hint1 hint2 hpt
  have hInt : ∫ θ in t..(2 * t), θ ^ (-γ) =
      t ^ (1 - γ) * (2 ^ (1 - γ) - 1) / (1 - γ) := by
    have hr : -γ ≠ -1 := by linarith
    have hz : (0:ℝ) ∉ Set.uIcc t (2 * t) := by
      rw [Set.uIcc_of_le ht0]
      intro h; linarith [h.1]
    rw [integral_rpow (Or.inr ⟨hr, hz⟩)]
    rw [show -γ + 1 = 1 - γ by ring]
    rw [Real.mul_rpow (by norm_num : (0:ℝ) ≤ 2) ht.le]
    ring
  calc ∫ θ in t..(2 * t), (Real.sin (2 * θ)) ^ (-γ)
      ≤ ∫ θ in t..(2 * t), (Real.pi / 4) ^ γ * θ ^ (-γ) := hmono
    _ = (Real.pi / 4) ^ γ * ∫ θ in t..(2 * t), θ ^ (-γ) := by
        rw [intervalIntegral.integral_const_mul]
    _ = (Real.pi / 4) ^ γ * (t ^ (1 - γ) * (2 ^ (1 - γ) - 1) / (1 - γ)) := by rw [hInt]

end Work.FTS.GalBasis.cc
