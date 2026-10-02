import Mathlib
import Submission.Work.MRMT.Found.ball_integral_polar
import Submission.Work.MRMT.Found.exists_sq_mul_le_integral

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory Real Set intervalIntegral

namespace Work.MRMT.Found

/-- The angular integral of `f` over `(-π, π)` on the circle of radius `ρ` equals `2π` times the
integral of the `(0, 1)`-parametrisation `t ↦ f (ρ * exp (2 π t I))`.

This is the substitution `θ = 2π t` together with the `2π`-periodicity of `θ ↦ f (ρ e^{iθ})`. -/
theorem int_angle_eq (f : ℂ → ℝ) (ρ : ℝ) :
    (∫ θ in (-Real.pi)..Real.pi, f (ρ * Complex.exp (θ * Complex.I)))
      = 2 * Real.pi * ∫ t in (0:ℝ)..1, f (ρ * Complex.exp (2 * Real.pi * t * Complex.I)) := by
  set F : ℝ → ℝ := fun θ => f (ρ * Complex.exp (θ * Complex.I)) with hF
  have hc : (2 * Real.pi) ≠ 0 := by positivity
  have hper : Function.Periodic F (2 * Real.pi) := by
    intro x
    simp only [hF]
    have e1 : (↑(x + 2*Real.pi) : ℂ) * Complex.I
        = ↑x * Complex.I + (↑(2*Real.pi) : ℂ) * Complex.I := by
      push_cast; ring
    have e2 : Complex.exp ((↑(2*Real.pi) : ℂ) * Complex.I) = 1 := by
      rw [show (↑(2*Real.pi) : ℂ) * Complex.I = 2 * ↑Real.pi * Complex.I by push_cast; ring]
      exact Complex.exp_two_pi_mul_I
    rw [e1, Complex.exp_add, e2, mul_one]
  have hA : ∫ θ in (-Real.pi)..Real.pi, F θ = ∫ θ in (0:ℝ)..2*Real.pi, F θ := by
    have h := hper.intervalIntegral_add_eq (-Real.pi) (0:ℝ)
    rw [show (-Real.pi) + 2*Real.pi = Real.pi by ring, zero_add] at h
    exact h
  have hB : ∫ θ in (0:ℝ)..2*Real.pi, F θ = 2*Real.pi * ∫ t in (0:ℝ)..1, F (2*Real.pi * t) := by
    have h := intervalIntegral.integral_comp_mul_left (a := (0:ℝ)) (b := (1:ℝ)) F hc
    rw [h]
    simp only [mul_zero, mul_one, smul_eq_mul]
    rw [mul_inv_cancel_left₀ hc]
  have hC : ∫ t in (0:ℝ)..1, F (2*Real.pi * t)
      = ∫ t in (0:ℝ)..1, f (ρ * Complex.exp (2 * Real.pi * t * Complex.I)) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [hF]
    have : (↑(2*Real.pi*t) : ℂ) * Complex.I = 2 * (↑Real.pi) * (↑t) * Complex.I := by
      push_cast; ring
    rw [this]
  rw [hA, hB, hC]

/-- The area integral of `f` over `Metric.ball 0 R` expressed through the `(0,1)` angle
parametrisation `t ↦ f (ρ * exp (2 π t I))`. -/
theorem ball_integral_two_pi (f : ℂ → ℝ) (hf : Continuous f) {R : ℝ} (hR : 0 ≤ R) :
    (∫ z in Metric.ball (0 : ℂ) R, f z)
      = 2 * Real.pi * ∫ ρ in (0 : ℝ)..R,
          ρ * (∫ t in (0 : ℝ)..1, f (ρ * Complex.exp (2 * Real.pi * t * Complex.I))) := by
  rw [ball_integral_polar hf hR]
  have h1 : (∫ ρ in (0:ℝ)..R, ρ * (∫ θ in (-Real.pi)..Real.pi,
              f (ρ * Complex.exp (θ * Complex.I))))
      = ∫ ρ in (0:ℝ)..R, ρ * (2 * Real.pi * (∫ t in (0:ℝ)..1,
              f (ρ * Complex.exp (2 * Real.pi * t * Complex.I)))) := by
    apply intervalIntegral.integral_congr
    intro ρ _
    beta_reduce
    rw [int_angle_eq f ρ]
  rw [h1]
  have h2 : (∫ ρ in (0:ℝ)..R, ρ * (2 * Real.pi * (∫ t in (0:ℝ)..1,
              f (ρ * Complex.exp (2 * Real.pi * t * Complex.I)))))
      = 2 * Real.pi * ∫ ρ in (0:ℝ)..R, ρ * (∫ t in (0:ℝ)..1,
              f (ρ * Complex.exp (2 * Real.pi * t * Complex.I))) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro ρ _
    beta_reduce
    ring
  rw [h2]

theorem exists_radius_sq_shell_le {f : ℂ → ℝ} (hf : Continuous f) (hf0 : ∀ z : ℂ, 0 ≤ f z)
    {a R : ℝ} (ha : 0 < a) (haR : a < R) :
    ∃ r ∈ Set.Ioo a R,
      Real.log (R / a) * (r ^ 2 * (∫ t in (0 : ℝ)..1, f (r * Complex.exp (2 * Real.pi * t * Complex.I))))
        ≤ (1 / (2 * Real.pi)) * (∫ z in Metric.ball (0 : ℂ) R, f z) := by
  have hR : 0 < R := lt_trans ha haR
  have hQcont : Continuous (fun ρ : ℝ =>
      ∫ t in (0:ℝ)..1, f (ρ * Complex.exp (2 * Real.pi * t * Complex.I))) := by
    apply intervalIntegral.continuous_parametric_intervalIntegral_of_continuous'
      (f := fun (ρ : ℝ) (t : ℝ) => f (ρ * Complex.exp (2 * Real.pi * t * Complex.I)))
    show Continuous (fun p : ℝ × ℝ => f (p.1 * Complex.exp (2 * Real.pi * p.2 * Complex.I)))
    exact hf.comp (by fun_prop)
  have hQnonneg : ∀ ρ : ℝ,
      0 ≤ ∫ t in (0:ℝ)..1, f (ρ * Complex.exp (2 * Real.pi * t * Complex.I)) := by
    intro ρ
    apply intervalIntegral.integral_nonneg zero_le_one
    intro t _
    exact hf0 _
  obtain ⟨r, hr, hle⟩ := exists_sq_mul_le_integral hQcont ha haR
  refine ⟨r, hr, ?_⟩
  have hcomm : Real.log (R / a)
      * (r ^ 2 * (∫ t in (0:ℝ)..1, f (r * Complex.exp (2 * Real.pi * t * Complex.I))))
      = r ^ 2 * (∫ t in (0:ℝ)..1, f (r * Complex.exp (2 * Real.pi * t * Complex.I)))
        * Real.log (R / a) := by ring
  rw [hcomm]
  have hDB : (∫ x in (a:ℝ)..R, x * (∫ t in (0:ℝ)..1,
                f (x * Complex.exp (2 * Real.pi * t * Complex.I))))
      ≤ (∫ x in (0:ℝ)..R, x * (∫ t in (0:ℝ)..1,
                f (x * Complex.exp (2 * Real.pi * t * Complex.I)))) := by
    have hint1 : IntervalIntegrable (fun x : ℝ => x * (∫ t in (0:ℝ)..1,
        f (x * Complex.exp (2 * Real.pi * t * Complex.I)))) volume (0:ℝ) a :=
      (continuous_id.mul hQcont).intervalIntegrable 0 a
    have hint2 : IntervalIntegrable (fun x : ℝ => x * (∫ t in (0:ℝ)..1,
        f (x * Complex.exp (2 * Real.pi * t * Complex.I)))) volume a R :=
      (continuous_id.mul hQcont).intervalIntegrable a R
    have hsplit := intervalIntegral.integral_add_adjacent_intervals hint1 hint2
    have hnn : 0 ≤ ∫ x in (0:ℝ)..a, x * (∫ t in (0:ℝ)..1,
        f (x * Complex.exp (2 * Real.pi * t * Complex.I))) := by
      apply intervalIntegral.integral_nonneg ha.le
      intro x hx
      exact mul_nonneg hx.1 (hQnonneg x)
    linarith
  have hball := ball_integral_two_pi f hf hR.le
  rw [hball]
  rw [one_div, ← mul_assoc, inv_mul_cancel₀ (show (2 * Real.pi) ≠ 0 by positivity), one_mul]
  exact le_trans hle hDB

end Work.MRMT.Found
