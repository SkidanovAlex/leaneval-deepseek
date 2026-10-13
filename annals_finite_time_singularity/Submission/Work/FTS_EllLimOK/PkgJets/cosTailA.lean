import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

open MeasureTheory

namespace Work.FTS_EllLimOK.PkgJets

/-- First half of the `cos`-weight tail estimate: for `T ∈ (0, π/2)` the integral of
`cos(s)² · sin(2s)^η` over `[T, π/2]` is at most `2^η · (π/2 - T)^(3+η)` (with `η = 99/100`).
Route: on `[T, π/2]` put `u = π/2 - s`; then `cos s = sin u ≤ u` and `sin (2s) = sin (2u) ≤ 2u`,
so the integrand is `≤ 2^η (π/2-s)^(2+η) ≤ 2^η (π/2-T)^(2+η)`, and the interval has length
`π/2 - T`. -/
theorem cosTailA :
    ∀ T : ℝ, T ∈ Set.Ioo 0 (Real.pi / 2) →
      (∫ s in T..(Real.pi / 2), (Real.cos s) ^ 2 * (Real.sin (2 * s)) ^ (99 / 100 : ℝ))
        ≤ (2 : ℝ) ^ (99 / 100 : ℝ) * (Real.pi / 2 - T) ^ (3 + 99 / 100 : ℝ) := by
  intro T hT
  obtain ⟨hT0, hTlt⟩ := hT
  have hη : (0 : ℝ) ≤ 99 / 100 := by norm_num
  -- the two abbreviations: `L = π/2 - T` and the value of the uniform bound
  set L : ℝ := Real.pi / 2 - T with hL
  have hLpos : 0 < L := by rw [hL]; linarith
  have hLnn : 0 ≤ L := le_of_lt hLpos
  set C : ℝ := (2 : ℝ) ^ (99 / 100 : ℝ) * L ^ (2 + 99 / 100 : ℝ) with hC
  -- the pointwise bound on the (closed) interval of integration
  have hpt : ∀ s ∈ Set.Icc T (Real.pi / 2),
      (Real.cos s) ^ 2 * (Real.sin (2 * s)) ^ (99 / 100 : ℝ) ≤ C := by
    intro s hs
    have hs0 : 0 ≤ Real.pi / 2 - s := by linarith [hs.2]
    have hsL : Real.pi / 2 - s ≤ L := by rw [hL]; linarith [hs.1]
    -- `cos s = sin (π/2 - s) ≤ π/2 - s ≤ L`
    have hcos_eq : Real.cos s = Real.sin (Real.pi / 2 - s) :=
      (Real.sin_pi_div_two_sub s).symm
    have hcos_nn : 0 ≤ Real.cos s := by
      rw [hcos_eq]
      exact Real.sin_nonneg_of_mem_Icc ⟨hs0, by linarith [Real.pi_pos]⟩
    have hcos_le : Real.cos s ≤ L := by
      rw [hcos_eq]
      linarith [Real.sin_le hs0, hsL]
    have hcos2 : (Real.cos s) ^ 2 ≤ L ^ 2 := pow_le_pow_left₀ hcos_nn hcos_le 2
    -- `sin (2s) = sin (2 (π/2 - s)) ≤ 2 (π/2 - s) ≤ 2 L`
    have hsin_nn : 0 ≤ Real.sin (2 * s) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hs.1, hT0], by linarith [hs.2, Real.pi_pos]⟩
    have hsin_eq : Real.sin (2 * s) = Real.sin (2 * (Real.pi / 2 - s)) := by
      have h : Real.pi - 2 * (Real.pi / 2 - s) = 2 * s := by ring
      rw [← h]
      exact Real.sin_pi_sub _
    have hsin_le : Real.sin (2 * s) ≤ 2 * L := by
      rw [hsin_eq]
      have h2u : 0 ≤ 2 * (Real.pi / 2 - s) := by linarith
      linarith [Real.sin_le h2u, hsL]
    have hsin_pow : (Real.sin (2 * s)) ^ (99 / 100 : ℝ) ≤
        (2 : ℝ) ^ (99 / 100 : ℝ) * L ^ (99 / 100 : ℝ) := by
      have h1 : (Real.sin (2 * s)) ^ (99 / 100 : ℝ) ≤ (2 * L) ^ (99 / 100 : ℝ) :=
        Real.rpow_le_rpow hsin_nn hsin_le hη
      have h2 : (2 * L) ^ (99 / 100 : ℝ)
          = (2 : ℝ) ^ (99 / 100 : ℝ) * L ^ (99 / 100 : ℝ) :=
        Real.mul_rpow (by norm_num : (0 : ℝ) ≤ 2) hLnn
      rwa [h2] at h1
    calc (Real.cos s) ^ 2 * (Real.sin (2 * s)) ^ (99 / 100 : ℝ)
        ≤ L ^ 2 * ((2 : ℝ) ^ (99 / 100 : ℝ) * L ^ (99 / 100 : ℝ)) :=
          mul_le_mul hcos2 hsin_pow (Real.rpow_nonneg hsin_nn _) (sq_nonneg L)
      _ = C := by
          rw [hC]
          rw [show L ^ 2 * ((2 : ℝ) ^ (99 / 100 : ℝ) * L ^ (99 / 100 : ℝ))
                = (2 : ℝ) ^ (99 / 100 : ℝ) * (L ^ 2 * L ^ (99 / 100 : ℝ)) from by ring,
              ← Real.rpow_two L,
              ← Real.rpow_add hLpos (2 : ℝ) (99 / 100 : ℝ)]
  -- continuity (hence interval integrability) of the integrand and of the constant
  have hcont1 : Continuous (fun s : ℝ => (Real.cos s) ^ 2) := by
    have h := Real.continuous_cos.pow 2
    rw [show Real.cos ^ 2 = fun s : ℝ => Real.cos s ^ 2 from by funext s; rfl] at h
    exact h
  have hcont2 : Continuous (fun s : ℝ => (Real.sin (2 * s)) ^ (99 / 100 : ℝ)) :=
    (Real.continuous_sin.comp (continuous_const.mul continuous_id)).rpow_const
      (fun _ => Or.inr hη)
  have hcont : Continuous
      (fun s : ℝ => (Real.cos s) ^ 2 * (Real.sin (2 * s)) ^ (99 / 100 : ℝ)) :=
    hcont1.mul hcont2
  have hfint : IntervalIntegrable
      (fun s : ℝ => (Real.cos s) ^ 2 * (Real.sin (2 * s)) ^ (99 / 100 : ℝ))
      volume T (Real.pi / 2) := hcont.intervalIntegrable T (Real.pi / 2)
  have hCint : IntervalIntegrable (fun _ : ℝ => C) volume T (Real.pi / 2) :=
    intervalIntegrable_const
  have hmono := intervalIntegral.integral_mono_on (le_of_lt hTlt) hfint hCint hpt
  calc (∫ s in T..(Real.pi / 2),
          (Real.cos s) ^ 2 * (Real.sin (2 * s)) ^ (99 / 100 : ℝ))
      ≤ ∫ s in T..(Real.pi / 2), C := hmono
    _ = C * (Real.pi / 2 - T) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
        ring
    _ = (2 : ℝ) ^ (99 / 100 : ℝ) * L ^ (3 + 99 / 100 : ℝ) := by
        rw [hC, ← hL]
        rw [show (2 : ℝ) ^ (99 / 100 : ℝ) * L ^ (2 + 99 / 100 : ℝ) * L
              = (2 : ℝ) ^ (99 / 100 : ℝ) * (L ^ (2 + 99 / 100 : ℝ) * L) from by ring]
        rw [show L ^ (2 + 99 / 100 : ℝ) * L = L ^ (3 + 99 / 100 : ℝ) from by
          rw [← Real.rpow_add_one (ne_of_gt hLpos) (2 + 99 / 100 : ℝ)]
          rw [show (2 + 99 / 100 : ℝ) + 1 = 3 + 99 / 100 by norm_num]]
    _ = (2 : ℝ) ^ (99 / 100 : ℝ) * (Real.pi / 2 - T) ^ (3 + 99 / 100 : ℝ) := by
        rw [hL]

end Work.FTS_EllLimOK.PkgJets
