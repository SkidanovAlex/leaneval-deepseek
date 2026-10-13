import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.Mine

open MeasureTheory Set

/-- On `[0, π/2]` the function `θ ↦ sin(2θ)` takes values in `[0,1]`, hence
`sin(2θ)^a ≤ 1` for every exponent `a ≥ 0`; integrating the constant `1` over
the interval of length `π/2` gives the bound. -/
theorem setIntegral_sin_two_rpow_le {a : ℝ} (ha : 0 ≤ a) :
    (∫ θ in Set.Icc 0 (Real.pi / 2), Real.rpow (Real.sin (2 * θ)) a) ≤ Real.pi / 2 := by
  set s : Set ℝ := Set.Icc 0 (Real.pi / 2) with hs
  have hsmeas : MeasurableSet s := measurableSet_Icc
  -- `0 ≤ sin(2θ)` on the interval
  have hsin_nonneg : ∀ θ ∈ s, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_nonneg_of_mem_Icc
      ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  -- the integrand is nonnegative
  have hnonneg : 0 ≤ᵐ[volume.restrict s] (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) a) := by
    filter_upwards [ae_restrict_mem hsmeas] with θ hθ
    exact Real.rpow_nonneg (hsin_nonneg θ hθ) a
  -- the integrand is bounded by the constant `1`
  have hpoint : (fun θ : ℝ => Real.rpow (Real.sin (2 * θ)) a) ≤ᵐ[volume.restrict s]
      (fun _ : ℝ => (1 : ℝ)) := by
    filter_upwards [ae_restrict_mem hsmeas] with θ hθ
    exact Real.rpow_le_one (hsin_nonneg θ hθ) (Real.sin_le_one _) ha
  -- the constant `1` is integrable on the finite-measure interval
  have hone_int : Integrable (fun _ : ℝ => (1 : ℝ)) (volume.restrict s) := by
    rw [hs]
    exact integrableOn_const (μ := volume) (s := Set.Icc 0 (Real.pi / 2)) (C := (1 : ℝ))
      (by rw [Real.volume_Icc]; exact ENNReal.ofReal_ne_top)
  -- and its integral is the length of the interval
  have hval : (∫ θ in s, (1 : ℝ)) = Real.pi / 2 := by
    have hvol : (volume.real s) = Real.pi / 2 := by
      rw [hs, MeasureTheory.measureReal_def, Real.volume_Icc,
        ENNReal.toReal_ofReal (by linarith [Real.pi_pos])]
      ring
    rw [MeasureTheory.setIntegral_const, smul_eq_mul, mul_one, hvol]
  calc (∫ θ in Set.Icc 0 (Real.pi / 2), Real.rpow (Real.sin (2 * θ)) a)
      = ∫ θ in s, Real.rpow (Real.sin (2 * θ)) a := by rw [hs]
    _ ≤ ∫ θ in s, (1 : ℝ) := integral_mono_of_nonneg hnonneg hone_int hpoint
    _ = Real.pi / 2 := hval

end Work.FTS.EllipticEst.Mine
