import Mathlib

namespace Work.Mostow.gapA

open MeasureTheory

theorem lintegralCoshSinhc (R : ℝ) (hR : 0 ≤ R) :
    ∫⁻ x in Set.Ioo (0 : ℝ) R,
        ENNReal.ofReal x * ENNReal.ofReal (Real.cosh x * (Real.sinh x / x))
      = ENNReal.ofReal (Real.sinh R ^ 2 / 2) := by
  -- On `(0, R)` the integrand simplifies to `ENNReal.ofReal (cosh x * sinh x)`.
  have hcongr : ∫⁻ x in Set.Ioo (0 : ℝ) R,
        ENNReal.ofReal x * ENNReal.ofReal (Real.cosh x * (Real.sinh x / x))
      = ∫⁻ x in Set.Ioo (0 : ℝ) R, ENNReal.ofReal (Real.cosh x * Real.sinh x) := by
    apply setLIntegral_congr_fun measurableSet_Ioo
    intro x hx
    show ENNReal.ofReal x * ENNReal.ofReal (Real.cosh x * (Real.sinh x / x))
        = ENNReal.ofReal (Real.cosh x * Real.sinh x)
    have hx0 : 0 < x := hx.1
    have hxs : x * (Real.cosh x * (Real.sinh x / x)) = Real.cosh x * Real.sinh x := by
      field_simp
    rw [← ENNReal.ofReal_mul hx0.le, hxs]
  rw [hcongr]
  -- Pass from the lintegral of `ofReal g` to `ofReal` of the integral of `g`.
  have hint : IntegrableOn (fun x => Real.cosh x * Real.sinh x) (Set.Ioo (0 : ℝ) R) := by
    have hcomp : IntegrableOn (fun x => Real.cosh x * Real.sinh x) (Set.Icc (0 : ℝ) R) :=
      ContinuousOn.integrableOn_compact (K := Set.Icc (0 : ℝ) R) isCompact_Icc
        (Real.continuous_cosh.mul Real.continuous_sinh).continuousOn
    exact hcomp.mono_set (fun x hx => ⟨le_of_lt hx.1, hx.2.le⟩)
  have hnn : 0 ≤ᵐ[volume.restrict (Set.Ioo (0 : ℝ) R)]
      (fun x => Real.cosh x * Real.sinh x) := by
    exact (ae_restrict_iff' measurableSet_Ioo).2
      (ae_of_all _ (fun x hx =>
        mul_nonneg (Real.cosh_pos x).le (Real.sinh_nonneg_iff.mpr hx.1.le)))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn]
  congr 1
  -- Reduce to the interval integral `∫ x in 0..R, cosh x * sinh x`.
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hR]
  have hderiv : ∀ x ∈ Set.uIcc (0 : ℝ) R,
      HasDerivAt (fun y => Real.sinh y ^ 2 / 2) (Real.cosh x * Real.sinh x) x := by
    intro x hx
    have h1 : HasDerivAt (fun y : ℝ => Real.sinh y ^ 2) (2 * Real.sinh x * Real.cosh x) x := by
      have hb : HasDerivAt (Real.sinh ^ 2) (2 * Real.sinh x * Real.cosh x) x := by
        simpa using (Real.hasDerivAt_sinh x).pow 2
      have hf : (Real.sinh ^ 2 : ℝ → ℝ) = fun y => Real.sinh y ^ 2 := by
        funext y; rw [Pi.pow_apply]
      rwa [hf] at hb
    have h2 : HasDerivAt (fun y => Real.sinh y ^ 2 / 2)
        ((2 * Real.sinh x * Real.cosh x) / 2) x := h1.div_const 2
    have he : (2 * Real.sinh x * Real.cosh x) / 2 = Real.cosh x * Real.sinh x := by ring
    rwa [he] at h2
  have hint2 : IntervalIntegrable (fun x => Real.cosh x * Real.sinh x) volume 0 R :=
    (Real.continuous_cosh.mul Real.continuous_sinh).intervalIntegrable 0 R
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint2]
  simp [Real.sinh_zero]

end Work.Mostow.gapA
