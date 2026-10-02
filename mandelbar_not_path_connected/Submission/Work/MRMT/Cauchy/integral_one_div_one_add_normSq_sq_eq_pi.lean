import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.MRMT.Cauchy

open MeasureTheory Filter
open scoped Topology

/-- The `1`-dimensional Beta-type integral `∫_0^∞ y/(1+y²)² dy = 1/2`, obtained from the
fundamental theorem of calculus applied to the antiderivative `y ↦ -(1/2)/(1+y²)`. -/
private theorem integral_Ioi_mul_one_div_one_add_sq_sq :
    ∫ y in Set.Ioi (0 : ℝ), y * (1 / (1 + y ^ 2) ^ 2) = 1 / 2 := by
  have hd : ∀ x ∈ Set.Ici (0 : ℝ),
      HasDerivAt (fun y : ℝ => -(1 / 2) * (1 + y ^ 2)⁻¹) (x * (1 / (1 + x ^ 2) ^ 2)) x := by
    intro x _
    have h : HasDerivAt (fun y : ℝ => 1 + y ^ 2) (2 * x) x := by
      simpa using (hasDerivAt_pow 2 x).const_add 1
    have h2 : HasDerivAt (fun y : ℝ => (1 + y ^ 2)⁻¹) (-(2 * x) / (1 + x ^ 2) ^ 2) x :=
      h.inv (by positivity)
    have h3 : HasDerivAt (fun y : ℝ => -(1 / 2) * (1 + y ^ 2)⁻¹)
        (-(1 / 2) * (-(2 * x) / (1 + x ^ 2) ^ 2)) x :=
      h2.const_mul (-(1 / 2))
    convert h3 using 1
    field_simp
  have hpos : ∀ x ∈ Set.Ioi (0 : ℝ), 0 ≤ x * (1 / (1 + x ^ 2) ^ 2) := by
    intro x hx
    exact mul_nonneg (le_of_lt hx) (by positivity)
  have hu : Tendsto (fun y : ℝ => 1 + y ^ 2) atTop atTop := by
    apply tendsto_atTop_mono (f := fun y : ℝ => y) (g := fun y : ℝ => 1 + y ^ 2)
    · intro y; nlinarith [sq_nonneg (y - 1 / 2)]
    · exact tendsto_id
  have h1 : Tendsto (fun y : ℝ => (1 + y ^ 2)⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hu
  have htend : Tendsto (fun y : ℝ => -(1 / 2) * (1 + y ^ 2)⁻¹) atTop (𝓝 0) := by
    have := h1.const_mul (-(1 / 2))
    simpa using this
  have := integral_Ioi_of_hasDerivAt_of_nonneg' (a := 0) (l := 0)
    (g := fun y : ℝ => -(1 / 2) * (1 + y ^ 2)⁻¹)
    (g' := fun x => x * (1 / (1 + x ^ 2) ^ 2)) hd hpos htend
  simpa using this

/-- The real-valued plane integral `∫_ℂ (1 + ‖z‖²)⁻² dz = π`, via the polar-coordinate
(radial) formula for an additive Haar measure and the `1`-dimensional computation above. -/
private theorem integral_one_div_one_add_normSq_sq :
    (∫ z : ℂ, (1 / (1 + ‖z‖ ^ 2) ^ 2 : ℝ)) = Real.pi := by
  have hball : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
    rw [Measure.real, Complex.volume_ball]
    norm_num
  have hint : (∫ y in Set.Ioi (0 : ℝ),
      y ^ (Module.finrank ℝ ℂ - 1) • (1 / (1 + y ^ 2) ^ 2 : ℝ)) = 1 / 2 := by
    have : (fun y : ℝ => y ^ (Module.finrank ℝ ℂ - 1) • (1 / (1 + y ^ 2) ^ 2 : ℝ)) =
        fun y : ℝ => y * (1 / (1 + y ^ 2) ^ 2) := by
      funext y
      rw [Complex.finrank_real_complex]
      norm_num
    rw [this, integral_Ioi_mul_one_div_one_add_sq_sq]
  have h := MeasureTheory.integral_fun_norm_addHaar (μ := (volume : Measure ℂ))
      (f := fun t : ℝ => (1 / (1 + t ^ 2) ^ 2 : ℝ))
  rw [h, hball, hint]
  rw [Complex.finrank_real_complex]
  rw [nsmul_eq_mul, smul_eq_mul]
  ring

theorem integral_one_div_one_add_normSq_sq_eq_pi :
    ∫ z : ℂ, ((1 / (1 + ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ) = (Real.pi : ℂ) := by
  have hconv : (∫ z : ℂ, ((1 / (1 + ‖z‖ ^ 2) ^ 2 : ℝ) : ℂ)) =
      ↑(∫ z : ℂ, (1 / (1 + ‖z‖ ^ 2) ^ 2 : ℝ)) := integral_ofReal
  rw [hconv, integral_one_div_one_add_normSq_sq]

end Work.MRMT.Cauchy
