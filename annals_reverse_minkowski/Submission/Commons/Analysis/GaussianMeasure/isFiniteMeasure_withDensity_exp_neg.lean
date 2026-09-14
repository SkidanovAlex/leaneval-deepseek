import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.InnerProductSpace.Calculus
import Submission.Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm

noncomputable section

namespace Commons.Analysis.GaussianMeasure

open MeasureTheory Real

/-- A convex function on a real normed space lies above its tangent line at any point where it is
differentiable: `g 0 + g'(0)(x) ≤ g x`.  This is the subgradient inequality for convex functions,
obtained by applying the one-dimensional secant bound to `t ↦ g (t • x)`. -/
theorem convexOn_le_fderiv {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {g : E → ℝ} (hg : ConvexOn ℝ Set.univ g) {L : E →L[ℝ] ℝ}
    (hL : HasFDerivAt g L 0) (x : E) : g 0 + L x ≤ g x := by
  set φ : ℝ → ℝ := fun t => g (t • x) with hφ
  have hφc : ConvexOn ℝ Set.univ φ := by
    have h := hg.comp_linearMap (LinearMap.toSpanSingleton ℝ E x)
    simpa [φ, Set.preimage_univ, Function.comp_def] using h
  have hcurve : HasDerivAt (fun t : ℝ => t • x) x 0 := by
    simpa using (hasDerivAt_id (0 : ℝ)).smul_const x
  have hL' : HasFDerivAt g L ((fun t : ℝ => t • x) 0) := by simpa using hL
  have hφd : HasDerivAt φ (L x) 0 := by
    have h := HasFDerivAt.comp_hasDerivAt (x := (0 : ℝ)) hL' hcurve
    simpa [φ, Function.comp_def] using h
  have hle := hφc.deriv_le_slope (Set.mem_univ 0) (Set.mem_univ 1) (by norm_num)
    hφd.differentiableAt
  rw [hφd.deriv, slope_def_field] at hle
  simp [φ] at hle
  linarith

/-- `e^{-f} dx` is a finite measure when `f - π‖·‖²` is convex (so `f` grows at least quadratically,
hence `e^{-f}` is integrable). -/
theorem isFiniteMeasure_withDensity_exp_neg {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → ℝ) (hf : ContDiff ℝ 2 f)
    (hconv : ConvexOn ℝ Set.univ (fun x => f x - Real.pi * ‖x‖ ^ 2)) :
    IsFiniteMeasure (volume.withDensity (fun x => ENNReal.ofReal (Real.exp (-(f x))))) := by
  have hg_cont : ContDiff ℝ 2 (fun x : E => f x - Real.pi * ‖x‖ ^ 2) :=
    hf.sub (contDiff_const.mul (contDiff_norm_sq ℝ))
  have hg_diff : DifferentiableAt ℝ (fun x : E => f x - Real.pi * ‖x‖ ^ 2) 0 :=
    (hg_cont.differentiable (by norm_num)) 0
  set L : E →L[ℝ] ℝ := fderiv ℝ (fun x : E => f x - Real.pi * ‖x‖ ^ 2) 0 with hLdef
  have hL : HasFDerivAt (fun x : E => f x - Real.pi * ‖x‖ ^ 2) L 0 := hg_diff.hasFDerivAt
  -- tangent lower bound for `g = f - π‖·‖²`
  have htan : ∀ x : E,
      (f 0 - Real.pi * ‖(0 : E)‖ ^ 2) + L x ≤ f x - Real.pi * ‖x‖ ^ 2 := by
    intro x
    have h := convexOn_le_fderiv hconv hL x
    simpa using h
  -- `L x` is bounded below by `-‖L‖‖x‖`
  have hLbound : ∀ x : E, -(‖L‖ * ‖x‖) ≤ L x := by
    intro x
    have h : ‖L x‖ ≤ ‖L‖ * ‖x‖ := L.le_opNorm x
    have habs : |L x| ≤ ‖L‖ * ‖x‖ := by rwa [Real.norm_eq_abs] at h
    exact (abs_le.mp habs).1
  -- hence `f` grows at least quadratically
  have hf_lower : ∀ x : E,
      Real.pi * ‖x‖ ^ 2 - ‖L‖ * ‖x‖ + (f 0 - Real.pi * ‖(0 : E)‖ ^ 2) ≤ f x := by
    intro x
    have h1 := htan x
    have h2 := hLbound x
    linarith
  -- the quadratic-completion inequality
  have hquad : ∀ r : ℝ,
      -Real.pi * r ^ 2 + ‖L‖ * r ≤ ‖L‖ ^ 2 / (2 * Real.pi) - (Real.pi / 2) * r ^ 2 := by
    intro r
    have hnn : 0 ≤ (‖L‖ - Real.pi * r) ^ 2 / (2 * Real.pi) :=
      div_nonneg (sq_nonneg _) (by positivity)
    have hident : ‖L‖ ^ 2 / (2 * Real.pi) - (Real.pi / 2) * r ^ 2 -
        (‖L‖ - Real.pi * r) ^ 2 / (2 * Real.pi) = -Real.pi * r ^ 2 + ‖L‖ * r := by
      have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
      field_simp
      ring
    linarith
  -- exponential decay bound, dominated by a scaled Gaussian
  have hpt : ∀ x : E,
      Real.exp (-(f x)) ≤
        Real.exp (‖L‖ ^ 2 / (2 * Real.pi) - (f 0 - Real.pi * ‖(0 : E)‖ ^ 2)) *
          Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2) := by
    intro x
    rw [← Real.exp_add]
    apply Real.exp_le_exp.mpr
    have hl := hf_lower x
    have hq := hquad ‖x‖
    linarith
  -- the dominating Gaussian is integrable
  have hint : MeasureTheory.Integrable (fun x : E => Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2))
      volume :=
    Commons.Measure.Integral.integrable_rexp_neg_mul_sq_norm (Real.pi / 2) (by positivity)
  have hnn : 0 ≤ᵐ[volume] (fun x : E => Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2)) :=
    ae_of_all _ (fun x => (Real.exp_pos _).le)
  have hz : ∫⁻ x : E, ENNReal.ofReal (Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2)) =
      ENNReal.ofReal (∫ x : E, Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2)) :=
    (ofReal_integral_eq_lintegral_ofReal hint hnn).symm
  have hC : 0 ≤ Real.exp (‖L‖ ^ 2 / (2 * Real.pi) - (f 0 - Real.pi * ‖(0 : E)‖ ^ 2)) :=
    (Real.exp_pos _).le
  have hlin : ∫⁻ x : E, ENNReal.ofReal (Real.exp (-(f x))) ≤
      ENNReal.ofReal (Real.exp (‖L‖ ^ 2 / (2 * Real.pi) - (f 0 - Real.pi * ‖(0 : E)‖ ^ 2))) *
        ∫⁻ x : E, ENNReal.ofReal (Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2)) := by
    calc
      ∫⁻ x : E, ENNReal.ofReal (Real.exp (-(f x)))
          ≤ ∫⁻ x : E, ENNReal.ofReal
              (Real.exp (‖L‖ ^ 2 / (2 * Real.pi) - (f 0 - Real.pi * ‖(0 : E)‖ ^ 2)) *
                Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2)) := by
            apply lintegral_mono
            intro x
            exact ENNReal.ofReal_le_ofReal (hpt x)
      _ = ∫⁻ x : E, ENNReal.ofReal
              (Real.exp (‖L‖ ^ 2 / (2 * Real.pi) - (f 0 - Real.pi * ‖(0 : E)‖ ^ 2))) *
                ENNReal.ofReal (Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2)) := by
            apply lintegral_congr
            intro x
            rw [ENNReal.ofReal_mul hC]
      _ = ENNReal.ofReal
              (Real.exp (‖L‖ ^ 2 / (2 * Real.pi) - (f 0 - Real.pi * ‖(0 : E)‖ ^ 2))) *
                ∫⁻ x : E, ENNReal.ofReal (Real.exp (-(Real.pi / 2) * ‖x‖ ^ 2)) := by
            rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine isFiniteMeasure_withDensity (ne_of_lt (lt_of_le_of_lt hlin ?_))
  rw [hz, ← ENNReal.ofReal_mul hC]
  exact ENNReal.ofReal_lt_top

end Commons.Analysis.GaussianMeasure