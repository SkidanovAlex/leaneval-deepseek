import Mathlib

namespace Work.Mostow

open MeasureTheory

/-- Change of variables for the interpolation map `y ↦ (1 - t) • y + t • f y`.

If this map is injective on the closed unit ball, maps it onto itself, and its
differential `(1 - t) • 1 + t • fderiv f x` has positive determinant everywhere on the
ball, then the integral of that determinant over the ball equals the volume of the ball. -/
theorem integralDetInterpEq {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (f : E → E) (hf : ContDiff ℝ 1 f) {t : ℝ}
    (hderiv : ∀ x, fderiv ℝ (fun y => (1 - t) • y + t • f y) x
      = (1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x)
    (hinj : Set.InjOn (fun y => (1 - t) • y + t • f y) (Metric.closedBall (0 : E) 1))
    (himg : (fun y => (1 - t) • y + t • f y) '' Metric.closedBall (0 : E) 1
      = Metric.closedBall (0 : E) 1)
    (hpos : ∀ x ∈ Metric.closedBall (0 : E) 1,
      0 < ((1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x).det) :
    ∫ x in Metric.closedBall (0 : E) 1,
        ((1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x).det
      = (MeasureTheory.volume (Metric.closedBall (0 : E) 1)).toReal := by
  -- the interpolation map is differentiable everywhere
  have hdiff : ∀ x, DifferentiableAt ℝ (fun y : E => (1 - t) • y + t • f y) x := by
    intro x
    have h1 : DifferentiableAt ℝ (fun y : E => (1 - t) • y) x :=
      ((differentiableAt_id (x := x)).const_smul (1 - t) :
        DifferentiableAt ℝ (fun y : E => (1 - t) • y) x)
    have h2 : DifferentiableAt ℝ (fun y : E => t • f y) x :=
      ((hf.contDiffAt.differentiableAt_one).const_smul t :
        DifferentiableAt ℝ (fun y : E => t • f y) x)
    exact h1.add h2
  -- the closed unit ball is measurable
  have hs : MeasurableSet (Metric.closedBall (0 : E) 1) :=
    Metric.isClosed_closedBall.measurableSet
  -- the derivative of the interpolation map is the required linear map
  have hf' : ∀ x ∈ Metric.closedBall (0 : E) 1,
      HasFDerivWithinAt (fun y => (1 - t) • y + t • f y)
        ((1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x)
        (Metric.closedBall (0 : E) 1) x := by
    intro x _
    have hx : HasFDerivAt (fun y => (1 - t) • y + t • f y)
        ((1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x) x := by
      rw [← hderiv x]
      exact (hdiff x).hasFDerivAt
    exact hx.hasFDerivWithinAt
  -- the change of variables formula for injective differentiable maps
  have key := MeasureTheory.integral_image_eq_integral_abs_det_fderiv_smul
    (MeasureTheory.volume : Measure E)
    (f := fun y => (1 - t) • y + t • f y)
    (f' := fun x => (1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x)
    (s := Metric.closedBall (0 : E) 1) hs hf' hinj (fun _ : E => (1 : ℝ))
  -- the two integrands agree because the determinant is positive on the ball
  have hcongr : ∫ x in Metric.closedBall (0 : E) 1,
        ((1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x).det
      = ∫ x in Metric.closedBall (0 : E) 1,
        |((1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x).det| • (1 : ℝ) := by
    apply setIntegral_congr_fun hs
    intro x hx
    simp only [abs_of_pos (hpos x hx), smul_eq_mul, mul_one]
  calc ∫ x in Metric.closedBall (0 : E) 1,
        ((1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x).det
      = ∫ x in Metric.closedBall (0 : E) 1,
          |((1 - t) • (1 : E →L[ℝ] E) + t • fderiv ℝ f x).det| • (1 : ℝ) := hcongr
    _ = ∫ x in (fun y => (1 - t) • y + t • f y) '' Metric.closedBall (0 : E) 1,
          (1 : ℝ) := key.symm
    _ = (MeasureTheory.volume (Metric.closedBall (0 : E) 1)).toReal := by
        rw [himg, setIntegral_const, MeasureTheory.Measure.real_def, smul_eq_mul, mul_one]

end Work.Mostow
