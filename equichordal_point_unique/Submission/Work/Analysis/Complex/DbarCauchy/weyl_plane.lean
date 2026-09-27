import Mathlib
import Submission.Work.Analysis.Complex.DbarCauchy.Defs

/-!
# Weyl's lemma for `∂̄` on plane domains (the differentiable case)

The `∂̄` operator of `DbarCauchy.Defs` is `∂̄ f z = ∂_x f z + i ∂_y f z`, so `∂̄ f z = 0` is a
spelling of the Cauchy--Riemann equation at `z`: the real Fréchet derivative is multiplication
by a complex number, i.e. `f` is complex differentiable at `z`.  Consequently a
real-differentiable `f` with `∂̄ f = 0` on an *open* set is holomorphic there.

This is the input the (0,1)-form formalism of the divisor chapter consumes: it converts the
`∂̄`-closedness of a difference of smooth chart representatives into holomorphy of the
corresponding function on the surface.
-/

open MeasureTheory
open scoped Topology

noncomputable section

namespace Work.Analysis.Complex.DbarCauchy

/-- **The Cauchy--Riemann equation.**  If `∂̄ f z = 0` then the real Fréchet derivative of `f` at
`z` is complex linear: it maps `I` to `I • (its value at 1)`. -/
theorem fderiv_eq_of_dbar_eq_zero {f : ℂ → ℂ} {z : ℂ} (h : dbar f z = 0) :
    fderiv ℝ f z Complex.I = Complex.I • fderiv ℝ f z 1 := by
  have hz0 : fderiv ℝ f z 1 + Complex.I * fderiv ℝ f z Complex.I = 0 := h
  have h1 : Complex.I * fderiv ℝ f z Complex.I = -(fderiv ℝ f z 1) :=
    eq_neg_of_add_eq_zero_right hz0
  have h3 : Complex.I * (Complex.I * fderiv ℝ f z Complex.I)
      = Complex.I * (-(fderiv ℝ f z 1)) := congrArg (fun x : ℂ => Complex.I * x) h1
  rw [← mul_assoc, Complex.I_mul_I, neg_one_mul, mul_neg] at h3
  have h2 : fderiv ℝ f z Complex.I = Complex.I * fderiv ℝ f z 1 := neg_inj.mp h3
  simpa [smul_eq_mul] using h2

/-- **Weyl's lemma, plane version.**  A real-differentiable function on an open set `U` whose
`∂̄` vanishes pointwise on `U` is holomorphic (analytic) at every point of `U`. -/
theorem analyticAt_of_dbar_eq_zero {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ z ∈ U, DifferentiableAt ℝ f z) (h : ∀ z ∈ U, dbar f z = 0) {z : ℂ} (hz : z ∈ U) :
    AnalyticAt ℂ f z := by
  refine DifferentiableOn.analyticAt ?_ (hU.mem_nhds hz)
  intro w hw
  exact (differentiableAt_complex_iff_differentiableAt_real.mpr
    ⟨hf w hw, fderiv_eq_of_dbar_eq_zero (h w hw)⟩).differentiableWithinAt

/-- **Weyl's lemma, plane version, on an open set.** -/
theorem analyticOnNhd_of_dbar_eq_zero {f : ℂ → ℂ} {U : Set ℂ} (hU : IsOpen U)
    (hf : ∀ z ∈ U, DifferentiableAt ℝ f z) (h : ∀ z ∈ U, dbar f z = 0) :
    AnalyticOnNhd ℂ f U :=
  fun z hz => analyticAt_of_dbar_eq_zero hU hf h hz

end Work.Analysis.Complex.DbarCauchy
