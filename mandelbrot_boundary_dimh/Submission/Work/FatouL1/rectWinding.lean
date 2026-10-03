import Mathlib
import Submission.Work.FatouL1.DefsLower

/-!
# FATOU-L1: the winding number of a rectangle around an interior point

`rectB a b Y (fun ζ => (ζ - z)⁻¹) = 2 * π * I` whenever `z` lies in the open rectangle
`(a,b) × (-Y,Y)`.  This is the elementary computation of the (counterclockwise) boundary
integral of `1/(ζ - z)`: we evaluate each of the four edge integrals with the fundamental
theorem of calculus, using a branch of `Complex.log` on each edge, and observe that all
terms cancel against each other except the total change of argument `2π` picked up on the
left edge (where the contour crosses the branch cut).

The file is self-contained; the only ingredient used from `defs.lean` is the definition
`rectB`.
-/

namespace Work.FatouL1

noncomputable section

open MeasureTheory

/-- Real chain rule for `Complex.log` composed with a real path: if `u` is real
differentiable at `x` with derivative `u'` and `u x` is off the branch cut `(-∞,0]`
(i.e. lies in `slitPlane`), then `log ∘ u` is real differentiable at `x` with derivative
`u' * (u x)⁻¹`. -/
theorem hasDerivAt_clog_comp {u : ℝ → ℂ} {u' : ℂ} {x : ℝ}
    (hu : HasDerivAt u u' x) (hmem : u x ∈ Complex.slitPlane) :
    HasDerivAt (fun y => Complex.log (u y)) (u' * (u x)⁻¹) x := by
  have hL : HasFDerivAt Complex.log ((u x)⁻¹ • (1 : ℂ →L[ℝ] ℂ)) (u x) :=
    (Complex.hasStrictFDerivAt_log_real hmem).hasFDerivAt
  have huF : HasFDerivAt u (ContinuousLinearMap.toSpanSingleton ℝ u') x :=
    hasDerivAt_iff_hasFDerivAt.mp hu
  have hraw : HasFDerivAt (Complex.log ∘ u)
      (((u x)⁻¹ • (1 : ℂ →L[ℝ] ℂ)) ∘SL (ContinuousLinearMap.toSpanSingleton ℝ u')) x :=
    hL.comp x huF
  have heq : (((u x)⁻¹ • (1 : ℂ →L[ℝ] ℂ)) ∘SL (ContinuousLinearMap.toSpanSingleton ℝ u'))
      = ContinuousLinearMap.toSpanSingleton ℝ (u' * (u x)⁻¹) := by
    ext
    simp [ContinuousLinearMap.comp_apply, ContinuousLinearMap.toSpanSingleton_apply, smul_eq_mul,
      mul_comm]
  rw [heq] at hraw
  rw [hasDerivAt_iff_hasFDerivAt]
  exact hraw

/-- For `w` in the open lower half plane, `log (-w) = log w + π I` (the arguments differ
by `π`). -/
theorem clog_neg_eq_add_pi_I {w : ℂ} (h : w.im < 0) :
    Complex.log (-w) = Complex.log w + Real.pi * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re, norm_neg]
  · simp only [Complex.log_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one]
    rw [Complex.arg_neg_eq_arg_add_pi_of_im_neg h]

/-- For `w` in the open upper half plane, `log (-w) = log w - π I`. -/
theorem clog_neg_eq_sub_pi_I {w : ℂ} (h : 0 < w.im) :
    Complex.log (-w) = Complex.log w - Real.pi * Complex.I := by
  apply Complex.ext
  · simp [Complex.log_re, norm_neg]
  · simp only [Complex.log_im, Complex.sub_im, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, add_zero, mul_one]
    rw [Complex.arg_neg_eq_arg_sub_pi_of_im_pos h]

theorem I_mul_negI_mul (X : ℂ) : Complex.I * (-Complex.I * X) = X := by
  have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-X) * h

/-- `-I * (I * X) = X`. -/
theorem negI_mul_I_mul (X : ℂ) : -Complex.I * (Complex.I * X) = X := by
  have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-X) * h

/-- `-I * (-I * (-X)⁻¹) = X⁻¹`. -/
theorem negI_mul_negI_mul_inv_neg (X : ℂ) : -Complex.I * (-Complex.I * (-X)⁻¹) = X⁻¹ := by
  rw [inv_neg]
  have h : Complex.I * Complex.I = -1 := Complex.I_mul_I
  linear_combination (-X⁻¹) * h

/-- Integral of `(ζ - z)⁻¹` along the vertical segment `x ↦ x + c`, `x ∈ [p,q]`, where
`c - z` is off the real axis (so that the integrand has no pole on the segment and the
principal branch of `log` is a primitive). -/
theorem integral_vert {p q : ℝ} {c z : ℂ} (hc : (c - z).im ≠ 0) :
    (∫ x in p..q, (((x : ℂ) + c) - z)⁻¹) =
      Complex.log (((q : ℂ) + c) - z) - Complex.log (((p : ℂ) + c) - z) := by
  have hderiv : ∀ x : ℝ, HasDerivAt (fun x : ℝ => Complex.log (((x : ℂ) + c) - z))
      ((((x : ℂ) + c) - z)⁻¹) x := by
    intro x
    have hmem : (((x : ℂ) + c) - z) ∈ Complex.slitPlane := by
      rw [Complex.slitPlane]; right
      simpa [Complex.sub_im, Complex.add_im] using hc
    have hu : HasDerivAt (fun x : ℝ => ((x : ℂ) + c) - z) 1 x := by
      simpa using ((Complex.ofRealCLM.hasDerivAt (x := x)).add_const c).sub_const z
    simpa using hasDerivAt_clog_comp hu hmem
  have hint : IntervalIntegrable (fun x : ℝ => (((x : ℂ) + c) - z)⁻¹) volume p q := by
    apply Continuous.intervalIntegrable
    apply Continuous.inv₀
    · exact ((Complex.ofRealCLM.continuous.add continuous_const).sub continuous_const)
    · intro x h
      have him : (((x : ℂ) + c) - z).im = (c - z).im := by
        simp [Complex.sub_im, Complex.add_im, Complex.ofReal_im]
      have h0 : (((x : ℂ) + c) - z).im = 0 := by rw [h]; simp
      rw [him] at h0
      exact hc h0
  exact intervalIntegral.integral_eq_sub_of_hasDerivAt (fun x _ => hderiv x) hint

/-- Integral of `(ζ - z)⁻¹` along the vertical segment `y ↦ c + y * I`, `y ∈ [p,q]`, where
`c - z` has positive real part (so the principal branch of `log` is a primitive on the
segment). -/
theorem integral_horiz_pos {p q : ℝ} {c z : ℂ} (hc : 0 < (c - z).re) :
    (∫ y in p..q, ((c + (y : ℂ) * Complex.I) - z)⁻¹) =
      -Complex.I * (Complex.log ((c + (q : ℂ) * Complex.I) - z) -
        Complex.log ((c + (p : ℂ) * Complex.I) - z)) := by
  have hderiv : ∀ y : ℝ,
      HasDerivAt (fun y : ℝ => -Complex.I * Complex.log ((c + (y : ℂ) * Complex.I) - z))
        (((c + (y : ℂ) * Complex.I) - z)⁻¹) y := by
    intro y
    have hmem : ((c + (y : ℂ) * Complex.I) - z) ∈ Complex.slitPlane := by
      rw [Complex.slitPlane]; left
      simpa [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im] using hc
    have hu : HasDerivAt (fun y : ℝ => (c + (y : ℂ) * Complex.I) - z) Complex.I y := by
      have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.I) Complex.I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I
      simpa using (h2.const_add c).sub_const z
    have h3 := (hasDerivAt_clog_comp hu hmem).const_mul (-Complex.I)
    rwa [negI_mul_I_mul] at h3
  have hint : IntervalIntegrable (fun y : ℝ => ((c + (y : ℂ) * Complex.I) - z)⁻¹) volume p q := by
    apply Continuous.intervalIntegrable
    apply Continuous.inv₀
    · exact ((continuous_const.add (Complex.ofRealCLM.continuous.mul continuous_const)).sub
        continuous_const)
    · intro y h
      have hre : ((c + (y : ℂ) * Complex.I) - z).re = (c - z).re := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
      have h0 : ((c + (y : ℂ) * Complex.I) - z).re = 0 := by rw [h]; simp
      rw [hre] at h0
      exact absurd h0 (ne_of_gt hc)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) hint]
  ring

/-- Integral of `(ζ - z)⁻¹` along the vertical segment `y ↦ c + y * I`, `y ∈ [p,q]`, where
`c - z` has negative real part.  The segment crosses the branch cut of the principal
`log`, so we use the primitive `-I * log(-(ζ - z))`, which is holomorphic on the reflected
(right) half plane. -/
theorem integral_horiz_neg {p q : ℝ} {c z : ℂ} (hc : (c - z).re < 0) :
    (∫ y in p..q, ((c + (y : ℂ) * Complex.I) - z)⁻¹) =
      -Complex.I * (Complex.log (-((c + (q : ℂ) * Complex.I) - z)) -
        Complex.log (-((c + (p : ℂ) * Complex.I) - z))) := by
  have hderiv : ∀ y : ℝ,
      HasDerivAt (fun y : ℝ => -Complex.I * Complex.log (-((c + (y : ℂ) * Complex.I) - z)))
        (((c + (y : ℂ) * Complex.I) - z)⁻¹) y := by
    intro y
    have hmem : -((c + (y : ℂ) * Complex.I) - z) ∈ Complex.slitPlane := by
      rw [Complex.slitPlane]; left
      have h0 : (-((c + (y : ℂ) * Complex.I) - z)).re = -(c - z).re := by
        rw [Complex.neg_re]; congr 1
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
      rw [h0]; linarith
    have hu : HasDerivAt (fun y : ℝ => -((c + (y : ℂ) * Complex.I) - z)) (-Complex.I) y := by
      have h2 : HasDerivAt (fun y : ℝ => (y : ℂ) * Complex.I) Complex.I y := by
        simpa using (Complex.ofRealCLM.hasDerivAt (x := y)).mul_const Complex.I
      exact ((h2.const_add c).sub_const z).neg
    have h3 := (hasDerivAt_clog_comp hu hmem).const_mul (-Complex.I)
    rwa [negI_mul_negI_mul_inv_neg] at h3
  have hint : IntervalIntegrable (fun y : ℝ => ((c + (y : ℂ) * Complex.I) - z)⁻¹) volume p q := by
    apply Continuous.intervalIntegrable
    apply Continuous.inv₀
    · exact ((continuous_const.add (Complex.ofRealCLM.continuous.mul continuous_const)).sub
        continuous_const)
    · intro y h
      have hre : ((c + (y : ℂ) * Complex.I) - z).re = (c - z).re := by
        simp [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
          Complex.I_re, Complex.I_im]
      have h0 : ((c + (y : ℂ) * Complex.I) - z).re = 0 := by rw [h]; simp
      rw [hre] at h0
      linarith
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun y _ => hderiv y) hint]
  ring

theorem rectWinding {a b Y : ℝ} {z : ℂ} (haz : a < z.re) (hzb : z.re < b)
    (hYl : -Y < z.im) (hYr : z.im < Y) :
    Work.FatouL1.rectB a b Y (fun ζ => (ζ - z)⁻¹) = 2 * Real.pi * Complex.I := by
  have hc1 : ((((-Y : ℂ) * Complex.I) - z).im) ≠ 0 := by
    have h0 : ((((-Y : ℂ) * Complex.I) - z).im) = -Y - z.im := by
      simp [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    rw [h0]; intro hh; linarith
  have hc2 : ((((Y : ℝ) : ℂ) * Complex.I - z).im) ≠ 0 := by
    have h0 : ((((Y : ℝ) : ℂ) * Complex.I - z).im) = Y - z.im := by
      simp [Complex.sub_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
        Complex.I_re, Complex.I_im]
    rw [h0]; intro hh; linarith
  have hc3 : 0 < (((b : ℂ) - z).re) := by
    have h0 : (((b : ℂ) - z).re) = b - z.re := by simp [Complex.sub_re]
    rw [h0]; linarith
  have hc4 : (((a : ℂ) - z).re) < 0 := by
    have h0 : (((a : ℂ) - z).re) = a - z.re := by simp [Complex.sub_re]
    rw [h0]; linarith
  have h1 := integral_vert (p := a) (q := b) (c := (-Y : ℂ) * Complex.I) (z := z) hc1
  have h2 := integral_vert (p := a) (q := b) (c := ((Y : ℝ) : ℂ) * Complex.I) (z := z) hc2
  have h3 := integral_horiz_pos (p := -Y) (q := Y) (c := (b : ℂ)) (z := z) hc3
  have h4 := integral_horiz_neg (p := -Y) (q := Y) (c := (a : ℂ)) (z := z) hc4
  have hb1 : Complex.log (-(((a : ℂ) + (-Y : ℂ) * Complex.I) - z)) =
      Complex.log (((a : ℂ) + (-Y : ℂ) * Complex.I) - z) + Real.pi * Complex.I := by
    refine clog_neg_eq_add_pi_I ?_
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    linarith
  have hb2 : Complex.log (-(((a : ℂ) + ((Y : ℝ) : ℂ) * Complex.I) - z)) =
      Complex.log (((a : ℂ) + ((Y : ℝ) : ℂ) * Complex.I) - z) - Real.pi * Complex.I := by
    refine clog_neg_eq_sub_pi_I ?_
    simp [Complex.sub_im, Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
    linarith
  rw [rectB, h1, h2, h3, h4]
  simp only [Complex.ofReal_neg, I_mul_negI_mul]
  rw [hb1, hb2]
  ring

end

end Work.FatouL1
