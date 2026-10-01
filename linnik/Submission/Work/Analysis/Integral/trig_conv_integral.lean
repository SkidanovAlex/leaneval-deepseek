import Mathlib

namespace Work.Analysis.Integral

/-- Antiderivative of `t ↦ (cos (z*t) - cos θ) * (cos (z*(x-t)) - cos θ)`. -/
private noncomputable def antideriv (z θ x : ℝ) : ℝ → ℝ :=
  fun s => s * Real.cos (z * x) / 2 + Real.sin (2 * z * s - z * x) / (4 * z)
        - Real.cos θ * Real.sin (z * s) / z + Real.cos θ * Real.sin (z * (x - s)) / z
        + Real.cos θ ^ 2 * s

private lemma hasDerivAt_antideriv (z x θ : ℝ) (hz : z ≠ 0) (t : ℝ) :
    HasDerivAt (antideriv z θ x)
      ((Real.cos (z * t) - Real.cos θ) * (Real.cos (z * (x - t)) - Real.cos θ)) t := by
  unfold antideriv
  have h1 : HasDerivAt (fun s : ℝ => s * Real.cos (z * x) / 2) (Real.cos (z * x) / 2) t := by
    simpa using ((hasDerivAt_id t).mul_const (Real.cos (z * x))).div_const 2
  have h2 : HasDerivAt (fun s : ℝ => Real.sin (2 * z * s - z * x) / (4 * z))
      (Real.cos (2 * z * t - z * x) / 2) t := by
    have hin : HasDerivAt (fun s : ℝ => 2 * z * s - z * x) (2 * z) t := by
      have h1' : HasDerivAt (fun s : ℝ => (2 * z) * s) (2 * z) t := by
        simpa using (hasDerivAt_id t).const_mul (2 * z)
      simpa using h1'.sub_const (z * x)
    have hsin : HasDerivAt (fun s : ℝ => Real.sin (2 * z * s - z * x))
        (Real.cos (2 * z * t - z * x) * (2 * z)) t := hin.sin
    have hdiv := hsin.div_const (4 * z)
    rw [show Real.cos (2 * z * t - z * x) * (2 * z) / (4 * z)
          = Real.cos (2 * z * t - z * x) / 2 by field_simp; ring] at hdiv
    exact hdiv
  have h3 : HasDerivAt (fun s : ℝ => Real.cos θ * Real.sin (z * s) / z)
      (Real.cos θ * Real.cos (z * t)) t := by
    have hin : HasDerivAt (fun s : ℝ => z * s) z t := by
      simpa using (hasDerivAt_id t).const_mul z
    have hsin : HasDerivAt (fun s : ℝ => Real.sin (z * s)) (Real.cos (z * t) * z) t := hin.sin
    have hmul : HasDerivAt (fun s : ℝ => Real.cos θ * Real.sin (z * s))
        (Real.cos θ * (Real.cos (z * t) * z)) t := hsin.const_mul (Real.cos θ)
    have hdiv := hmul.div_const z
    rw [show Real.cos θ * (Real.cos (z * t) * z) / z = Real.cos θ * Real.cos (z * t) by
          field_simp] at hdiv
    exact hdiv
  have h4 : HasDerivAt (fun s : ℝ => Real.cos θ * Real.sin (z * (x - s)) / z)
      (-(Real.cos θ * Real.cos (z * (x - t)))) t := by
    have hin1 : HasDerivAt (fun s : ℝ => x - s) (-1) t := by
      simpa using (hasDerivAt_id t).const_sub x
    have hin : HasDerivAt (fun s : ℝ => z * (x - s)) (z * (-1)) t := hin1.const_mul z
    have hsin : HasDerivAt (fun s : ℝ => Real.sin (z * (x - s)))
        (Real.cos (z * (x - t)) * (z * (-1))) t := hin.sin
    have hmul : HasDerivAt (fun s : ℝ => Real.cos θ * Real.sin (z * (x - s)))
        (Real.cos θ * (Real.cos (z * (x - t)) * (z * (-1)))) t := hsin.const_mul (Real.cos θ)
    have hdiv := hmul.div_const z
    rw [show Real.cos θ * (Real.cos (z * (x - t)) * (z * (-1))) / z
          = -(Real.cos θ * Real.cos (z * (x - t))) by field_simp] at hdiv
    exact hdiv
  have h5 : HasDerivAt (fun s : ℝ => Real.cos θ ^ 2 * s) (Real.cos θ ^ 2) t := by
    simpa using (hasDerivAt_id t).const_mul (Real.cos θ ^ 2)
  have hsum := (((h1.add h2).sub h3).add h4).add h5
  have hkey : Real.cos (z * t) * Real.cos (z * (x - t))
      = (Real.cos (z * x) + Real.cos (2 * z * t - z * x)) / 2 := by
    have h := Real.two_mul_cos_mul_cos (z * t) (z * (x - t))
    rw [show z * t - z * (x - t) = 2 * z * t - z * x by ring,
        show z * t + z * (x - t) = z * x by ring] at h
    linarith [h]
  have hdd : Real.cos (z * x) / 2 + Real.cos (2 * z * t - z * x) / 2
        - Real.cos θ * Real.cos (z * t)
        + -(Real.cos θ * Real.cos (z * (x - t))) + Real.cos θ ^ 2
      = (Real.cos (z * t) - Real.cos θ) * (Real.cos (z * (x - t)) - Real.cos θ) := by
    rw [show (Real.cos (z * t) - Real.cos θ) * (Real.cos (z * (x - t)) - Real.cos θ)
        = Real.cos (z * t) * Real.cos (z * (x - t)) - Real.cos θ * Real.cos (z * t)
          - Real.cos θ * Real.cos (z * (x - t)) + Real.cos θ ^ 2 by ring, hkey]
    ring
  exact hsum.congr_deriv hdd

theorem trig_conv_integral (z g θ x : ℝ) (hz : z ≠ 0) (hzg : z * g = θ) :
    ∫ t in (x - g)..g,
        (Real.cos (z * t) - Real.cos θ) * (Real.cos (z * (x - t)) - Real.cos θ)
      = (2 * g - x) * (Real.cos (z * x) / 2 + Real.cos θ ^ 2)
        + Real.sin (2 * θ - z * x) / (2 * z) - Real.sin (2 * θ) / z
        + 2 * Real.cos θ * Real.sin (z * x - θ) / z := by
  have hcont : Continuous (fun t : ℝ =>
      (Real.cos (z * t) - Real.cos θ) * (Real.cos (z * (x - t)) - Real.cos θ)) := by fun_prop
  have hftc := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := x - g) (b := g)
    (f := antideriv z θ x)
    (f' := fun t : ℝ => (Real.cos (z * t) - Real.cos θ) * (Real.cos (z * (x - t)) - Real.cos θ))
    (fun s _ => hasDerivAt_antideriv z x θ hz s)
    (hcont.intervalIntegrable (x - g) g)
  rw [hftc]
  unfold antideriv
  have e4 : 2 * z * g - z * x = 2 * θ - z * x := by rw [mul_assoc, hzg]
  have e5 : 2 * z * (x - g) - z * x = z * x - 2 * θ := by rw [mul_assoc, mul_sub, hzg]; ring
  have e6 : Real.sin (z * x - 2 * θ) = - Real.sin (2 * θ - z * x) := by
    rw [← Real.sin_neg]; congr 1; ring
  have e2 : z * (x - g) = z * x - θ := by rw [mul_sub, hzg]
  have e3 : z * (x - (x - g)) = θ := by rw [show x - (x - g) = g by ring, hzg]
  rw [e4, e5, e6, e2, e3, hzg, Real.sin_two_mul]
  ring

end Work.Analysis.Integral
