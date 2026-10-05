import Mathlib

namespace Work.RPB.B1

open MeasureTheory intervalIntegral

theorem exp_integral_of_hasDerivAt (w : ℝ → ℂ) (lam : ℝ → ℝ) (hlam : Continuous lam)
    (hw : ∀ s, HasDerivAt w ((lam s : ℂ) * w s) s) :
    ∀ s, w s = Complex.exp (((∫ x in (0 : ℝ)..s, lam x : ℝ) : ℂ)) * w 0 := by
  intro s
  -- The derivative of the primitive of `lam`.
  have hA : ∀ t : ℝ,
      HasDerivAt (fun t : ℝ => ((∫ x in (0 : ℝ)..t, lam x : ℝ) : ℂ)) (lam t : ℂ) t := by
    intro t
    exact (integral_hasDerivAt_right (hlam.intervalIntegrable 0 t)
      hlam.aestronglyMeasurable.stronglyMeasurableAtFilter hlam.continuousAt).ofReal_comp
  -- The integrating factor `w t * exp (-∫ x in 0..t, lam x)` has zero derivative.
  have hF : ∀ t : ℝ,
      HasDerivAt
        (fun t : ℝ => w t * Complex.exp (-(((∫ x in (0 : ℝ)..t, lam x : ℝ) : ℂ)))) 0 t := by
    intro t
    have hg : HasDerivAt
        (fun t : ℝ => Complex.exp (-(((∫ x in (0 : ℝ)..t, lam x : ℝ) : ℂ))))
        (Complex.exp (-(((∫ x in (0 : ℝ)..t, lam x : ℝ) : ℂ))) * (-(lam t : ℂ))) t :=
      (hA t).neg.cexp
    have h2 := (hw t).mul hg
    convert h2 using 1
    ring
  have hconst := is_const_of_deriv_eq_zero
    (f := fun t : ℝ => w t * Complex.exp (-(((∫ x in (0 : ℝ)..t, lam x : ℝ) : ℂ))))
    (fun t => (hF t).differentiableAt) (fun t => (hF t).deriv) s 0
  have hI0 : (((∫ x in (0 : ℝ)..(0 : ℝ), lam x : ℝ) : ℂ)) = 0 := by simp
  have hconst' : w s * Complex.exp (-(((∫ x in (0 : ℝ)..s, lam x : ℝ) : ℂ))) = w 0 := by
    rw [hconst, hI0, neg_zero, Complex.exp_zero, mul_one]
  have hcancel : Complex.exp (-(((∫ x in (0 : ℝ)..s, lam x : ℝ) : ℂ)))
      * Complex.exp (((∫ x in (0 : ℝ)..s, lam x : ℝ) : ℂ)) = 1 := by
    rw [← Complex.exp_add, neg_add_cancel, Complex.exp_zero]
  rw [← mul_one (w s), ← hcancel, ← mul_assoc, hconst', mul_comm]

end Work.RPB.B1
