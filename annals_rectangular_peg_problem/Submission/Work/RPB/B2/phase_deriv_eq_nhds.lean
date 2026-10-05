import Submission.Work.RPB.B2.phase_deriv_eq

namespace Work.RPB.B2

theorem phase_deriv_eq_nhds (z w : ℝ → ℂ) (φ : ℝ → ℝ) (t : ℝ) (ζ η : ℂ) (φ' : ℝ)
    (hz : HasDerivAt z ζ t) (hw : HasDerivAt w η t) (hφ : HasDerivAt φ φ' t)
    (hv : z t - w t ≠ 0)
    (harg : ∀ᶠ s in nhds t, (Complex.exp (-(φ s : ℂ) * Complex.I) * (z s - w s)).im = 0) :
    φ' = ((ζ - η) / (z t - w t)).im := by
  -- Derivative of `s ↦ exp (-(φ s) * I)`.
  have hu : HasDerivAt (fun s => Complex.exp (-(φ s : ℂ) * Complex.I))
      (Complex.exp (-(φ t : ℂ) * Complex.I) * (-(φ' : ℂ) * Complex.I)) t := by
    have h1 : HasDerivAt (fun s : ℝ => (φ s : ℂ)) ((φ' : ℂ)) t := HasDerivAt.ofReal_comp hφ
    have h2 : HasDerivAt (fun s : ℝ => -(φ s : ℂ) * Complex.I) (-(φ' : ℂ) * Complex.I) t := by
      have h1' : HasDerivAt (fun s : ℝ => (φ s : ℂ) * (-Complex.I))
          ((φ' : ℂ) * (-Complex.I)) t := h1.mul_const _
      convert h1' using 1
      · funext s; ring
      · ring
    have h3 := (Complex.hasDerivAt_exp (-(φ t : ℂ) * Complex.I)).comp t h2
    have h3' : HasDerivAt (fun s => Complex.exp (-(φ s : ℂ) * Complex.I))
        (Complex.exp (-(φ t : ℂ) * Complex.I) * (-(φ' : ℂ) * Complex.I)) t := h3
    exact h3'
  -- Derivative of `s ↦ z s - w s`.
  have hv' : HasDerivAt (fun s => z s - w s) (ζ - η) t := hz.sub hw
  have hF := hu.mul hv'
  have hF' : HasDerivAt (fun s => Complex.exp (-(φ s : ℂ) * Complex.I) * (z s - w s))
      ((Complex.exp (-(φ t : ℂ) * Complex.I) * (-(φ' : ℂ) * Complex.I)) * (z t - w t)
        + Complex.exp (-(φ t : ℂ) * Complex.I) * (ζ - η)) t := hF
  have him := hasDerivAt_im hF'
  -- The imaginary part of `g` is *eventually* zero, hence its derivative is zero.
  have h2 : HasDerivAt (fun _ : ℝ => (0 : ℝ))
      ((Complex.exp (-(φ t : ℂ) * Complex.I) * (-(φ' : ℂ) * Complex.I)) * (z t - w t)
        + Complex.exp (-(φ t : ℂ) * Complex.I) * (ζ - η)).im t :=
    (Filter.EventuallyEq.hasDerivAt_iff harg).mp him
  have hkey : ((Complex.exp (-(φ t : ℂ) * Complex.I) * (-(φ' : ℂ) * Complex.I)) * (z t - w t)
        + Complex.exp (-(φ t : ℂ) * Complex.I) * (ζ - η)).im = 0 :=
    h2.unique (hasDerivAt_const t (0 : ℝ))
  exact im_div_eq_of_im_eq_zero (hD := harg.self_of_nhds)
    (hnz := mul_ne_zero (Complex.exp_ne_zero _) hv) hkey

end Work.RPB.B2
