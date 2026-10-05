import Mathlib

namespace Work.RPB.B2

/-- Arithmetic core.

If `c * D` is a nonzero *real* complex number (`(c * D).im = 0`, `c * D ≠ 0`) and the
imaginary part of `c * (-(↑p) * I) * D + c * D'` vanishes, then `p` is the imaginary part
of the quotient `D' / D`.

Geometrically: `c` is a unit complex number making `c * D` real, and the vanishing
imaginary part is the first-order condition that the argument of `c * D` equals the
argument of `c * D'`; dividing cancels `c`. -/
lemma im_div_eq_of_im_eq_zero {c D D' : ℂ} {p : ℝ}
    (hD : (c * D).im = 0) (hnz : c * D ≠ 0)
    (hkey : ((c * ((-↑p) * Complex.I)) * D + c * D').im = 0) :
    p = (D' / D).im := by
  -- `c * D` is the real number `(c * D).re`.
  have hcD : c * D = (((c * D).re : ℝ) : ℂ) := by
    rw [← Complex.re_add_im (c * D), hD]; simp
  have ha : (c * D).re ≠ 0 := by
    intro h; apply hnz; rw [hcD, h]; simp
  have hc : c ≠ 0 := by
    intro h; apply hnz; rw [h, zero_mul]
  -- Regroup the vanishing imaginary part as `(-(↑p) * I) * (c * D) + c * D'`.
  have hkey' : (((-↑p) * Complex.I) * (c * D) + c * D').im = 0 := by
    have h : (c * ((-↑p) * Complex.I)) * D + c * D'
        = ((-↑p) * Complex.I) * (c * D) + c * D' := by ring
    rw [h] at hkey; exact hkey
  rw [hcD] at hkey'
  -- Compute the imaginary part and read off `(c * D').im = p * (c * D).re`.
  have hval : (((-↑p) * Complex.I) * (((c * D).re : ℝ) : ℂ) + c * D').im
      = (c * D').im - p * (c * D).re := by
    simp only [Complex.add_im, Complex.neg_im, Complex.neg_re, Complex.mul_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_im, Complex.I_re, mul_zero, add_zero]
    ring
  rw [hval] at hkey'
  have hres : (c * D').im = p * (c * D).re := by linarith
  -- Rewrite `D' / D` using `D = c⁻¹ * (c * D)`.
  have hfinal : D' / D = (c * D') / (c * D) := (mul_div_mul_left D' D hc).symm
  rw [hfinal, hcD, div_eq_mul_inv, ← Complex.ofReal_inv, Complex.mul_im]
  simp only [Complex.ofReal_re, Complex.ofReal_im, mul_zero, zero_add]
  rw [hres, mul_assoc, mul_inv_cancel₀ ha, mul_one]

/-- The imaginary part of a complex-valued function inherits the imaginary part of the
derivative. -/
lemma hasDerivAt_im {f : ℝ → ℂ} {f' : ℂ} {t : ℝ} (hf : HasDerivAt f f' t) :
    HasDerivAt (fun s => (f s).im) f'.im t := by
  have h : HasDerivAt (Complex.im ∘ f) (Complex.imCLM f') t :=
    (Complex.imCLM.hasFDerivAt).comp_hasDerivAt t hf
  have h' : HasDerivAt (fun s => (f s).im) f'.im t := h
  exact h'

theorem phase_deriv_eq (z w : ℝ → ℂ) (φ : ℝ → ℝ) (t : ℝ) (ζ η : ℂ) (φ' : ℝ)
    (hz : HasDerivAt z ζ t) (hw : HasDerivAt w η t) (hφ : HasDerivAt φ φ' t)
    (hv : z t - w t ≠ 0)
    (harg : ∀ s, (Complex.exp (-(φ s : ℂ) * Complex.I) * (z s - w s)).im = 0) :
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
  -- The imaginary part of `g` is identically zero, hence its derivative is zero.
  have him := hasDerivAt_im hF'
  have hzero : (fun s => (Complex.exp (-(φ s : ℂ) * Complex.I) * (z s - w s)).im)
      = fun _ => (0 : ℝ) := funext fun s => harg s
  have hc : HasDerivAt
      (fun s => (Complex.exp (-(φ s : ℂ) * Complex.I) * (z s - w s)).im) 0 t := by
    rw [hzero]; exact hasDerivAt_const t 0
  have hkey := him.unique hc
  exact im_div_eq_of_im_eq_zero (hD := harg t)
    (hnz := mul_ne_zero (Complex.exp_ne_zero _) hv) hkey

end Work.RPB.B2
