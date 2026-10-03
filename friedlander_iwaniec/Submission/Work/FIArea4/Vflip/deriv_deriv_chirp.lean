import Mathlib

namespace Work.FIArea4.Vflip

/-- The logarithmic derivative of `|·|` away from the origin: for `x ≠ 0`,
`deriv (fun x => Real.log |x|) x = x⁻¹`. -/
private lemma hasDerivAt_log_abs' {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x : ℝ => Real.log |x|) (x⁻¹) x := by
  have hne : |x| ≠ 0 := abs_ne_zero.mpr hx
  have hs : (SignType.sign x : ℝ) = x / |x| := by
    rw [eq_div_iff hne]; exact sign_mul_abs x
  have hval : |x|⁻¹ * (SignType.sign x : ℝ) = x⁻¹ := by
    rw [hs]; field_simp; rw [sq_abs]
  have h0 : HasDerivAt (fun x : ℝ => Real.log |x|) (|x|⁻¹ * (SignType.sign x : ℝ)) x := by
    simpa [Function.comp_def] using (Real.hasDerivAt_log hne).comp x (hasDerivAt_abs hx)
  rwa [hval] at h0

/-- First derivative of the chirp `m(ξ) = exp(iα log|ξ|)` away from the origin:
`m' = ((iα)/ξ) · m`. -/
private lemma hasDerivAt_chirp' (α : ℝ) {x : ℝ} (hx : x ≠ 0) :
    HasDerivAt (fun x : ℝ => Complex.exp (((α * Real.log |x| : ℝ) : ℂ) * Complex.I))
      (((α : ℂ) * (x : ℂ)⁻¹) * Complex.I * Complex.exp (((α * Real.log |x| : ℝ) : ℂ) * Complex.I)) x := by
  have hlog1 : HasDerivAt (fun x : ℝ => Real.log |x|) (x⁻¹) x := hasDerivAt_log_abs' hx
  have hlogα : HasDerivAt (fun x : ℝ => α * Real.log |x|) (α * x⁻¹) x := hlog1.const_mul α
  have hc : HasDerivAt (fun x : ℝ => ((α * Real.log |x| : ℝ) : ℂ)) ((α * x⁻¹ : ℝ) : ℂ) x :=
    HasDerivAt.ofReal_comp hlogα
  have hu : HasDerivAt (fun x : ℝ => ((α * Real.log |x| : ℝ) : ℂ) * Complex.I)
      (((α * x⁻¹ : ℝ) : ℂ) * Complex.I) x := hc.mul_const Complex.I
  have hval2 : (((α * x⁻¹ : ℝ) : ℂ) * Complex.I) = ((α : ℂ) * (x : ℂ)⁻¹) * Complex.I := by
    push_cast; ring
  have hexp : HasDerivAt (fun x : ℝ => Complex.exp (((α * Real.log |x| : ℝ) : ℂ) * Complex.I))
      (Complex.exp (((α * Real.log |x| : ℝ) : ℂ) * Complex.I) * (((α : ℂ) * (x : ℂ)⁻¹) * Complex.I)) x :=
    (Complex.hasDerivAt_exp (((α * Real.log |x| : ℝ) : ℂ) * Complex.I)).comp x (hu.congr_deriv hval2)
  have key : (((α : ℂ) * (x : ℂ)⁻¹) * Complex.I * Complex.exp (((α * Real.log |x| : ℝ) : ℂ) * Complex.I))
      = Complex.exp (((α * Real.log |x| : ℝ) : ℂ) * Complex.I) * (((α : ℂ) * (x : ℂ)⁻¹) * Complex.I) := by
    ring
  exact hexp.congr_deriv key.symm

/-- Second derivative of the chirp `m(ξ) = exp(iα log|ξ|)`: since `m' = (iα/ξ)·m` one has
`m'' = -(α²+iα)/ξ² · m`. -/
theorem deriv_deriv_chirp (α : ℝ) {ξ : ℝ} (hξ : ξ ≠ 0) :
    deriv (deriv (fun x : ℝ => Complex.exp (((α * Real.log |x| : ℝ) : ℂ) * Complex.I))) ξ =
      -(((α : ℂ) ^ 2 + Complex.I * (α : ℂ)) / (ξ : ℂ) ^ 2) *
        Complex.exp (((α * Real.log |ξ| : ℝ) : ℂ) * Complex.I) := by
  have hGderiv :
      deriv (fun x : ℝ => ((α : ℂ) * (x : ℂ)⁻¹) * Complex.I *
          Complex.exp (((α * Real.log |x| : ℝ) : ℂ) * Complex.I)) ξ =
        -(((α : ℂ) ^ 2 + Complex.I * (α : ℂ)) / (ξ : ℂ) ^ 2) *
          Complex.exp (((α * Real.log |ξ| : ℝ) : ℂ) * Complex.I) := by
    have hξc : (ξ : ℂ) ≠ 0 := by exact_mod_cast hξ
    have hid : HasDerivAt (fun x : ℝ => (x : ℂ)) (1 : ℂ) ξ := by
      simpa using HasDerivAt.ofReal_comp (hasDerivAt_id ξ : HasDerivAt (fun x : ℝ => x) (1 : ℝ) ξ)
    have hinv : HasDerivAt (fun x : ℝ => ((x : ℂ))⁻¹) (-(1 : ℂ) / (ξ : ℂ) ^ 2) ξ := hid.inv hξc
    have hh : HasDerivAt (fun x : ℝ => ((α : ℂ) * (x : ℂ)⁻¹) * Complex.I)
        (((α : ℂ) * (-(1 : ℂ) / (ξ : ℂ) ^ 2)) * Complex.I) ξ :=
      (hinv.const_mul (α : ℂ)).mul_const Complex.I
    have hk : HasDerivAt (fun x : ℝ => Complex.exp (((α * Real.log |x| : ℝ) : ℂ) * Complex.I))
        ((((α : ℂ) * (ξ : ℂ)⁻¹) * Complex.I) *
          Complex.exp (((α * Real.log |ξ| : ℝ) : ℂ) * Complex.I)) ξ :=
      hasDerivAt_chirp' α hξ
    have hmul := hh.mul hk
    have hval : deriv (fun x : ℝ => ((α : ℂ) * (x : ℂ)⁻¹) * Complex.I *
          Complex.exp (((α * Real.log |x| : ℝ) : ℂ) * Complex.I)) ξ
        = (((α : ℂ) * (-(1 : ℂ) / (ξ : ℂ) ^ 2)) * Complex.I) *
            Complex.exp (((α * Real.log |ξ| : ℝ) : ℂ) * Complex.I)
          + (((α : ℂ) * (ξ : ℂ)⁻¹) * Complex.I) * ((((α : ℂ) * (ξ : ℂ)⁻¹) * Complex.I) *
            Complex.exp (((α * Real.log |ξ| : ℝ) : ℂ) * Complex.I)) := hmul.deriv
    rw [hval]
    field_simp
    ring_nf
    rw [Complex.I_sq]
    ring
  have heq : deriv (fun x : ℝ => Complex.exp (((α * Real.log |x| : ℝ) : ℂ) * Complex.I)) =ᶠ[nhds ξ]
      (fun x : ℝ => ((α : ℂ) * (x : ℂ)⁻¹) * Complex.I *
        Complex.exp (((α * Real.log |x| : ℝ) : ℂ) * Complex.I)) :=
    Filter.eventuallyEq_of_mem (compl_singleton_mem_nhds hξ)
      (fun x hx => (hasDerivAt_chirp' α hx).deriv)
  rw [Filter.EventuallyEq.deriv_eq heq, hGderiv]

end Work.FIArea4.Vflip
