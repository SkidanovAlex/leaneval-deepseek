import Mathlib

namespace Work.RPB.B2

/-- If `f : ℝ → ℂ` has derivative `c` at `t`, then its imaginary part has derivative `c.im`. -/
private lemma hasDerivAt_im {f : ℝ → ℂ} {c : ℂ} {t : ℝ} (h : HasDerivAt f c t) :
    HasDerivAt (fun s => (f s).im) c.im t := by
  simpa [Function.comp_def, smul_apply, Complex.imCLM_apply]
    using (Complex.imCLM.hasFDerivAt.comp t h.hasFDerivAt).hasDerivAt

/-- `exp (x * I) * exp (-x * I) = 1` for any complex `x`. -/
private lemma exp_mul_exp_neg_I (x : ℂ) :
    Complex.exp (x * Complex.I) * Complex.exp ((-x) * Complex.I) = 1 := by
  rw [← Complex.exp_add]
  have : x * Complex.I + (-x) * Complex.I = 0 := by ring
  rw [this, Complex.exp_zero]

/-- **The key algebraic step.**  Given `F * ψ = (r : ℂ)` with `r` a nonzero real number, an
identity `Im (p * ψ + F * (ψ * (-(A' * I)))) = 0` (which expresses that `s ↦ F * ψ` is real),
and the differentiability data, one recovers `A'` as `Im (p / F)`. -/
private lemma im_div_of_im_zero {p ψ F : ℂ} {r A' : ℝ} (hr : r ≠ 0)
    (hFψ : F * ψ = (r : ℂ))
    (h : (p * ψ + F * (ψ * (-(A' * Complex.I)))).im = 0) :
    A' = (p / F).im := by
  have hrC : (r : ℂ) ≠ 0 := by exact_mod_cast hr
  have hF : F ≠ 0 := fun h0 => hrC (by rw [← hFψ, h0, zero_mul])
  have hψ : ψ = (r : ℂ) / F := by rw [eq_div_iff hF, mul_comm]; exact hFψ
  rw [hψ] at h
  have hFr : F * ((r : ℂ) / F) = (r : ℂ) := by field_simp
  rw [← mul_assoc] at h
  rw [hFr] at h
  have e1 : p * ((r : ℂ) / F) = (r : ℂ) * (p / F) := by field_simp
  rw [e1] at h
  have h1 : ((r : ℂ) * (p / F)).im = r * (p / F).im := by simp [Complex.mul_im]
  have h2 : ((r : ℂ) * (-(A' * Complex.I))).im = -(r * A') := by
    simp [Complex.mul_im, Complex.neg_im]
  rw [Complex.add_im, h1, h2] at h
  have hz0 : (p / F).im - A' = 0 := by
    have : r * ((p / F).im - A') = 0 := by linarith
    exact (mul_eq_zero.mp this).resolve_left hr
  linarith

theorem argLift_deriv {z w : ℝ → ℂ} {A : ℝ → ℝ} {t A' : ℝ} {ζ η : ℂ}
    (hz : HasDerivAt z ζ t) (hw : HasDerivAt w η t) (hA : HasDerivAt A A' t)
    (hne : z t ≠ w t)
    (harg : ∀ᶠ s in nhds t, z s - w s = (‖z s - w s‖ : ℂ) * Complex.exp (A s * Complex.I)) :
    A' = ((ζ - η) / (z t - w t)).im := by
  -- `F = z - w` and the auxiliary function `Ψ s = (z s - w s) * exp (-(A s) * I)`.
  have hF : HasDerivAt (fun s => z s - w s) (ζ - η) t := hz.sub hw
  have hg : HasDerivAt (fun s => Complex.exp (-(A s) * Complex.I))
      (Complex.exp (-(A t) * Complex.I) * (-(A' * Complex.I))) t := by
    have hAc : HasDerivAt (fun s => (A s : ℂ)) A' t := hA.ofReal_comp
    have hinner : HasDerivAt (fun s => -(A s) * Complex.I) (-(A' * Complex.I)) t := by
      simpa using (hAc.neg.mul_const Complex.I)
    exact hinner.cexp
  have hΨ : HasDerivAt (fun s => (z s - w s) * Complex.exp (-(A s) * Complex.I))
      ((ζ - η) * Complex.exp (-(A t) * Complex.I)
        + (z t - w t) * (Complex.exp (-(A t) * Complex.I) * (-(A' * Complex.I)))) t :=
    hF.mul hg
  have hΨim : HasDerivAt (fun s => ((z s - w s) * Complex.exp (-(A s) * Complex.I)).im)
      (((ζ - η) * Complex.exp (-(A t) * Complex.I)
        + (z t - w t) * (Complex.exp (-(A t) * Complex.I) * (-(A' * Complex.I)))).im) t :=
    hasDerivAt_im hΨ
  -- On a neighbourhood of `t`, `Ψ` equals the real number `‖z s - w s‖`, so its imaginary
  -- part vanishes there and therefore has zero derivative at `t`.
  have hev : (fun s => ((z s - w s) * Complex.exp (-(A s) * Complex.I)).im)
      =ᶠ[nhds t] fun _ => 0 := by
    filter_upwards [harg] with s hs
    rw [hs, mul_assoc, exp_mul_exp_neg_I, mul_one, Complex.ofReal_im]
  have h0 : HasDerivAt (fun s => ((z s - w s) * Complex.exp (-(A s) * Complex.I)).im) 0 t :=
    HasDerivAt.congr_of_eventuallyEq (hasDerivAt_const t (0 : ℝ)) hev
  have hDval :
      ((ζ - η) * Complex.exp (-(A t) * Complex.I)
        + (z t - w t) * (Complex.exp (-(A t) * Complex.I) * (-(A' * Complex.I)))).im = 0 :=
    hΨim.unique h0
  -- The value at `t` of the polar decomposition.
  have hFt : z t - w t = (‖z t - w t‖ : ℂ) * Complex.exp (A t * Complex.I) := harg.self_of_nhds
  have hr : ‖z t - w t‖ ≠ 0 := norm_ne_zero_iff.mpr (sub_ne_zero.mpr hne)
  have hFψ : (z t - w t) * Complex.exp (-(A t) * Complex.I) = (‖z t - w t‖ : ℂ) := by
    conv_lhs => rw [hFt]
    rw [mul_assoc, exp_mul_exp_neg_I, mul_one]
  exact im_div_of_im_zero hr hFψ hDval

end Work.RPB.B2
