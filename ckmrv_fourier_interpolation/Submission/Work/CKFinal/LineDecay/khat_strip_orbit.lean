import Mathlib
import Submission.Work.CKFinal.LineDecay.shift_helpers
import Submission.Work.CKFinal.LineDecay.orbit_classification

namespace Work.CKFinal.LineDecay

/-- When `τ` lies on `Re τ = ±1/2` with `Im τ ≥ 12`, an `SL(2,ℤ)`-translate of the form
`-1 +ᵥ τ` can never have non-negative real part (it is `Re τ - 1 = -1/2` or `-3/2`). -/
theorem not_ofComplex_eq_vadd_neg_one (τ : UpperHalfPlane) {z : ℂ}
    (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (hzre : 0 ≤ z.re)
    (hzim : 0 < z.im) :
    UpperHalfPlane.ofComplex z ≠ ((-1 : ℝ) +ᵥ τ) := by
  intro h
  have hcoe : (z : ℂ) = (((-1 : ℝ) +ᵥ τ : UpperHalfPlane) : ℂ) := by
    have := congrArg (fun p : UpperHalfPlane => (p : ℂ)) h
    rwa [UpperHalfPlane.ofComplex_apply_of_im_pos hzim] at this
  have hreζ : z.re = -1 + τ.re := by
    have h' := congrArg Complex.re hcoe
    simpa only [UpperHalfPlane.coe_vadd, Complex.add_re, Complex.ofReal_re,
      UpperHalfPlane.coe_re] using h'
  rcases hre with hh | hh <;> linarith

theorem khat_strip_orbit (τ : UpperHalfPlane) (ζ : ℂ) (hre : τ.re = 1 / 2 ∨ τ.re = - 1 / 2) (him : 12 ≤ τ.im) (h1 : 0 ≤ ζ.re) (h2 : ζ.re ≤ 1) (h3 : 1 ≤ ζ.im) (hj : Work.Kernels.jInvariantFun τ = Work.Kernels.jInvariantFun (UpperHalfPlane.ofComplex ζ)) : UpperHalfPlane.ofComplex ζ = τ ∨ UpperHalfPlane.ofComplex ζ = ((1 : ℝ) +ᵥ τ) := by
  have hz2 : -1 ≤ ζ.re := by linarith
  rcases ofComplex_mem_orbit τ hre him h3 hz2 h2 hj with h | h | h
  · exact Or.inl h
  · exact absurd h (not_ofComplex_eq_vadd_neg_one τ hre h1 (by linarith))
  · exact Or.inr h

end Work.CKFinal.LineDecay
