import Mathlib
import Submission.Work.TMComp.RedC8.EllBound.Defs

/-!
# Continuity of the harmonic-measure barrier `harc` at the arc

`harc E₀ R M z = (2M/π) · Im (log w(z))` with `w(z) = (R + (z - E₀)) / (R - (z - E₀))`.

On the upper arc `{0 < Im z, ‖z - E₀‖ = R}` the Möbius transform `w` takes values in the open
upper half plane (`Im w = 2R·Im(z-E₀)/‖R - (z-E₀)‖² > 0`), hence off the branch cut `(-∞,0]` of
`Complex.log`; since `w` is continuous at such a point and `log` is continuous on the slit plane,
`harc` is continuous there.
-/

noncomputable section

open Complex

namespace Work.TMComp.RedC8

/-- The Möbius transform `w = (R + ζ)/(R - ζ)` has strictly positive imaginary part when
`R > 0` and `Im ζ > 0`. -/
private lemma mobius_im_pos (R : ℝ) (hR : 0 < R) {ζ : ℂ} (hζ : 0 < ζ.im) :
    0 < (((R : ℂ) + ζ) / ((R : ℂ) - ζ)).im := by
  have hb : (R : ℂ) - ζ ≠ 0 := by
    intro h
    have him : ((R : ℂ) - ζ).im = 0 := by rw [h]; simp
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub] at him
    linarith
  have hns : 0 < Complex.normSq ((R : ℂ) - ζ) := by
    rwa [Complex.normSq_pos]
  have key : (((R : ℂ) + ζ) / ((R : ℂ) - ζ)).im
      = 2 * R * ζ.im / Complex.normSq ((R : ℂ) - ζ) := by
    rw [Complex.div_im]
    simp only [Complex.add_im, Complex.add_re, Complex.ofReal_im, Complex.ofReal_re,
      Complex.sub_im, Complex.sub_re]
    ring
  rw [key]
  exact div_pos (by positivity) hns

theorem harc_continuousAt_arc (E₀ R M : ℝ) :
    ∀ z : ℂ, 0 < z.im → ‖z - (E₀ : ℂ)‖ = R →
      ContinuousAt (Work.TMComp.RedC8.harc E₀ R M) z := by
  intro z hz hnorm
  have hR : 0 < R := by
    have h := Complex.abs_im_le_norm (z - (E₀ : ℂ))
    simp only [Complex.sub_im, Complex.ofReal_im, sub_zero] at h
    rw [hnorm, abs_of_pos hz] at h
    linarith
  have hζ : 0 < (z - (E₀ : ℂ)).im := by simpa using hz
  have hb : (R : ℂ) - (z - (E₀ : ℂ)) ≠ 0 := by
    intro h
    have him : ((R : ℂ) - (z - (E₀ : ℂ))).im = 0 := by rw [h]; simp
    simp only [Complex.sub_im, Complex.ofReal_im, zero_sub] at him
    linarith
  have hslit : (((R : ℂ) + (z - (E₀ : ℂ))) / ((R : ℂ) - (z - (E₀ : ℂ))))
      ∈ Complex.slitPlane :=
    Complex.mem_slitPlane_iff.mpr
      (Or.inr (ne_of_gt (mobius_im_pos R hR hζ)))
  change ContinuousAt (fun w : ℂ =>
      (2 * M / Real.pi)
        * (Complex.log (((R : ℂ) + (w - (E₀ : ℂ))) / ((R : ℂ) - (w - (E₀ : ℂ))))).im) z
  have h1 : ContinuousAt (fun w : ℂ => (R : ℂ) + (w - (E₀ : ℂ))) z := by fun_prop
  have h2 : ContinuousAt (fun w : ℂ => (R : ℂ) - (w - (E₀ : ℂ))) z := by fun_prop
  have hq : ContinuousAt
      (fun w : ℂ => ((R : ℂ) + (w - (E₀ : ℂ))) / ((R : ℂ) - (w - (E₀ : ℂ)))) z :=
    h1.div h2 hb
  have hlog : ContinuousAt
      (fun w : ℂ =>
        Complex.log (((R : ℂ) + (w - (E₀ : ℂ))) / ((R : ℂ) - (w - (E₀ : ℂ))))) z :=
    hq.clog hslit
  have him : ContinuousAt
      (fun w : ℂ =>
        (Complex.log (((R : ℂ) + (w - (E₀ : ℂ))) / ((R : ℂ) - (w - (E₀ : ℂ))))).im) z :=
    Complex.continuous_im.continuousAt.comp hlog
  exact him.const_mul (2 * M / Real.pi)

end Work.TMComp.RedC8
