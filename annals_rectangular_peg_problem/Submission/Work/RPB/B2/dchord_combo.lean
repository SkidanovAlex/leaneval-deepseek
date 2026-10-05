import Mathlib
import Submission.Work.RPV.Defs

/-!
# Linearity of the chord differential in the pair (`Work.RPB.B2.dchord_combo`)

`dchord z w a ζ η` is the linearisation of the chord map `chordPS` at `(z,w)` (with `a` a lift of
`arg (z-w)`) in the direction `(ζ,η)`.  It is `ℝ`-linear in `(ζ,η)`, and this file records the
concrete identity needed by `Work.RPB.B2.chordSurf_immersed`:

`α • dchord z w a ζ η + β • dchord z w a ζ (-η)
   = dchord z w a (((α+β) : ℂ) * ζ) (((α-β) : ℂ) * η)`.

The proof is pure algebra.  Writing `E = exp (-(a:ℂ) * I)` and `p = (z+w)/√2`, the `da` coordinate
of `dchord` is `im ((ζ-η)/(z-w))` and the `(p₁,p₂)` coordinates are `E * ((ζ+η)/√2 - da·I·p)`
together with `Re(conj z · ζ) + Re(conj w · η)`.  Each of the three pieces is linear, and the
`da`-piece is handled *without* expanding the division, so the identity holds also when `z = w`.
-/

namespace Work.RPB.B2

theorem dchord_combo (z w : ℂ) (a α β : ℝ) (ζ η : ℂ) :
    α • Work.RPV.dchord z w a ζ η + β • Work.RPV.dchord z w a ζ (-η)
      = Work.RPV.dchord z w a (((α + β : ℝ) : ℂ) * ζ) (((α - β : ℝ) : ℂ) * η) := by
  -- The complex identity behind the `da`-coordinate.
  have hda' : (α : ℂ) * ((ζ - η) / (z - w)) + (β : ℂ) * ((ζ + η) / (z - w))
      = (((α + β : ℝ) : ℂ) * ζ - ((α - β : ℝ) : ℂ) * η) / (z - w) := by
    rw [← mul_div_assoc, ← mul_div_assoc, ← add_div]
    congr 1
    push_cast
    ring
  -- the `da`-coordinate is `ℝ`-linear.
  have hd3 : (((((α + β : ℝ) : ℂ) * ζ - ((α - β : ℝ) : ℂ) * η) / (z - w)).im)
      = α * (((ζ - η) / (z - w)).im) + β * (((ζ + η) / (z - w)).im) := by
    have h := congrArg Complex.im hda'
    simpa only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero] using h.symm
  -- the `(p₁,p₂)`-part is `ℂ`-linear once `da` is.
  have hu : Complex.exp (-(a:ℂ)*Complex.I) * ((((α+β:ℝ):ℂ)*ζ + ((α-β:ℝ):ℂ)*η)/(Real.sqrt 2:ℂ)
        - (((((α+β:ℝ):ℂ)*ζ - ((α-β:ℝ):ℂ)*η)/(z-w)).im : ℂ) * Complex.I * ((z+w)/(Real.sqrt 2:ℂ)))
      = (α:ℂ) * (Complex.exp (-(a:ℂ)*Complex.I) * ((ζ+η)/(Real.sqrt 2:ℂ)
            - (((ζ-η)/(z-w)).im : ℂ) * Complex.I * ((z+w)/(Real.sqrt 2:ℂ))))
        + (β:ℂ) * (Complex.exp (-(a:ℂ)*Complex.I) * ((ζ + -η)/(Real.sqrt 2:ℂ)
            - (((ζ+η)/(z-w)).im : ℂ) * Complex.I * ((z+w)/(Real.sqrt 2:ℂ)))) := by
    have hd3c : (((((α+β:ℝ):ℂ)*ζ - ((α-β:ℝ):ℂ)*η)/(z-w)).im : ℂ)
        = (α:ℂ) * ((((ζ-η)/(z-w)).im : ℂ)) + (β:ℂ) * ((((ζ+η)/(z-w)).im : ℂ)) := by
      rw [hd3]; push_cast; ring
    rw [hd3c]
    push_cast
    ring
  -- the `p₂`-coordinate.
  have hp : α * (((starRingEnd ℂ) z * ζ).re + ((starRingEnd ℂ) w * η).re)
        + β * (((starRingEnd ℂ) z * ζ).re + ((starRingEnd ℂ) w * (-η)).re)
      = ((starRingEnd ℂ) z * (((α + β : ℝ) : ℂ) * ζ)).re
        + ((starRingEnd ℂ) w * (((α - β : ℝ) : ℂ) * η)).re := by
    have hc : (α : ℂ) * ((starRingEnd ℂ) z * ζ + (starRingEnd ℂ) w * η)
        + (β : ℂ) * ((starRingEnd ℂ) z * ζ + (starRingEnd ℂ) w * (-η))
        = (starRingEnd ℂ) z * (((α + β : ℝ) : ℂ) * ζ)
          + (starRingEnd ℂ) w * (((α - β : ℝ) : ℂ) * η) := by
      push_cast
      ring
    have h := congrArg Complex.re hc
    simpa only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero] using h
  simp only [Work.RPV.dchord, Prod.smul_mk, Prod.mk_add_mk, smul_eq_mul]
  refine Prod.ext (Prod.ext ?_ ?_) (Prod.ext ?_ ?_) <;>
    simp only [sub_neg_eq_add]
  · rw [hu]
    simp only [Complex.add_im, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, add_zero]
  · rw [hd3]
  · rw [hu]
    simp only [Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im,
      zero_mul, sub_zero]
  · exact hp

end Work.RPB.B2
