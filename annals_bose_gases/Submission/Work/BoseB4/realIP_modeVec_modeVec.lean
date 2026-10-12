import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB4.BoxChiScaling
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB4.realIP_modeVec_modeVec`

The Gram product of two localised plane waves `f_k = e^{ikx} χ_Λ`
(`Work.BoseB4.BoxData.modeVec`) in the **real** inner product

    `realIP f g = ∫ Re(conj(f x) · g x)`

of `Work.BoseB4.BoxChi` is the (unstripped) box kernel:

    `⟨f_k, f_{k'}⟩ = ℓ³ χ̂²(ℓ(k' − k))`.

This is the *first* of the two terms of FS's `eq:Commutator_general`; the second
comes from the projection onto the condensate `θ_Λ`.  The proof is pointwise:
`conj(e^{ikx}χ_Λ) · e^{ik'x}χ_Λ = χ_Λ² e^{i⟪k'−k,x⟫}`, whose real part is
`χ_Λ² cos⟪k'−k,x⟫`, and the box integral is the scaling identity
`Work.BoseB4.BoxData.integral_chiLam_sq_mul_cos` of `BoxChiScaling`.
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- Pointwise form of the Gram product of two localised plane waves: for real
`c` (the value of `χ_Λ`) and real phases `a`, `b`,

    `Re(conj(e^{ia} c) · e^{ib} c) = c² cos(b − a)`.

The conjugation of the first exponential is handled by `Complex.exp_conj`, and
the two exponentials are merged with `Complex.exp_add`; `Real.cos_sub` supplies
the angle difference. -/
lemma modeVec_integrand_re (c a b : ℝ) :
    ((starRingEnd ℂ) (Complex.exp (Complex.I * (a : ℂ)) * (c : ℂ))
        * (Complex.exp (Complex.I * (b : ℂ)) * (c : ℂ))).re
      = c ^ 2 * Real.cos (b - a) := by
  have hconj : (starRingEnd ℂ) (Complex.exp (Complex.I * (a : ℂ)))
      = Complex.exp (Complex.I * (-(a : ℂ))) := by
    rw [← Complex.exp_conj, map_mul, Complex.conj_I, Complex.conj_ofReal]
    ring_nf
  rw [map_mul, Complex.conj_ofReal, hconj]
  have hstep : (Complex.exp (Complex.I * (-(a : ℂ))) * (c : ℂ)
        * (Complex.exp (Complex.I * (b : ℂ)) * (c : ℂ)))
      = ((c : ℂ) * (c : ℂ))
        * (Complex.exp (Complex.I * (-(a : ℂ))) * Complex.exp (Complex.I * (b : ℂ))) := by
    ring
  rw [hstep, ← Complex.ofReal_mul, ← Complex.exp_add]
  have harg : Complex.I * (-(a : ℂ)) + Complex.I * (b : ℂ) = ((b - a : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [harg, Complex.exp_ofReal_mul_I]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.mul_re, Complex.ofReal_im, zero_mul,
    sub_zero, Complex.I_re, Complex.I_im, mul_zero, Complex.add_im, zero_add, mul_one]
  rw [Real.cos_sub]
  ring

/-- The integrand of `realIP (modeVec ℓ k) (modeVec ℓ k')` is
`χ_Λ² cos⟪k' − k, x⟫`. -/
lemma modeVec_realIP_integrand (B : BoxData) (ℓ : ℝ) (k k' : ℝ³) :
    (fun x : ℝ³ => ((starRingEnd ℂ) (B.modeVec ℓ k x) * B.modeVec ℓ k' x).re)
      = fun x : ℝ³ => (B.chiLam ℓ x) ^ 2 * Real.cos (inner ℝ (k' - k) x) := by
  funext x
  simp only [BoxData.modeVec_apply]
  rw [inner_sub_left]
  exact modeVec_integrand_re (B.chiLam ℓ x) (inner ℝ k x) (inner ℝ k' x)

/-- **The Gram product of two localised plane waves**: in the real inner product
of `L²(Λ)`, `⟨e^{ikx}χ_Λ, e^{ik'x}χ_Λ⟩ = ℓ³ χ̂²(ℓ(k' − k))`. -/
theorem realIP_modeVec_modeVec (B : Work.BoseB4.BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (k k' : EuclideanSpace ℝ (Fin 3)) :
    B.realIP (B.modeVec ℓ k) (B.modeVec ℓ k') = ℓ ^ 3 * B.hatChiSq (ℓ • (k' - k)) := by
  rw [BoxData.realIP_apply, modeVec_realIP_integrand B ℓ k k']
  exact BoxData.integral_chiLam_sq_mul_cos B hℓ (k' - k)

end Work.BoseB4
