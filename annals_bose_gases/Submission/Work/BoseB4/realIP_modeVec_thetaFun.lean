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
# `Work.BoseB4.realIP_modeVec_thetaFun` — `⟨e^{ikx}χ_Λ, 1_Λ⟩ = ℓ³ χ̂(ℓk)`

The condensate overlap of FS's localized plane wave `f_k = e^{ikx}χ_Λ` with the
sharp box indicator `θ = 1_Λ` (`Work.BoseB4.BoxData.thetaFun`):

    `⟪f_k, θ⟫_{L²(ℂ)} = ∫ θ(x) χ_Λ(x) e^{ikx} dx = ℓ³ χ̂(ℓk)`.

This is exactly FS's identity `ℓ⁻³⟨θ, e^{ikx}χ_Λ⟩ = χ̂(kℓ)`, the one used in
`def:projections` to write the condensate projection `P φ = ℓ⁻³⟨θ,φ⟩θ` and hence
`Q f_k = f_k − χ̂(kℓ)·θ` (`Work.BoseB4.BoxData.qVec`).

The proof is two ingredients, both already in the corpus:

* `χ_Λ` is supported in the box `Λ(ℓ)` (`BoxData.chiLam_supp`), so multiplying
  by the indicator `1_Λ` changes nothing;
* on the box, `Re(conj(e^{ikx})χ_Λ · 1) = χ_Λ(x) cos⟪k,x⟫`, and
  `∫ χ_Λ cos⟪k,x⟫ = ℓ³ χ̂(ℓk)` (`BoxData.integral_chiLam_mul_cos`).
-/

noncomputable section

open scoped BigOperators Pointwise
open MeasureTheory Classical

namespace Work.BoseB4

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

namespace BoxData

/-- **Pointwise form.**  The real part of the `L²(ℂ)` pairing of the localized
plane wave `f_k = e^{ikx}χ_Λ` with the sharp box indicator `1_Λ` is
`χ_Λ(x) cos⟪k,x⟫`: on the box the indicator is `1` and the real part of
`conj(e^{ikx})χ_Λ` is `χ_Λ cos⟪k,x⟫`; off the box both sides vanish, since the
support of `χ_Λ` lies in the box. -/
lemma realIP_modeVec_thetaFun_re (B : BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ) (k : ℝ³) (x : ℝ³) :
    ((starRingEnd ℂ) (B.modeVec ℓ k x) * B.thetaFun ℓ x).re
      = B.chiLam ℓ x * Real.cos (inner ℝ k x) := by
  by_cases hx : x ∈ B.boxL ℓ
  · simp only [modeVec_apply, thetaFun_apply, hx, if_true,
      mul_one, map_mul, Complex.conj_ofReal, Complex.mul_re, Complex.conj_re, Complex.conj_im,
      Complex.ofReal_re, Complex.ofReal_im]
    rw [mul_comm Complex.I ((inner ℝ k x : ℝ) : ℂ), Complex.exp_ofReal_mul_I_re,
      Complex.exp_ofReal_mul_I_im]
    ring
  · have hchi : B.chiLam ℓ x = 0 := by
      by_contra h
      exact hx (B.chiLam_supp hℓ (by simpa using h))
    simp only [modeVec_apply, thetaFun_apply, hx, if_false,
      mul_zero, Complex.zero_re, hchi, zero_mul]

end BoxData

/-- **The condensate overlap of FS's localized plane wave with the box.**
`⟨e^{ikx}χ_Λ, 1_Λ⟩ = ℓ³ χ̂(ℓk)`, i.e. `ℓ⁻³⟨θ, f_k⟩ = χ̂(kℓ)`: the identity
underlying FS's `def:projections` and the definition of `qVec`. -/
theorem realIP_modeVec_thetaFun (B : Work.BoseB4.BoxData) {ℓ : ℝ} (hℓ : 0 < ℓ)
    (k : EuclideanSpace ℝ (Fin 3)) :
    B.realIP (B.modeVec ℓ k) (B.thetaFun ℓ) = ℓ ^ 3 * B.hatChi (ℓ • k) := by
  rw [BoxData.realIP_apply, ← B.integral_chiLam_mul_cos hℓ k]
  exact integral_congr_ae
    (Filter.Eventually.of_forall fun x => B.realIP_modeVec_thetaFun_re hℓ k x)

end Work.BoseB4
