import Mathlib
import Submission.Work.TMComp.Kotani.EllDerivDefs

/-!
# C8 (Kotani theory): the identity (L5)

The energy-derivative of the covariance relation gives

`m'(E, x+α) = 1 + m'(E,x)/m(E,x)²`,

and the covariance relations at the phases `x` and `-x` give the *local* relation

`defect(E, x+α) · m(E,x) · s(E,x) = defect(E,x)`,

where `s(E,x) = 1/m(E, α-x)`.  Combining these two produces the pointwise identity

`R(E,x) = 1/defect(E,x+α) - m'(E,x+α)/defect(E,x+α) + m'(E,x)/defect(E,x)`,

whose coboundary part has vanishing integral; this is step (L5) of the Kotani computation.
-/

open MeasureTheory Filter Topology Set
open LeanEval.Analysis.TenMartini

noncomputable section

namespace Work.TMComp.Kotani

open Work.TMContract

/-- Differentiating the covariance relation `m(x+α) = E - pot x - 1/m(x)` in the energy. -/
theorem mderiv_covariance (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (x : ℝ) :
    mderiv α lam E (x + α) = 1 + mderiv α lam E x / (mfun α lam E x)^2 := by
  have hnb : {z : ℂ | 0 < z.im} ∈ 𝓝 E :=
    (isOpen_lt continuous_const Complex.continuous_im).mem_nhds hE
  have hcov_nhds : (fun z : ℂ => mfun α lam z (x + α)) =ᶠ[𝓝 E]
      (fun z : ℂ => z - ((pot lam x : ℝ) : ℂ) - 1 / mfun α lam z x) := by
    filter_upwards [hnb] with z hz using MfunProbs.mfun_covariance α lam hz x
  have hdiff : DifferentiableAt ℂ (fun z : ℂ => mfun α lam z x) E :=
    (MfunProbs.mfun_differentiableOn α lam x).differentiableAt
      ((isOpen_lt continuous_const Complex.continuous_im).mem_nhds hE)
  have hne : mfun α lam E x ≠ 0 :=
    ne_of_apply_ne Complex.im (ne_of_gt (MfunProbs.mfun_im_pos α lam hE x))
  have hder : HasDerivAt (fun z : ℂ => z - ((pot lam x : ℝ) : ℂ) - 1 / mfun α lam z x)
      (1 + mderiv α lam E x / (mfun α lam E x)^2) E := by
    have h1 : HasDerivAt (fun z : ℂ => z - ((pot lam x : ℝ) : ℂ)) 1 E :=
      (hasDerivAt_id E).sub_const _
    have h2 : HasDerivAt (fun z : ℂ => (mfun α lam z x)⁻¹)
        (-(mderiv α lam E x) / (mfun α lam E x)^2) E := hdiff.hasDerivAt.inv hne
    have h3 := h1.sub h2
    have hfun : ((fun z : ℂ => z - ((pot lam x : ℝ) : ℂ)) - fun z : ℂ => (mfun α lam z x)⁻¹)
        = fun z : ℂ => z - ((pot lam x : ℝ) : ℂ) - 1 / mfun α lam z x := by
      funext z; simp [one_div]
    have hval : 1 - (-(mderiv α lam E x) / (mfun α lam E x)^2)
        = 1 + mderiv α lam E x / (mfun α lam E x)^2 := by ring
    rw [hfun, hval] at h3
    exact h3
  rw [mderiv, hcov_nhds.deriv_eq, hder.deriv]

/-- **The (L5) pointwise identity.** -/
theorem Rfun_eq_defect (α lam : ℝ) {E : ℂ} (hE : 0 < E.im) (x : ℝ) :
    Rfun α lam E x
      = 1 / defect α lam E (x + α) - mderiv α lam E (x + α) / defect α lam E (x + α)
          + mderiv α lam E x / defect α lam E x := by
  have hcov2 : mfun α lam E (α - x) = E - ((pot lam x : ℝ) : ℂ) - 1 / mfun α lam E (-x) := by
    have h := MfunProbs.mfun_covariance α lam hE (-x)
    rw [show -x + α = α - x by ring, pot_even] at h
    exact h
  have hmx : mfun α lam E x ≠ 0 :=
    ne_of_apply_ne Complex.im (ne_of_gt (MfunProbs.mfun_im_pos α lam hE x))
  have hwne : mfun α lam E (α - x) ≠ 0 :=
    ne_of_apply_ne Complex.im (ne_of_gt (MfunProbs.mfun_im_pos α lam hE (α - x)))
  have hDx : defect α lam E (x + α) = mfun α lam E (x + α) - 1 / mfun α lam E (-x) := by
    simp only [defect, sSec]
    rw [show α - (x + α) = -x by ring]
  have hDw : defect α lam E (x + α) = mfun α lam E (α - x) - 1 / mfun α lam E x := by
    rw [hDx, hcov2, MfunProbs.mfun_covariance α lam hE x]
    ring
  have hDms : defect α lam E (x + α) * mfun α lam E x * sSec α lam E x = defect α lam E x := by
    rw [hDw, defect, sSec]
    field_simp
  have hmd := mderiv_covariance α lam hE x
  have hB : defect α lam E x = mfun α lam E x - sSec α lam E x := rfl
  have hBne : mfun α lam E x - sSec α lam E x ≠ 0 := by
    rw [← hB]; exact defect_ne_zero α lam hE x
  have hsne : sSec α lam E x ≠ 0 := by
    simp only [sSec]; exact div_ne_zero one_ne_zero hwne
  have hD_eq : defect α lam E (x + α) = defect α lam E x / (mfun α lam E x * sSec α lam E x) := by
    rw [hB] at hDms ⊢
    field_simp
    linear_combination hDms
  rw [Rfun, hmd, hD_eq, hB]
  field_simp
  ring

end Work.TMComp.Kotani
