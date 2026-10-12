import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `chat` is the cosine transform

The corpus's `p`-convention Fourier transform is
`kinFT u p = ∫ y, e^{−i⟪p,y⟫} u(y) dy`, and `Work.BoseFixR.chat W` is the real
part of `kinFT` of the complexification of a real function `W`:

`chat W p = Re ∫ y, e^{−i⟪p,y⟫} W(y) dy`.

Taking the real part commutes with the integral, and *pointwise* `Re(e^{−it}) = cos t`,
so `chat W p = ∫ y, W(y) cos⟪p,y⟫ dy` for **every** real integrable `W` — no
evenness of `W` is needed (the real part already kills the sine part).

This is the identity `Work.BoseFixR.chat W q = ∫ x, W x * Real.cos ⟪q,x⟫`.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixR.Rb5Lin

/-- The real part of a purely imaginary exponential times a real number:
`Re(e^{−it}·w) = w·cos t`. -/
private lemma re_exp_mul_ofReal (t w : ℝ) :
    (Complex.exp (-(Complex.I * (t : ℂ))) * (w : ℂ)).re = w * Real.cos t := by
  rw [Complex.mul_re, Complex.exp_re, Complex.exp_im, Complex.ofReal_re, Complex.ofReal_im]
  simp only [Complex.mul_re, Complex.mul_im, Complex.I_re, Complex.I_im, Complex.ofReal_re,
    Complex.ofReal_im, Complex.neg_re, Complex.neg_im, Real.cos_neg, mul_zero,
    sub_zero, zero_mul, Real.exp_neg, Real.exp_zero, inv_one, one_mul, zero_add]
  ring

theorem chat_eq_cos {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hW : MeasureTheory.Integrable W)
    (q : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.chat W q = ∫ x, W x * Real.cos (inner ℝ q x) := by
  have hnorm : ∀ y : EuclideanSpace ℝ (Fin 3),
      ‖Complex.exp (-(Complex.I * (inner ℝ q y : ℂ)))‖ ≤ 1 := by
    intro y
    simp [Complex.norm_exp]
  have hInt : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ q y : ℂ))) * ((W y : ℝ) : ℂ)) :=
    hW.ofReal.bdd_mul (c := 1) (by fun_prop) (Filter.Eventually.of_forall hnorm)
  rw [Work.BoseFixR.chat, Submission.BoseGases.kinFT, ← Complex.reCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hInt]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  exact re_exp_mul_ofReal (inner ℝ q y) (W y)

end Work.BoseFixR.Rb5Lin
