import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
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
# The quadratic Fourier bound on `Ŵ` (`chat_sub_le`)

FS's proof of `thm:BogHamDiag` uses the elementary quadratic estimate

`|Ŵ(k) − Ŵ(0)| ≤ ½‖k‖² ∫ ‖y‖²W(y) dy`

for a nonnegative integrable `W` with finite second moment (for such `W` the sine
part of the Fourier integral cancels, so `Ŵ(k) = ∫ W(y)cos⟨k,y⟩ dy`).

The corpus's `Work.BoseFixR.chat` is defined as the **real part** of the
`p`-convention Fourier transform `kinFT` of the complexification of `W`:

`chat W k = Re ∫ y, e^{−i⟪k,y⟫} W(y) dy`.

Taking the real part *already* kills the sine part pointwise
(`Re(e^{−it}) = cos t`), so `chat W k = ∫ y, W(y)cos⟨k,y⟩ dy` holds for **every**
real integrable `W` — the evenness hypothesis is not needed for the identity, and
the estimate follows from `|cos t − 1| ≤ t²/2` (`Real.one_sub_sq_div_two_le_cos`)
together with `⟨k,y⟩² ≤ ‖k‖²‖y‖²`.
-/

noncomputable section

-- The requested statement carries the evenness hypothesis `heven`, which turns out not to
-- be needed for the estimate (the real part of the Fourier integral is already the cosine
-- transform); silence the unused-variable linter rather than rename the binder.
set_option linter.unusedVariables false

namespace Work.BoseB7AK.W1low

/-- The real part of a purely imaginary exponential times a real number:
`Re(e^{−it} w) = w cos t`. -/
private lemma re_exp_mul_ofReal (t w : ℝ) :
    (Complex.exp (-(Complex.I * (t : ℂ))) * (w : ℂ)).re = w * Real.cos t := by
  have h : -(Complex.I * (t : ℂ)) = ((-t : ℝ) : ℂ) * Complex.I := by push_cast; ring
  rw [h, Complex.exp_ofReal_mul_I]
  simp [Complex.mul_re, Complex.add_re, Complex.mul_im, Real.cos_neg, Complex.cos_ofReal_re]
  ring

/-- **`chat` is the cosine transform.**  For any real integrable `W`,
`chat W k = ∫ y, W y * cos ⟨k,y⟩ dy`: taking the real part of
`∫ y, e^{−i⟪k,y⟫}W(y)dy` can be done pointwise, so no evenness of `W` is needed. -/
lemma chat_eq_integral_cos {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hint : MeasureTheory.Integrable W) (k : EuclideanSpace ℝ (Fin 3)) :
    Work.BoseFixR.chat W k = ∫ y, W y * Real.cos (inner ℝ k y) := by
  have hnorm : ∀ y : EuclideanSpace ℝ (Fin 3), ‖Complex.exp (-(Complex.I * (inner ℝ k y : ℂ)))‖ ≤ 1 := by
    intro y
    simp [Complex.norm_exp]
  have hInt : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * (inner ℝ k y : ℂ))) * ((W y : ℝ) : ℂ)) :=
    hint.ofReal.bdd_mul (c := 1) (by fun_prop) (Filter.Eventually.of_forall hnorm)
  rw [Work.BoseFixR.chat, Submission.BoseGases.kinFT, ← Complex.reCLM_apply,
    ← ContinuousLinearMap.integral_comp_comm Complex.reCLM hInt]
  apply MeasureTheory.integral_congr_ae
  filter_upwards with y
  exact re_exp_mul_ofReal (inner ℝ k y) (W y)

/-- **The quadratic Fourier estimate of FS (`thm:BogHamDiag`'s proof):** for a
nonnegative integrable `W` with finite second moment,

`|Ŵ(k) − Ŵ(0)| ≤ ½‖k‖² ∫ ‖y‖² W(y) dy`.

The sine part is killed by taking real parts, and `|1 − cos t| ≤ t²/2` together
with `⟨k,y⟩² ≤ ‖k‖²‖y‖²` gives the bound. -/
theorem chat_sub_le {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hint : MeasureTheory.Integrable W)
    (heven : ∀ x : EuclideanSpace ℝ (Fin 3), W (-x) = W x)
    (hWnn : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ W x)
    (h2 : MeasureTheory.Integrable fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖ ^ 2 * W x)
    (k : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseFixR.chat W k - Work.BoseFixR.chat W 0|
      ≤ (1 / 2) * ‖k‖ ^ 2 * ∫ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ^ 2 * W x := by
  rw [chat_eq_integral_cos hint k, chat_eq_integral_cos hint 0]
  simp only [inner_zero_left, Real.cos_zero, mul_one]
  -- `|cos t − 1| ≤ t²/2`
  have hcos_le : ∀ t : ℝ, |Real.cos t - 1| ≤ t ^ 2 / 2 := by
    intro t
    rw [abs_of_nonpos (by linarith [Real.cos_le_one t])]
    linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  -- integrability of the cosine transform of `W`
  have hA : MeasureTheory.Integrable (fun y : EuclideanSpace ℝ (Fin 3) => W y * Real.cos (inner ℝ k y)) := by
    refine hint.mul_bdd (c := 1) (by fun_prop) ?_
    filter_upwards with y
    simp only [Real.norm_eq_abs]
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  -- the pointwise bound
  have hkey : ∀ y : EuclideanSpace ℝ (Fin 3),
      |W y * Real.cos (inner ℝ k y) - W y| ≤ (1 / 2) * ‖k‖ ^ 2 * (‖y‖ ^ 2 * W y) := by
    intro y
    have hinner : (inner ℝ k y) ^ 2 ≤ ‖k‖ ^ 2 * ‖y‖ ^ 2 := by
      have h : |inner ℝ k y| ≤ ‖k‖ * ‖y‖ := by
        simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) k y
      calc (inner ℝ k y) ^ 2 ≤ (‖k‖ * ‖y‖) ^ 2 := by
            rw [sq_le_sq]
            simpa using h
        _ = ‖k‖ ^ 2 * ‖y‖ ^ 2 := by ring
    have h1 : |W y * Real.cos (inner ℝ k y) - W y| = W y * |Real.cos (inner ℝ k y) - 1| := by
      have h2' : W y * Real.cos (inner ℝ k y) - W y
          = W y * (Real.cos (inner ℝ k y) - 1) := by ring
      rw [h2', abs_mul, abs_of_nonneg (hWnn y)]
    rw [h1]
    have hc := hcos_le (inner ℝ k y)
    have hw := hWnn y
    nlinarith [hinner, hc, hw, sq_nonneg ‖k‖, sq_nonneg ‖y‖]
  calc |(∫ y : EuclideanSpace ℝ (Fin 3), W y * Real.cos (inner ℝ k y)) - ∫ y, W y|
      = |∫ y, (W y * Real.cos (inner ℝ k y) - W y)| := by
        rw [MeasureTheory.integral_sub hA hint]
    _ ≤ ∫ y, |W y * Real.cos (inner ℝ k y) - W y| := by
        simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm
          (fun y : EuclideanSpace ℝ (Fin 3) => W y * Real.cos (inner ℝ k y) - W y)
    _ ≤ ∫ y, (1 / 2) * ‖k‖ ^ 2 * (‖y‖ ^ 2 * W y) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun y => abs_nonneg _)
          (h2.const_mul ((1 / 2) * ‖k‖ ^ 2))
          (Filter.Eventually.of_forall hkey)
    _ = (1 / 2) * ‖k‖ ^ 2 * ∫ y, ‖y‖ ^ 2 * W y := by
        rw [MeasureTheory.integral_const_mul]

end Work.BoseB7AK.W1low
