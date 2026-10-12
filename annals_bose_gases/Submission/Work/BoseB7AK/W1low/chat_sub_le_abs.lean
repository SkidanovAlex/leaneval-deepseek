import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB7AK.W1low.chat_sub_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# The quadratic Fourier bound on `Ŵ`, absolute-value form (`chat_sub_le_abs`)

Companion of `chat_sub_le`, with the nonnegativity hypothesis on `W` dropped and
`W` replaced by `|W|` on the right-hand side:

`|Ŵ(k) − Ŵ(0)| ≤ ½‖k‖² ∫ ‖y‖²|W(y)| dy`

for an integrable real `W` with finite second absolute moment.  No sign nor
evenness assumption is needed: the corpus's `Work.BoseFixR.chat` is the real part
of the `p`-convention Fourier integral, hence the *cosine* transform
(`chat_eq_integral_cos`), and
`|W y (cos⟨k,y⟩ − 1)| = |W y|·|cos⟨k,y⟩ − 1| ≤ |W y|·⟨k,y⟩²/2 ≤ |W y|·‖k‖²‖y‖²/2`
by `Real.one_sub_sq_div_two_le_cos` and Cauchy–Schwarz.
-/

noncomputable section

namespace Work.BoseB7AK.W1low

/-- **The quadratic Fourier estimate, absolute-value form.**  For an integrable
real `W` with `∫ ‖y‖²|W y| < ∞`,

`|Ŵ(k) − Ŵ(0)| ≤ ½‖k‖² ∫ ‖y‖²|W(y)| dy`.

The sign of `W` is irrelevant: taking the real part of `e^{−i⟪k,y⟫}` produces the
cosine transform, and `|cos t − 1| ≤ t²/2` pointwise with `⟨k,y⟩² ≤ ‖k‖²‖y‖²`. -/
theorem chat_sub_le_abs {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hint : MeasureTheory.Integrable W)
    (h2 : MeasureTheory.Integrable fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖ ^ 2 * |W x|)
    (k : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseFixR.chat W k - Work.BoseFixR.chat W 0|
      ≤ (1 / 2) * ‖k‖ ^ 2 * ∫ x : EuclideanSpace ℝ (Fin 3), ‖x‖ ^ 2 * |W x| := by
  rw [chat_eq_integral_cos hint k, chat_eq_integral_cos hint 0]
  simp only [inner_zero_left, Real.cos_zero, mul_one]
  -- `|cos t − 1| ≤ t²/2`
  have hcos_le : ∀ t : ℝ, |Real.cos t - 1| ≤ t ^ 2 / 2 := by
    intro t
    rw [abs_of_nonpos (by linarith [Real.cos_le_one t])]
    linarith [Real.one_sub_sq_div_two_le_cos (x := t)]
  -- integrability of the cosine transform of `W`
  have hA : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) => W y * Real.cos (inner ℝ k y)) := by
    refine hint.mul_bdd (c := 1) (by fun_prop) ?_
    filter_upwards with y
    simp only [Real.norm_eq_abs]
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  -- the pointwise bound
  have hkey : ∀ y : EuclideanSpace ℝ (Fin 3),
      |W y * Real.cos (inner ℝ k y) - W y|
        ≤ (1 / 2) * ‖k‖ ^ 2 * (‖y‖ ^ 2 * |W y|) := by
    intro y
    have hinner : (inner ℝ k y) ^ 2 ≤ ‖k‖ ^ 2 * ‖y‖ ^ 2 := by
      have h : |inner ℝ k y| ≤ ‖k‖ * ‖y‖ := by
        simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) k y
      calc (inner ℝ k y) ^ 2 ≤ (‖k‖ * ‖y‖) ^ 2 := by
            rw [sq_le_sq]
            simpa using h
        _ = ‖k‖ ^ 2 * ‖y‖ ^ 2 := by ring
    have h1 : |W y * Real.cos (inner ℝ k y) - W y|
        = |W y| * |Real.cos (inner ℝ k y) - 1| := by
      rw [show W y * Real.cos (inner ℝ k y) - W y
            = W y * (Real.cos (inner ℝ k y) - 1) by ring, abs_mul]
    rw [h1]
    have hc := hcos_le (inner ℝ k y)
    have hw := abs_nonneg (W y)
    nlinarith [hinner, hc, hw, sq_nonneg ‖k‖, sq_nonneg ‖y‖]
  calc |(∫ y : EuclideanSpace ℝ (Fin 3), W y * Real.cos (inner ℝ k y)) - ∫ y, W y|
      = |∫ y, (W y * Real.cos (inner ℝ k y) - W y)| := by
        rw [MeasureTheory.integral_sub hA hint]
    _ ≤ ∫ y, |W y * Real.cos (inner ℝ k y) - W y| := by
        simpa only [Real.norm_eq_abs] using MeasureTheory.norm_integral_le_integral_norm
          (fun y : EuclideanSpace ℝ (Fin 3) => W y * Real.cos (inner ℝ k y) - W y)
    _ ≤ ∫ y, (1 / 2) * ‖k‖ ^ 2 * (‖y‖ ^ 2 * |W y|) :=
        MeasureTheory.integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun y => abs_nonneg _)
          (h2.const_mul ((1 / 2) * ‖k‖ ^ 2))
          (Filter.Eventually.of_forall hkey)
    _ = (1 / 2) * ‖k‖ ^ 2 * ∫ y, ‖y‖ ^ 2 * |W y| := by
        rw [MeasureTheory.integral_const_mul]

end Work.BoseB7AK.W1low
