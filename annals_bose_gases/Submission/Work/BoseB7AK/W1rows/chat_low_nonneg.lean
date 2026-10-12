import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.BoseB7AK.W1low.chat_sub_le_abs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.W1rows.chat_low_nonneg` — low-momentum positivity of `Ŵ`

For an integrable `W ≥ 0` a.e. supported in `ball 0 R`, the `p`-convention
Fourier transform `Work.BoseFixR.chat W` is nonnegative on the whole ball
`‖k‖ R ≤ 1` of momentum space.

## Why

`chat` is the *cosine* transform
(`Work.BoseB7AK.W1low.chat_eq_integral_cos`):
`Ŵ(k) = ∫ y, W(y) cos⟨k,y⟩ dy`.  If `W y ≠ 0` then `‖y‖ < R`, hence

`|⟨k,y⟩| ≤ ‖k‖‖y‖ ≤ ‖k‖R ≤ 1`,

so `cos⟨k,y⟩ ≥ cos 1 > 0` — the phase never leaves the region where the cosine
is positive.  Since `W ≥ 0` a.e., the integrand is a.e. bounded below by
`(cos 1)·W(y)`, and therefore

`Ŵ(k) = ∫ y, W(y)cos⟨k,y⟩ dy ≥ cos 1 · ∫ y, W(y) dy ≥ 0`.

No second-moment hypothesis is actually needed for this (the quadratic Fourier
estimate `chat_sub_le`/`chat_sub_le_abs` is used for the *lower bound by mass*,
not here); `h2` is kept because the caller states the same hypotheses as the
quadratic rows.  Contrast with `Work.BoseB7AK.W1low.W1_low_nonneg`, which needs
`‖k‖R ≤ 1/2` and shows the stronger `Ŵ₁(k) ≥ (1 − ½(‖k‖R)²)∫W₁`.
-/

noncomputable section

-- `hR` and `h2` are part of the requested interface but are not needed by the argument.
set_option linter.unusedVariables false

namespace Work.BoseB7AK.W1rows

theorem chat_low_nonneg {W : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ} (hR : 0 ≤ R)
    (hint : MeasureTheory.Integrable W)
    (h2 : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) => ‖x‖ ^ 2 * |W x|))
    (hnn : ∀ᵐ x, 0 ≤ W x)
    (hsupp : ∀ x : EuclideanSpace ℝ (Fin 3), R ≤ ‖x‖ → W x = 0)
    {k : EuclideanSpace ℝ (Fin 3)} (hk : ‖k‖ * R ≤ 1) :
    0 ≤ Work.BoseFixR.chat W k := by
  rw [Work.BoseB7AK.W1low.chat_eq_integral_cos hint k]
  have hcos1 : 0 < Real.cos 1 := Real.cos_one_pos
  -- integrability of the cosine transform of `W`
  have hInt : MeasureTheory.Integrable
      (fun y : EuclideanSpace ℝ (Fin 3) => W y * Real.cos (inner ℝ k y)) := by
    refine hint.mul_bdd (c := 1) (by fun_prop) ?_
    filter_upwards with y
    simp only [Real.norm_eq_abs]
    exact abs_le.mpr ⟨Real.neg_one_le_cos _, Real.cos_le_one _⟩
  -- the pointwise bound `(cos 1)·W y ≤ W y · cos⟨k,y⟩` a.e.
  have hdom : ∀ᵐ y : EuclideanSpace ℝ (Fin 3),
      Real.cos 1 * W y ≤ W y * Real.cos (inner ℝ k y) := by
    filter_upwards [hnn] with y hy
    by_cases hyR : ‖y‖ ≤ R
    · -- `|⟨k,y⟩| ≤ ‖k‖‖y‖ ≤ ‖k‖R ≤ 1`, so `cos⟨k,y⟩ ≥ cos 1`
      have hinner : |inner ℝ k y| ≤ 1 := by
        have h1 : |inner ℝ k y| ≤ ‖k‖ * ‖y‖ := by
          simpa [Real.norm_eq_abs] using norm_inner_le_norm (𝕜 := ℝ) k y
        have h2' : ‖k‖ * ‖y‖ ≤ ‖k‖ * R := mul_le_mul_of_nonneg_left hyR (norm_nonneg k)
        linarith [hk]
      have hcos : Real.cos 1 ≤ Real.cos (inner ℝ k y) := by
        rw [← Real.cos_abs (inner ℝ k y)]
        exact Real.cos_le_cos_of_nonneg_of_le_pi (abs_nonneg _)
          (by linarith [Real.pi_gt_three]) hinner
      simpa [mul_comm] using mul_le_mul_of_nonneg_right hcos hy
    · -- `W` vanishes outside `ball 0 R`
      have hyR2 : R ≤ ‖y‖ := le_of_lt (lt_of_not_ge hyR)
      rw [hsupp y hyR2]
      simp
  -- integrate the pointwise bound and use `∫W ≥ 0`
  have hmono := MeasureTheory.integral_mono_ae (hint.const_mul (Real.cos 1)) hInt hdom
  have hnn2 : 0 ≤ Real.cos 1 * ∫ y, W y :=
    mul_nonneg hcos1.le (MeasureTheory.integral_nonneg_of_ae hnn)
  rw [MeasureTheory.integral_const_mul] at hmono
  linarith

end Work.BoseB7AK.W1rows
