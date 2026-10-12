import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Submission.Work.BoseB7AK.W1low.chat_sub_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `‖∇Ŵ‖ ≤ ∫ ‖y‖ |W y|`

The `p`-convention Fourier transform `Ŵ = Work.BoseFixR.chat W` is the cosine
transform `Ŵ k = ∫ y, W y · cos ⟪k,y⟫` (`Work.BoseB7AK.W1low.chat_eq_integral_cos`).
Since `|cos a − cos b| ≤ |a − b| ≤ ‖k − k'‖ ‖y‖`, the cosine form gives immediately
that `Ŵ` is **Lipschitz with constant `∫ ‖y‖ |W y|`**:

    |Ŵ q − Ŵ p| ≤ (∫ y, ‖y‖ |W y|) ‖q − p‖.

Whenever `Ŵ` is differentiable at `p`, this Lipschitz bound propagates to the
derivative (`HasFDerivAt.le_of_lipschitz`), giving the requested
`‖fderiv ℝ (chat W) p‖ ≤ ∫ y, ‖y‖ |W y|`; at points of non-differentiability
`fderiv ℝ (chat W) p = 0` and the bound is trivial.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseB7AK.W1rows

/-- The cosine integrand of `chat W k` is integrable (it is dominated by `|W|`). -/
private lemma integrable_cos_integrand {W : ℝ³ → ℝ} (hint : Integrable W) (k : ℝ³) :
    Integrable fun y : ℝ³ => W y * Real.cos (inner ℝ k y) :=
  hint.mul_bdd (by fun_prop) (Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _)

/-- `chat W q − chat W p = ∫ y, W y (cos⟪q,y⟫ − cos⟪p,y⟫)`. -/
private lemma chat_sub_eq {W : ℝ³ → ℝ} (hint : Integrable W) (p q : ℝ³) :
    Work.BoseFixR.chat W q - Work.BoseFixR.chat W p
      = ∫ y : ℝ³, W y * (Real.cos (inner ℝ q y) - Real.cos (inner ℝ p y)) := by
  rw [Work.BoseB7AK.W1low.chat_eq_integral_cos hint q,
    Work.BoseB7AK.W1low.chat_eq_integral_cos hint p,
    ← integral_sub (integrable_cos_integrand hint q) (integrable_cos_integrand hint p)]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  ring

/-- The pointwise Lipschitz estimate: `|W y (cos⟪q,y⟫ − cos⟪p,y⟫)| ≤ (‖y‖ |W y|) ‖p − q‖`. -/
private lemma abs_mul_cos_sub_le {W : ℝ³ → ℝ} (p q : ℝ³) (y : ℝ³) :
    |W y * (Real.cos (inner ℝ q y) - Real.cos (inner ℝ p y))|
      ≤ (‖y‖ * |W y|) * ‖p - q‖ := by
  have hcos : |Real.cos (inner ℝ q y) - Real.cos (inner ℝ p y)|
      ≤ |inner ℝ q y - inner ℝ p y| := by
    have h := Real.lipschitzWith_cos.dist_le_mul (inner ℝ q y) (inner ℝ p y)
    simpa [Real.dist_eq] using h
  calc |W y * (Real.cos (inner ℝ q y) - Real.cos (inner ℝ p y))|
      = |W y| * |Real.cos (inner ℝ q y) - Real.cos (inner ℝ p y)| := abs_mul _ _
    _ ≤ |W y| * |inner ℝ q y - inner ℝ p y| :=
        mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
    _ = |W y| * |inner ℝ (q - p) y| := by rw [inner_sub_left]
    _ ≤ |W y| * (‖q - p‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (q - p) y) (abs_nonneg _)
    _ = (‖y‖ * |W y|) * ‖p - q‖ := by rw [norm_sub_rev]; ring

/-- **`Ŵ` is Lipschitz with constant `∫ ‖y‖ |W y|`.** -/
private lemma dist_chat_le {W : ℝ³ → ℝ} (hint : Integrable W)
    (h1 : Integrable fun y : ℝ³ => ‖y‖ * |W y|) (p q : ℝ³) :
    dist (Work.BoseFixR.chat W p) (Work.BoseFixR.chat W q)
      ≤ (∫ y : ℝ³, ‖y‖ * |W y|) * dist p q := by
  rw [Real.dist_eq, dist_eq_norm, abs_sub_comm, chat_sub_eq hint p q]
  calc |∫ y : ℝ³, W y * (Real.cos (inner ℝ q y) - Real.cos (inner ℝ p y))|
      ≤ ∫ y : ℝ³, |W y * (Real.cos (inner ℝ q y) - Real.cos (inner ℝ p y))| := by
        simpa [Real.norm_eq_abs] using norm_integral_le_integral_norm
          (fun y : ℝ³ => W y * (Real.cos (inner ℝ q y) - Real.cos (inner ℝ p y)))
    _ ≤ ∫ y : ℝ³, (‖y‖ * |W y|) * ‖p - q‖ := by
        refine integral_mono_of_nonneg
          (Filter.Eventually.of_forall fun y => abs_nonneg _) (h1.mul_const _) ?_
        exact Filter.Eventually.of_forall fun y => abs_mul_cos_sub_le p q y
    _ = (∫ y : ℝ³, ‖y‖ * |W y|) * ‖p - q‖ := integral_mul_const _ _

theorem fderiv_chat_bound {W : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hint : MeasureTheory.Integrable W)
    (h1 : MeasureTheory.Integrable fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖ * |W y|)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ‖fderiv ℝ (Work.BoseFixR.chat W) p‖
      ≤ ∫ y : EuclideanSpace ℝ (Fin 3), ‖y‖ * |W y| := by
  have hK : 0 ≤ ∫ y : ℝ³, ‖y‖ * |W y| :=
    integral_nonneg fun y => mul_nonneg (norm_nonneg _) (abs_nonneg _)
  have hlip : LipschitzWith (Real.toNNReal (∫ y : ℝ³, ‖y‖ * |W y|))
      (Work.BoseFixR.chat W) :=
    LipschitzWith.of_dist_le' (dist_chat_le hint h1)
  by_cases hd : DifferentiableAt ℝ (Work.BoseFixR.chat W) p
  · have h := HasFDerivAt.le_of_lipschitz hd.hasFDerivAt hlip
    rwa [Real.coe_toNNReal _ hK] at h
  · rw [fderiv_zero_of_not_differentiableAt hd, norm_zero]
    exact hK

end Work.BoseB7AK.W1rows
