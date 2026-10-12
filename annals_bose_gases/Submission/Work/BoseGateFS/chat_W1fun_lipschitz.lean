import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.MeasureTheory.Function.StronglyMeasurable.Inner
import Submission.Work.BoseB7AK.W1rows.W1hat_grad_le
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseGateFS.chat_W1fun_lipschitz` — `Ŵ₁` is Lipschitz with constant `16π R (a v)`

`Ŵ₁ = chat (W1fun v h ℓ)` is the `p`-convention Fourier transform (real part) of the
renormalised kernel `W₁ = wScaled ℓ (g₀ v h)`.  Via the cosine representation
(`Work.BoseB7AK.W1low.chat_eq_integral_cos`)

`Ŵ₁(k) = ∫ y, W₁(y) cos ⟪k,y⟫ dy`

the Lipschitz bound is immediate:

`|Ŵ₁(p) − Ŵ₁(q)| ≤ ∫ y, |W₁ y| |cos⟪p,y⟫ − cos⟪q,y⟫| dy
 ≤ ∫ y, |W₁ y| |⟪p−q,y⟫| dy ≤ (∫ y, ‖y‖|W₁ y|) ‖p−q‖`,

and since `W₁` vanishes off `ball 0 R` (it is `wScaled ℓ (g₀ v h)` and `g₀` vanishes there),
`∫ ‖y‖|W₁| ≤ R ∫ |W₁| ≤ R · 16π (a v)` by `wScaled_g0_abs_integral_le`.

Note this route needs **no differentiability** of `Ŵ₁` (which the mean-value-theorem route
through `fderiv_chat_W1fun_le` would); the cosine form of the transform gives the estimate
directly.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseGateFS

/-- The cosine integrand of `chat W k` is integrable when `W` is (dominated by `|W|`). -/
private lemma integrable_mul_cos {W : EuclideanSpace ℝ (Fin 3) → ℝ} (hint : MeasureTheory.Integrable W)
    (k : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable fun y : EuclideanSpace ℝ (Fin 3) => W y * Real.cos (inner ℝ k y) :=
  hint.mul_bdd (by fun_prop) (Filter.Eventually.of_forall fun y => by
    rw [Real.norm_eq_abs]
    exact Real.abs_cos_le_one _)

/-- **Pointwise Lipschitz estimate for the cosine kernel:**
`|W y (cos⟪p,y⟫ − cos⟪q,y⟫)| ≤ (‖y‖ |W y|) ‖p − q‖`. -/
private lemma abs_mul_cos_sub_le {W : EuclideanSpace ℝ (Fin 3) → ℝ} (p q : EuclideanSpace ℝ (Fin 3))
    (y : EuclideanSpace ℝ (Fin 3)) :
    |W y * Real.cos (inner ℝ p y) - W y * Real.cos (inner ℝ q y)|
      ≤ (‖y‖ * |W y|) * ‖p - q‖ := by
  have hcos : |Real.cos (inner ℝ p y) - Real.cos (inner ℝ q y)|
      ≤ |inner ℝ p y - inner ℝ q y| := by
    have h := Real.lipschitzWith_cos.dist_le_mul (inner ℝ p y) (inner ℝ q y)
    simpa [Real.dist_eq] using h
  have hfac : W y * Real.cos (inner ℝ p y) - W y * Real.cos (inner ℝ q y)
      = W y * (Real.cos (inner ℝ p y) - Real.cos (inner ℝ q y)) := by ring
  calc |W y * Real.cos (inner ℝ p y) - W y * Real.cos (inner ℝ q y)|
      = |W y| * |Real.cos (inner ℝ p y) - Real.cos (inner ℝ q y)| := by rw [hfac, abs_mul]
    _ ≤ |W y| * |inner ℝ p y - inner ℝ q y| :=
        mul_le_mul_of_nonneg_left hcos (abs_nonneg _)
    _ = |W y| * |inner ℝ (p - q) y| := by rw [inner_sub_left]
    _ ≤ |W y| * (‖p - q‖ * ‖y‖) :=
        mul_le_mul_of_nonneg_left (abs_real_inner_le_norm (p - q) y) (abs_nonneg _)
    _ = (‖y‖ * |W y|) * ‖p - q‖ := by ring

/-- **The Fourier transform of an `L¹` function supported in `ball 0 R` is `R∫|W|`-Lipschitz.**
`|chat W p − chat W q| ≤ R (∫ |W|) ‖p − q‖`, from the cosine representation of `chat`. -/
lemma chat_lipschitz_of_support {W : EuclideanSpace ℝ (Fin 3) → ℝ} {R : ℝ}
    (hint : MeasureTheory.Integrable W) (hsupp : ∀ x, W x ≠ 0 → ‖x‖ < R)
    (p q : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseFixR.chat W p - Work.BoseFixR.chat W q| ≤ R * (∫ x, |W x|) * ‖p - q‖ := by
  have h1 : MeasureTheory.Integrable fun y : EuclideanSpace ℝ (Fin 3) => ‖y‖ * |W y| := by
    refine MeasureTheory.Integrable.mono' (hint.abs.const_mul R) ?_ ?_
    · exact (continuous_norm.aestronglyMeasurable).mul hint.aestronglyMeasurable.norm
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg x) (abs_nonneg _))]
      by_cases hx : W x = 0
      · simp [hx]
      · exact mul_le_mul_of_nonneg_right (hsupp x hx).le (abs_nonneg _)
  have hmain : |Work.BoseFixR.chat W p - Work.BoseFixR.chat W q|
      ≤ (∫ y : EuclideanSpace ℝ (Fin 3), ‖y‖ * |W y|) * ‖p - q‖ := by
    rw [Work.BoseB7AK.W1low.chat_eq_integral_cos hint p,
      Work.BoseB7AK.W1low.chat_eq_integral_cos hint q]
    calc |(∫ y : EuclideanSpace ℝ (Fin 3), W y * Real.cos (inner ℝ p y))
            - ∫ y, W y * Real.cos (inner ℝ q y)|
        = |∫ y : EuclideanSpace ℝ (Fin 3),
            (W y * Real.cos (inner ℝ p y) - W y * Real.cos (inner ℝ q y))| := by
          rw [integral_sub (integrable_mul_cos hint p) (integrable_mul_cos hint q)]
      _ ≤ ∫ y : EuclideanSpace ℝ (Fin 3),
            |W y * Real.cos (inner ℝ p y) - W y * Real.cos (inner ℝ q y)| := by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm
            (fun y : EuclideanSpace ℝ (Fin 3) =>
              W y * Real.cos (inner ℝ p y) - W y * Real.cos (inner ℝ q y))
      _ ≤ ∫ y : EuclideanSpace ℝ (Fin 3), (‖y‖ * |W y|) * ‖p - q‖ :=
          integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => abs_nonneg _)
            (h1.mul_const _) (Filter.Eventually.of_forall fun y => abs_mul_cos_sub_le p q y)
      _ = (∫ y : EuclideanSpace ℝ (Fin 3), ‖y‖ * |W y|) * ‖p - q‖ := integral_mul_const _ _
  -- the support bound `∫ ‖y‖|W| ≤ R ∫ |W|`
  have hdom : ∀ y : EuclideanSpace ℝ (Fin 3), ‖y‖ * |W y| ≤ R * |W y| := by
    intro y
    by_cases hy : W y = 0
    · simp [hy]
    · exact mul_le_mul_of_nonneg_right (hsupp y hy).le (abs_nonneg _)
  have hleR : (∫ y : EuclideanSpace ℝ (Fin 3), ‖y‖ * |W y|) ≤ R * ∫ y, |W y| := by
    calc (∫ y : EuclideanSpace ℝ (Fin 3), ‖y‖ * |W y|) ≤ ∫ y, R * |W y| :=
          integral_mono_ae h1 (hint.abs.const_mul R) (Filter.Eventually.of_forall hdom)
      _ = R * ∫ y, |W y| := integral_const_mul R _
  calc |Work.BoseFixR.chat W p - Work.BoseFixR.chat W q|
      ≤ (∫ y : EuclideanSpace ℝ (Fin 3), ‖y‖ * |W y|) * ‖p - q‖ := hmain
    _ ≤ (R * ∫ y, |W y|) * ‖p - q‖ :=
        mul_le_mul_of_nonneg_right hleR (norm_nonneg _)
    _ = R * (∫ x, |W x|) * ‖p - q‖ := by ring

theorem chat_W1fun_lipschitz {v : EuclideanSpace ℝ (Fin 3) → ℝ} {h : Work.UBB.ScatSol v}
    {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0) (p q : EuclideanSpace ℝ (Fin 3)) :
    |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
      - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q|
      ≤ 16 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖ := by
  -- `W₁ = wScaled ℓ (g₀ v h)` is `L¹` in the dilute regime.
  have hW1int : MeasureTheory.Integrable (fun x : EuclideanSpace ℝ (Fin 3) =>
      Work.BoseFixR.W1fun v h ℓ x) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  -- `W₁` vanishes outside `ball 0 R`, because its numerator `g₀` does.
  have hsupp : ∀ x : EuclideanSpace ℝ (Fin 3), Work.BoseFixR.W1fun v h ℓ x ≠ 0 → ‖x‖ < R := by
    intro x hx
    refine lt_of_not_ge (fun hge => hx ?_)
    have hz : Submission.BoseGases.g0 v h x = 0 :=
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp hge h
    simp [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, hz]
  -- the real-space mass bound `∫|W₁| ≤ 16π (a v)`
  have hle3 : (∫ x : EuclideanSpace ℝ (Fin 3), |Work.BoseFixR.W1fun v h ℓ x|)
      ≤ 16 * Real.pi * _root_.BoseGases.a v :=
    Submission.BoseGases.wScaled_g0_abs_integral_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ
  calc |Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) p
        - Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ) q|
      ≤ R * (∫ x : EuclideanSpace ℝ (Fin 3), |Work.BoseFixR.W1fun v h ℓ x|) * ‖p - q‖ :=
        chat_lipschitz_of_support hW1int hsupp p q
    _ ≤ R * (16 * Real.pi * _root_.BoseGases.a v) * ‖p - q‖ :=
        mul_le_mul_of_nonneg_right
          (mul_le_mul_of_nonneg_left hle3 hR.le) (norm_nonneg _)
    _ = 16 * Real.pi * R * _root_.BoseGases.a v * ‖p - q‖ := by ring

end Work.BoseGateFS
