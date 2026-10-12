import ChallengeDeps
import Mathlib.Tactic.Have
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB7AK.W1rows.W1hat_abs_le
import Submission.Work.BoseB7AK.W1rows.fderiv_chat_bound
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7AK.W1rows.W1hat_grad_le` — the gradient row of FS `eq:W1estimate`

For the corpus kernel `Ŵ₁ = chat (W1fun v h ℓ)` (`W₁ = g₀/(χ⋆χ)(·/ℓ)`,
`g₀ = v(1−w₀)`) we prove

    ‖∇Ŵ₁(p)‖ ≤ 16 π R · a v · (1 + ‖p‖)                       (all `p`),

the `hW1grad` row of `Work.BoseK15.K15Input` (`FINDING_W1rows.md` §3), with the
corpus's own diluteness hypotheses (`v ≥ 0`, radial, `tsupport v ⊆ ball 0 R`,
`ScatSol v`, `R ≤ ℓ·chiR0`) and **no regularity of `v`**.

## Route

`Ŵ₁` is the cosine transform `Ŵ₁(k) = ∫ y, W₁(y) cos⟪k,y⟫ dy`
(`Work.BoseB7AK.W1low.chat_eq_integral_cos`), whence (the already proved
`fderiv_chat_bound`)

    ‖∇Ŵ₁(p)‖ ≤ ∫ y, ‖y‖ |W₁(y)| dy

without any smoothness hypothesis (`Ŵ₁` is Lipschitz with constant
`∫‖y‖|W₁|`, and at non-differentiability points both sides vanish trivially).

The first moment is then controlled **by support alone**: `W₁` vanishes off
`ball 0 R` (its numerator `g₀` does, `g0_zero_of_norm_ge`), so

    ∫ y, ‖y‖ |W₁(y)| dy ≤ R ∫ y, |W₁(y)| dy ≤ R · 16 π (a v),

the last step being `wScaled_g0_abs_integral_le`.  Finally `0 ≤ a v` is *not*
assumed: it follows from `0 ≤ ∫|W₁| ≤ 16π(a v)` (with `π > 0`), and the target
has the harmless factor `(1+‖p‖) ≥ 1`.
-/

namespace Work.BoseB7AK.W1rows

noncomputable section

open MeasureTheory
open scoped Real Topology

-- `ℝ³` is the *global* `notation "ℝ³" => EuclideanSpace ℝ (Fin 3)` of the
-- corpus (via `Submission.Work.BoseFixR.Defs`); no local redeclaration, which
-- would make the term ambiguous.

theorem W1hat_grad_le {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ℓ : ℝ} (hR : 0 < R) (hℓ : 0 < ℓ)
    (hv_nonneg : ∀ x : EuclideanSpace ℝ (Fin 3), 0 ≤ v x)
    (hvrad : _root_.BoseGases.IsRadial v)
    (hv_supp : tsupport v ⊆ Metric.ball 0 R)
    (h : Work.UBB.ScatSol v) (hRℓ : R ≤ ℓ * Submission.BoseGases.chiR0)
    (p : EuclideanSpace ℝ (Fin 3)) :
    ‖fderiv ℝ (Work.BoseFixR.chat (Work.BoseFixR.W1fun v h ℓ)) p‖
      ≤ 16 * Real.pi * R * _root_.BoseGases.a v * (1 + ‖p‖) := by
  -- `W₁ = wScaled ℓ (g₀ v h)` is `L¹` in the dilute regime.
  have hW1int : MeasureTheory.Integrable (fun x : ℝ³ =>
      Work.BoseFixR.W1fun v h ℓ x) :=
    Submission.BoseGases.wScaled_g0_integrable hR hv_supp h hℓ hRℓ
  -- `W₁` vanishes outside `ball 0 R`, because its numerator `g₀` does.
  have hsupp : ∀ x : ℝ³, Work.BoseFixR.W1fun v h ℓ x ≠ 0 → ‖x‖ < R := by
    intro x hx
    refine lt_of_not_ge (fun hge => hx ?_)
    have hz : Submission.BoseGases.g0 v h x = 0 :=
      Submission.BoseGases.g0_zero_of_norm_ge hv_supp hge h
    simp [Work.BoseFixR.W1fun, Submission.BoseGases.wScaled, hz]
  -- Hence the pointwise domination by the `L¹` mass `R|W₁|`.
  have hdom : ∀ x : ℝ³, ‖x‖ * |Work.BoseFixR.W1fun v h ℓ x|
      ≤ R * |Work.BoseFixR.W1fun v h ℓ x| := by
    intro x
    by_cases hx : Work.BoseFixR.W1fun v h ℓ x = 0
    · simp [hx]
    · exact mul_le_mul_of_nonneg_right (hsupp x hx).le (abs_nonneg _)
  have hfirst : MeasureTheory.Integrable (fun x : ℝ³ =>
      ‖x‖ * |Work.BoseFixR.W1fun v h ℓ x|) := by
    refine MeasureTheory.Integrable.mono' (hW1int.abs.const_mul R) ?_ ?_
    · exact (continuous_norm.aestronglyMeasurable).mul hW1int.aestronglyMeasurable.norm
    · filter_upwards with x
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (norm_nonneg x) (abs_nonneg _))]
      exact hdom x
  -- The two numerical rows.
  have hle1 : (∫ x : ℝ³, ‖x‖ * |Work.BoseFixR.W1fun v h ℓ x|)
      ≤ ∫ x : ℝ³, R * |Work.BoseFixR.W1fun v h ℓ x| :=
    MeasureTheory.integral_mono_ae hfirst (hW1int.abs.const_mul R)
      (Filter.Eventually.of_forall hdom)
  have hle2 : (∫ x : ℝ³, R * |Work.BoseFixR.W1fun v h ℓ x|)
      = R * (∫ x : ℝ³, |Work.BoseFixR.W1fun v h ℓ x|) :=
    MeasureTheory.integral_const_mul R _
  have hle3 : (∫ x : ℝ³, |Work.BoseFixR.W1fun v h ℓ x|)
      ≤ 16 * Real.pi * _root_.BoseGases.a v :=
    Submission.BoseGases.wScaled_g0_abs_integral_le hR hv_nonneg hvrad hv_supp h hℓ hRℓ
  have hnonneg : (0 : ℝ) ≤ ∫ x : ℝ³, |Work.BoseFixR.W1fun v h ℓ x| :=
    MeasureTheory.integral_nonneg (fun x => abs_nonneg _)
  -- `0 ≤ a v`, from `0 ≤ ∫|W₁| ≤ 16π(a v)`.
  have ha : 0 ≤ _root_.BoseGases.a v := by
    have h0 : (0 : ℝ) ≤ 16 * Real.pi * _root_.BoseGases.a v := le_trans hnonneg hle3
    have h0' : (0 : ℝ) ≤ _root_.BoseGases.a v * (16 * Real.pi) := by
      rw [mul_comm]; exact h0
    exact nonneg_of_mul_nonneg_left h0' (by positivity)
  refine le_trans (fderiv_chat_bound hW1int hfirst p) ?_
  have hy : (0 : ℝ) ≤ 16 * Real.pi * R * _root_.BoseGases.a v :=
    mul_nonneg (mul_nonneg (mul_nonneg (by norm_num) Real.pi_pos.le) hR.le) ha
  calc (∫ x : ℝ³, ‖x‖ * |Work.BoseFixR.W1fun v h ℓ x|)
      ≤ R * (∫ x : ℝ³, |Work.BoseFixR.W1fun v h ℓ x|) := by
        rw [← hle2]; exact hle1
    _ ≤ R * (16 * Real.pi * _root_.BoseGases.a v) :=
        mul_le_mul_of_nonneg_left hle3 hR.le
    _ = 16 * Real.pi * R * _root_.BoseGases.a v := by ring
    _ ≤ 16 * Real.pi * R * _root_.BoseGases.a v * (1 + ‖p‖) := by
        have h1 : (1 : ℝ) ≤ 1 + ‖p‖ := by linarith [norm_nonneg p]
        calc 16 * Real.pi * R * _root_.BoseGases.a v
            = (16 * Real.pi * R * _root_.BoseGases.a v) * 1 := (mul_one _).symm
          _ ≤ (16 * Real.pi * R * _root_.BoseGases.a v) * (1 + ‖p‖) :=
              mul_le_mul_of_nonneg_left h1 hy

end

end Work.BoseB7AK.W1rows
