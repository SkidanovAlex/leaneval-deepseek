import Mathlib
import Submission.Work.CR.Flat.Cauchy.openSolDefs
import Submission.Work.CR.Flat.Cauchy.integral_norm_rpow_ball
import Submission.Work.CR.Flat.Cauchy.integrableOn_norm_rpow_ball

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set Filter

namespace Work.CR.Flat.Cauchy

/-- The map `w ↦ Function.update 0 j w` is continuous on `Fin n → ℂ`. -/
lemma continuous_update_zero {n : ℕ} (j : Fin n) :
    Continuous (fun w : ℂ => Function.update (0 : Fin n → ℂ) j w) := by
  rw [continuous_pi_iff]
  intro i
  simp only [Function.update_apply]
  by_cases h : i = j
  · simp only [h, ite_true]; exact continuous_id
  · simp only [h, ite_false]; exact continuous_const

/-- The `j`-th slice integrand `w ↦ g (z + w e_j)/w` is integrable on the disc
`‖w‖ < ρ` when `g` is continuous: `g` is bounded on the image of the closed disc
and `‖w‖⁻¹` is integrable on a disc in `ℂ`. -/
lemma integrableOn_dbarTransform_integrand {n : ℕ} (j : Fin n) {ρ : ℝ}
    {g : (Fin n → ℂ) → ℂ} (hg : Continuous g) (z : Fin n → ℂ) :
    IntegrableOn (fun w : ℂ => g (z + Function.update (0 : Fin n → ℂ) j w) / w)
      (Metric.ball (0 : ℂ) ρ) := by
  have hcont : Continuous fun w : ℂ => g (z + Function.update (0 : Fin n → ℂ) j w) :=
    hg.comp (continuous_const.add (continuous_update_zero j))
  obtain ⟨M, hM⟩ :=
    (isCompact_closedBall (0 : ℂ) ρ).exists_bound_of_continuousOn hcont.continuousOn
  have hmaj : IntegrableOn (fun w : ℂ => M * ‖w‖ ^ (-1 : ℝ)) (Metric.ball (0 : ℂ) ρ) :=
    (integrableOn_norm_rpow_ball (ρ := ρ) (s := -1) (by norm_num)).const_mul M
  refine hmaj.mono' ?_ ?_
  · exact (hcont.measurable.div measurable_id).aestronglyMeasurable
  · rw [MeasureTheory.ae_restrict_iff' measurableSet_ball]
    filter_upwards with w hw
    rw [norm_div]
    calc ‖g (z + Function.update (0 : Fin n → ℂ) j w)‖ / ‖w‖
        ≤ M / ‖w‖ :=
          div_le_div_of_nonneg_right (hM w (Metric.ball_subset_closedBall hw)) (norm_nonneg w)
      _ = M * ‖w‖ ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv]

/-- Pointwise bound for the unsubtracted Cauchy kernel: under the support and
size hypotheses of `dbarTransform_basic`, one has `‖g (z + w e_j)‖ ≤ A` for
every `w`, because `w ↦ z + w e_j` either stays on the line through `z` with
`‖·‖_j ≤ b` (where the hypothesis applies) or leaves the support of `g`. -/
lemma dbarTransform_integrand_bound {n : ℕ} {b A : ℝ} (hb : 0 ≤ b) {j : Fin n}
    {g : (Fin n → ℂ) → ℂ} (hsupp : ∀ y, b ≤ ‖y j‖ → g y = 0) (z : Fin n → ℂ)
    (hbd : ∀ y, (∀ l, l ≠ j → y l = z l) → ‖y j‖ ≤ b → ‖g y‖ ≤ A) :
    ∀ w : ℂ, ‖g (z + Function.update (0 : Fin n → ℂ) j w)‖ ≤ A := by
  have hA : 0 ≤ A := by
    have h1 : ‖g (Function.update z j 0)‖ ≤ A :=
      hbd (Function.update z j 0)
        (fun l hl => Function.update_of_ne hl (0 : ℂ) z)
        (by rw [Function.update_self, norm_zero]; exact hb)
    exact le_trans (norm_nonneg _) h1
  intro w
  by_cases hle : ‖(z + Function.update (0 : Fin n → ℂ) j w) j‖ ≤ b
  · exact hbd _ (fun l hl => by simp [Pi.add_apply, hl]) hle
  · push Not at hle
    rw [hsupp _ hle.le, norm_zero]
    exact hA

theorem dbarTransform_basic {n : ℕ} {ρ b : ℝ} (hρ : 0 < ρ) (hb : 0 ≤ b) {j : Fin n} :
    (∀ {g : (Fin n → ℂ) → ℂ}, Continuous g → (∀ y, b ≤ ‖y j‖ → g y = 0) →
      ∀ (A : ℝ) (z : Fin n → ℂ), (∀ y, (∀ l, l ≠ j → y l = z l) → ‖y j‖ ≤ b → ‖g y‖ ≤ A) →
        ‖dbarTransform ρ j g z‖ ≤ 2 * ρ * A) ∧
    (∀ {g : (Fin n → ℂ) → ℂ}, Continuous g → (∀ y, b ≤ ‖y j‖ → g y = 0) →
      ∀ (α H : ℝ) (x y : Fin n → ℂ),
        (∀ a a', (∀ l, l ≠ j → a l = x l) → (∀ l, l ≠ j → a' l = y l) →
          ‖g a - g a'‖ ≤ H * ‖a - a'‖ ^ α) →
        ‖dbarTransform ρ j g x - dbarTransform ρ j g y‖ ≤ 2 * ρ * H * ‖x - y‖ ^ α) ∧
    (∀ {g g' : (Fin n → ℂ) → ℂ}, Continuous g → Continuous g' →
      (∀ y, b ≤ ‖y j‖ → g y = 0) → (∀ y, b ≤ ‖y j‖ → g' y = 0) → ∀ z : Fin n → ℂ,
        dbarTransform ρ j (fun y => g y - g' y) z = dbarTransform ρ j g z - dbarTransform ρ j g' z) := by
  have hpi : ‖((Real.pi : ℂ))⁻¹‖ = Real.pi⁻¹ := by
    rw [norm_inv, Complex.norm_real, Real.norm_of_nonneg Real.pi_pos.le]
  have hpi2 : Real.pi⁻¹ * (2 * Real.pi) = 2 := by
    rw [mul_comm (2 : ℝ) Real.pi, ← mul_assoc, inv_mul_cancel₀ Real.pi_ne_zero, one_mul]
  refine ⟨?_, ?_, ?_⟩
  · -- part 1: uniform bound `‖g‖ ≤ A` on the slice
    intro g hg hsupp A z hbd
    have hpt := dbarTransform_integrand_bound hb hsupp z hbd
    have hmaj : IntegrableOn (fun w : ℂ => A * ‖w‖ ^ (-1 : ℝ)) (Metric.ball (0 : ℂ) ρ) :=
      (integrableOn_norm_rpow_ball (ρ := ρ) (s := -1) (by norm_num)).const_mul A
    have hbound : ‖∫ w in Metric.ball (0 : ℂ) ρ,
          g (z + Function.update (0 : Fin n → ℂ) j w) / w‖
        ≤ ∫ w in Metric.ball (0 : ℂ) ρ, A * ‖w‖ ^ (-1 : ℝ) :=
      norm_integral_le_of_norm_le hmaj (Eventually.of_forall fun w => by
        rw [norm_div]
        calc ‖g (z + Function.update (0 : Fin n → ℂ) j w)‖ / ‖w‖ ≤ A / ‖w‖ :=
              div_le_div_of_nonneg_right (hpt w) (norm_nonneg w)
          _ = A * ‖w‖ ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv])
    have hval : (∫ w in Metric.ball (0 : ℂ) ρ, A * ‖w‖ ^ (-1 : ℝ))
        = A * (2 * Real.pi * ρ) := by
      rw [integral_const_mul, integral_norm_rpow_ball hρ (by norm_num : (-2 : ℝ) < -1)]
      rw [show (-1 : ℝ) + 2 = 1 by norm_num, Real.rpow_one, div_one]
    calc ‖dbarTransform ρ j g z‖
        = ‖((Real.pi : ℂ))⁻¹‖ * ‖∫ w in Metric.ball (0 : ℂ) ρ,
            g (z + Function.update (0 : Fin n → ℂ) j w) / w‖ := by
          simp only [dbarTransform, norm_mul, norm_neg]
      _ = Real.pi⁻¹ * ‖∫ w in Metric.ball (0 : ℂ) ρ,
            g (z + Function.update (0 : Fin n → ℂ) j w) / w‖ := by rw [hpi]
      _ ≤ Real.pi⁻¹ * (∫ w in Metric.ball (0 : ℂ) ρ, A * ‖w‖ ^ (-1 : ℝ)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = Real.pi⁻¹ * (A * (2 * Real.pi * ρ)) := by rw [hval]
      _ = 2 * ρ * A := by
          rw [show Real.pi⁻¹ * (A * (2 * Real.pi * ρ))
              = (Real.pi⁻¹ * (2 * Real.pi)) * (A * ρ) by ring, hpi2]
          ring
  · -- part 2: Hölder estimate
    intro g hg hsupp α H x y hholder
    have hGx : IntegrableOn (fun w : ℂ => g (x + Function.update (0 : Fin n → ℂ) j w) / w)
        (Metric.ball (0 : ℂ) ρ) := integrableOn_dbarTransform_integrand j hg x
    have hGy : IntegrableOn (fun w : ℂ => g (y + Function.update (0 : Fin n → ℂ) j w) / w)
        (Metric.ball (0 : ℂ) ρ) := integrableOn_dbarTransform_integrand j hg y
    have hdiff : dbarTransform ρ j g x - dbarTransform ρ j g y
        = -((Real.pi : ℂ))⁻¹ * ∫ w in Metric.ball (0 : ℂ) ρ,
            (g (x + Function.update (0 : Fin n → ℂ) j w)
              - g (y + Function.update (0 : Fin n → ℂ) j w)) / w := by
      have key : (∫ w in Metric.ball (0 : ℂ) ρ,
              g (x + Function.update (0 : Fin n → ℂ) j w) / w)
            - (∫ w in Metric.ball (0 : ℂ) ρ,
              g (y + Function.update (0 : Fin n → ℂ) j w) / w)
          = ∫ w in Metric.ball (0 : ℂ) ρ,
              (g (x + Function.update (0 : Fin n → ℂ) j w)
                - g (y + Function.update (0 : Fin n → ℂ) j w)) / w := by
        rw [← integral_sub hGx hGy]
        apply setIntegral_congr_fun measurableSet_ball
        intro w _
        show g (x + Function.update (0 : Fin n → ℂ) j w) / w
            - g (y + Function.update (0 : Fin n → ℂ) j w) / w
          = (g (x + Function.update (0 : Fin n → ℂ) j w)
              - g (y + Function.update (0 : Fin n → ℂ) j w)) / w
        rw [sub_div]
      calc dbarTransform ρ j g x - dbarTransform ρ j g y
          = -((Real.pi : ℂ))⁻¹ *
              ((∫ w in Metric.ball (0 : ℂ) ρ,
                  g (x + Function.update (0 : Fin n → ℂ) j w) / w)
                - (∫ w in Metric.ball (0 : ℂ) ρ,
                  g (y + Function.update (0 : Fin n → ℂ) j w) / w)) := by
            rw [dbarTransform, dbarTransform]; ring
        _ = -((Real.pi : ℂ))⁻¹ * ∫ w in Metric.ball (0 : ℂ) ρ,
              (g (x + Function.update (0 : Fin n → ℂ) j w)
                - g (y + Function.update (0 : Fin n → ℂ) j w)) / w := by rw [key]
    have hpt : ∀ w : ℂ,
        ‖(g (x + Function.update (0 : Fin n → ℂ) j w)
          - g (y + Function.update (0 : Fin n → ℂ) j w)) / w‖
          ≤ H * ‖x - y‖ ^ α * ‖w‖ ^ (-1 : ℝ) := by
      intro w
      rw [norm_div]
      have hh : ‖g (x + Function.update (0 : Fin n → ℂ) j w)
          - g (y + Function.update (0 : Fin n → ℂ) j w)‖ ≤ H * ‖x - y‖ ^ α := by
        have h1 : ∀ l, l ≠ j → (x + Function.update (0 : Fin n → ℂ) j w) l = x l :=
          fun l hl => by simp [Pi.add_apply, hl]
        have h2 : ∀ l, l ≠ j → (y + Function.update (0 : Fin n → ℂ) j w) l = y l :=
          fun l hl => by simp [Pi.add_apply, hl]
        have h := hholder (x + Function.update (0 : Fin n → ℂ) j w)
          (y + Function.update (0 : Fin n → ℂ) j w) h1 h2
        rwa [add_sub_add_right_eq_sub] at h
      calc ‖g (x + Function.update (0 : Fin n → ℂ) j w)
            - g (y + Function.update (0 : Fin n → ℂ) j w)‖ / ‖w‖
          ≤ (H * ‖x - y‖ ^ α) / ‖w‖ :=
            div_le_div_of_nonneg_right hh (norm_nonneg w)
        _ = H * ‖x - y‖ ^ α * ‖w‖ ^ (-1 : ℝ) := by rw [Real.rpow_neg_one, div_eq_mul_inv]
    have hmaj : IntegrableOn (fun w : ℂ => H * ‖x - y‖ ^ α * ‖w‖ ^ (-1 : ℝ))
        (Metric.ball (0 : ℂ) ρ) :=
      (integrableOn_norm_rpow_ball (ρ := ρ) (s := -1) (by norm_num)).const_mul (H * ‖x - y‖ ^ α)
    have hbound : ‖∫ w in Metric.ball (0 : ℂ) ρ,
          (g (x + Function.update (0 : Fin n → ℂ) j w)
            - g (y + Function.update (0 : Fin n → ℂ) j w)) / w‖
        ≤ ∫ w in Metric.ball (0 : ℂ) ρ, H * ‖x - y‖ ^ α * ‖w‖ ^ (-1 : ℝ) :=
      norm_integral_le_of_norm_le hmaj (Eventually.of_forall hpt)
    have hval : (∫ w in Metric.ball (0 : ℂ) ρ, H * ‖x - y‖ ^ α * ‖w‖ ^ (-1 : ℝ))
        = H * ‖x - y‖ ^ α * (2 * Real.pi * ρ) := by
      rw [integral_const_mul, integral_norm_rpow_ball hρ (by norm_num : (-2 : ℝ) < -1)]
      rw [show (-1 : ℝ) + 2 = 1 by norm_num, Real.rpow_one, div_one]
    calc ‖dbarTransform ρ j g x - dbarTransform ρ j g y‖
        = ‖((Real.pi : ℂ))⁻¹‖ * ‖∫ w in Metric.ball (0 : ℂ) ρ,
            (g (x + Function.update (0 : Fin n → ℂ) j w)
              - g (y + Function.update (0 : Fin n → ℂ) j w)) / w‖ := by
          rw [hdiff, norm_mul, norm_neg]
      _ = Real.pi⁻¹ * ‖∫ w in Metric.ball (0 : ℂ) ρ,
            (g (x + Function.update (0 : Fin n → ℂ) j w)
              - g (y + Function.update (0 : Fin n → ℂ) j w)) / w‖ := by rw [hpi]
      _ ≤ Real.pi⁻¹ * (∫ w in Metric.ball (0 : ℂ) ρ, H * ‖x - y‖ ^ α * ‖w‖ ^ (-1 : ℝ)) :=
          mul_le_mul_of_nonneg_left hbound (by positivity)
      _ = Real.pi⁻¹ * (H * ‖x - y‖ ^ α * (2 * Real.pi * ρ)) := by rw [hval]
      _ = 2 * ρ * H * ‖x - y‖ ^ α := by
          rw [show Real.pi⁻¹ * (H * ‖x - y‖ ^ α * (2 * Real.pi * ρ))
              = (Real.pi⁻¹ * (2 * Real.pi)) * (H * ‖x - y‖ ^ α * ρ) by ring, hpi2]
          ring
  · -- part 3: linearity of the integral
    intro g g' hg hg' hsupp hsupp' z
    have hG : IntegrableOn (fun w : ℂ => g (z + Function.update (0 : Fin n → ℂ) j w) / w)
        (Metric.ball (0 : ℂ) ρ) := integrableOn_dbarTransform_integrand j hg z
    have hG' : IntegrableOn (fun w : ℂ => g' (z + Function.update (0 : Fin n → ℂ) j w) / w)
        (Metric.ball (0 : ℂ) ρ) := integrableOn_dbarTransform_integrand j hg' z
    have hGA : (∫ w in Metric.ball (0 : ℂ) ρ,
          ((fun y : Fin n → ℂ => g y - g' y) (z + Function.update (0 : Fin n → ℂ) j w)) / w)
        = (∫ w in Metric.ball (0 : ℂ) ρ, g (z + Function.update (0 : Fin n → ℂ) j w) / w)
          - (∫ w in Metric.ball (0 : ℂ) ρ, g' (z + Function.update (0 : Fin n → ℂ) j w) / w) := by
      rw [← integral_sub hG hG']
      apply setIntegral_congr_fun measurableSet_ball
      intro w _
      show (g (z + Function.update (0 : Fin n → ℂ) j w)
              - g' (z + Function.update (0 : Fin n → ℂ) j w)) / w
        = g (z + Function.update (0 : Fin n → ℂ) j w) / w
            - g' (z + Function.update (0 : Fin n → ℂ) j w) / w
      rw [sub_div]
    rw [dbarTransform, dbarTransform, dbarTransform, hGA]
    ring

end Work.CR.Flat.Cauchy
