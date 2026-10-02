import Mathlib
import Submission.Work.MRMT.Cauchy.Defs
import Submission.Work.MRMT.Beltrami.cauchyTransform_decay

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

namespace Work.MRMT.Found

open MeasureTheory Complex

/-- The Cauchy transform written as an integral over the ball of radius `M` that carries the
support of `ψ`. -/
private lemma cauchyTransform_eq_setIntegral {ψ : ℂ → ℂ} {M : ℝ}
    (hM : ∀ ζ : ℂ, ψ ζ ≠ 0 → ‖ζ‖ ≤ M) (z : ℂ) :
    Work.MRMT.cauchyTransform ψ z
      = Work.MRMT.cauchyConst * ∫ ζ in Metric.closedBall (0 : ℂ) M, ψ ζ / (ζ - z) := by
  rw [Work.MRMT.cauchyTransform]
  congr 1
  exact (setIntegral_eq_integral_of_forall_compl_eq_zero (s := Metric.closedBall (0 : ℂ) M)
    (f := fun ζ => ψ ζ / (ζ - z)) (fun ζ hζ => by
      have h0 : ψ ζ = 0 := by
        by_contra h
        exact hζ (by simpa [Metric.mem_closedBall, dist_zero_right] using hM ζ h)
      simp [h0])).symm

/-- For `ψ` carried by the ball of radius `M` and `‖z‖ > M`, the integrand `ζ ↦ ψ ζ / (ζ - z)`
is integrable on that ball. -/
private lemma integrableOn_div_sub {ψ : ℂ → ℂ} (hψc : Continuous ψ) {M : ℝ}
    (_hM : ∀ ζ : ℂ, ψ ζ ≠ 0 → ‖ζ‖ ≤ M) {z : ℂ} (hz : M < ‖z‖) :
    IntegrableOn (fun ζ : ℂ => ψ ζ / (ζ - z)) (Metric.closedBall (0 : ℂ) M) volume := by
  have hne : ∀ ζ ∈ Metric.closedBall (0 : ℂ) M, ζ - z ≠ 0 := by
    intro ζ hζ
    exact Work.MRMT.Beltrami.decay_sub_ne_zero hz
      (by simpa [Metric.mem_closedBall, dist_zero_right] using hζ)
  exact (hψc.continuousOn.div (continuousOn_id.sub continuousOn_const) hne).integrableOn_compact
    (isCompact_closedBall 0 M)

/-- Pointwise bound on the difference of the two kernels, on the support of `ψ`. -/
private lemma norm_div_sub_sub_le {ψ : ℂ → ℂ} {M : ℝ}
    (hM : ∀ ζ : ℂ, ψ ζ ≠ 0 → ‖ζ‖ ≤ M)
    {z₁ z₂ : ℂ} (hz1₁ : 1 ≤ ‖z₁‖) (hz2₁ : 2 * M ≤ ‖z₁‖)
    (hz1₂ : 1 ≤ ‖z₂‖) (hz2₂ : 2 * M ≤ ‖z₂‖) (ζ : ℂ) :
    ‖ψ ζ / (ζ - z₁) - ψ ζ / (ζ - z₂)‖
      ≤ ‖ψ ζ‖ * (4 * ‖z₁ - z₂‖ / (‖z₁‖ * ‖z₂‖)) := by
  by_cases h : ψ ζ = 0
  · simp [h]
  have hζ : ‖ζ‖ ≤ M := hM ζ h
  have hz₁pos : 0 < ‖z₁‖ := lt_of_lt_of_le one_pos hz1₁
  have hz₂pos : 0 < ‖z₂‖ := lt_of_lt_of_le one_pos hz1₂
  have hhalf1 : ‖z₁‖ / 2 ≤ ‖ζ - z₁‖ := by
    have h1 : ‖z₁‖ - ‖ζ‖ ≤ ‖ζ - z₁‖ := by
      have h2 := norm_sub_norm_le z₁ ζ
      rwa [norm_sub_rev] at h2
    have h3 : M ≤ ‖z₁‖ / 2 := by linarith
    linarith
  have hhalf2 : ‖z₂‖ / 2 ≤ ‖ζ - z₂‖ := by
    have h1 : ‖z₂‖ - ‖ζ‖ ≤ ‖ζ - z₂‖ := by
      have h2 := norm_sub_norm_le z₂ ζ
      rwa [norm_sub_rev] at h2
    have h3 : M ≤ ‖z₂‖ / 2 := by linarith
    linarith
  have hne1 : ζ - z₁ ≠ 0 := fun hh => by
    have : ‖ζ - z₁‖ = 0 := by rw [hh, norm_zero]
    linarith
  have hne2 : ζ - z₂ ≠ 0 := fun hh => by
    have : ‖ζ - z₂‖ = 0 := by rw [hh, norm_zero]
    linarith
  have heq : ψ ζ / (ζ - z₁) - ψ ζ / (ζ - z₂)
      = ψ ζ * (z₁ - z₂) / ((ζ - z₁) * (ζ - z₂)) := by
    field_simp
    ring
  rw [heq, norm_div, norm_mul, norm_mul]
  calc ‖ψ ζ‖ * ‖z₁ - z₂‖ / (‖ζ - z₁‖ * ‖ζ - z₂‖)
      ≤ ‖ψ ζ‖ * ‖z₁ - z₂‖ / ((‖z₁‖ / 2) * (‖z₂‖ / 2)) := by
        refine div_le_div_of_nonneg_left (by positivity) (by positivity) ?_
        exact mul_le_mul hhalf1 hhalf2 (by positivity) (by positivity)
    _ = ‖ψ ζ‖ * (4 * ‖z₁ - z₂‖ / (‖z₁‖ * ‖z₂‖)) := by
        have h₁ : ‖z₁‖ ≠ 0 := ne_of_gt hz₁pos
        have h₂ : ‖z₂‖ ≠ 0 := ne_of_gt hz₂pos
        field_simp
        ring

/-- The difference of two values of the Cauchy transform, bounded by `‖z₁ - z₂‖` divided by the
product of the norms. -/
private lemma cauchyTransform_sub_le_aux {ψ : ℂ → ℂ} (hψc : Continuous ψ) {M : ℝ}
    (hM : ∀ ζ : ℂ, ψ ζ ≠ 0 → ‖ζ‖ ≤ M)
    (hψint : Integrable (fun ζ => ‖ψ ζ‖) volume)
    {z₁ z₂ : ℂ} (hz1₁ : 1 ≤ ‖z₁‖) (hz2₁ : 2 * M ≤ ‖z₁‖)
    (hz1₂ : 1 ≤ ‖z₂‖) (hz2₂ : 2 * M ≤ ‖z₂‖) :
    ‖Work.MRMT.cauchyTransform ψ z₁ - Work.MRMT.cauchyTransform ψ z₂‖
      ≤ (4 * (∫ ζ, ‖ψ ζ‖) / Real.pi) * ‖z₁ - z₂‖ / (‖z₁‖ * ‖z₂‖) := by
  have hzM₁ : M < ‖z₁‖ := by
    refine Work.MRMT.Beltrami.decay_M_lt_norm (x := z₁) hz1₁ hz2₁ ?_
    rw [sub_self, norm_zero]
    linarith [norm_nonneg z₁, hz1₁]
  have hzM₂ : M < ‖z₂‖ := by
    refine Work.MRMT.Beltrami.decay_M_lt_norm (x := z₂) hz1₂ hz2₂ ?_
    rw [sub_self, norm_zero]
    linarith [norm_nonneg z₂, hz1₂]
  have hI1 : IntegrableOn (fun ζ : ℂ => ψ ζ / (ζ - z₁)) (Metric.closedBall (0 : ℂ) M) volume :=
    integrableOn_div_sub hψc hM hzM₁
  have hI2 : IntegrableOn (fun ζ : ℂ => ψ ζ / (ζ - z₂)) (Metric.closedBall (0 : ℂ) M) volume :=
    integrableOn_div_sub hψc hM hzM₂
  have hCT1 := cauchyTransform_eq_setIntegral (ψ := ψ) hM z₁
  have hCT2 := cauchyTransform_eq_setIntegral (ψ := ψ) hM z₂
  have hK : 0 ≤ 4 * ‖z₁ - z₂‖ / (‖z₁‖ * ‖z₂‖) :=
    div_nonneg (by positivity) (mul_nonneg (norm_nonneg _) (norm_nonneg _))
  have hbound : ‖∫ ζ in Metric.closedBall (0 : ℂ) M,
        (ψ ζ / (ζ - z₁) - ψ ζ / (ζ - z₂))‖
      ≤ (∫ ζ, ‖ψ ζ‖) * (4 * ‖z₁ - z₂‖ / (‖z₁‖ * ‖z₂‖)) := by
    have hbint : IntegrableOn (fun ζ : ℂ => ‖ψ ζ‖ * (4 * ‖z₁ - z₂‖ / (‖z₁‖ * ‖z₂‖)))
        (Metric.closedBall (0 : ℂ) M) volume :=
      (hψc.continuousOn.norm.mul continuousOn_const).integrableOn_compact
        (isCompact_closedBall 0 M)
    calc ‖∫ ζ in Metric.closedBall (0 : ℂ) M, (ψ ζ / (ζ - z₁) - ψ ζ / (ζ - z₂))‖
        ≤ ∫ ζ in Metric.closedBall (0 : ℂ) M,
            ‖ψ ζ‖ * (4 * ‖z₁ - z₂‖ / (‖z₁‖ * ‖z₂‖)) :=
          norm_integral_le_of_norm_le hbint
            (ae_of_all _ (norm_div_sub_sub_le hM hz1₁ hz2₁ hz1₂ hz2₂))
      _ = (∫ ζ in Metric.closedBall (0 : ℂ) M, ‖ψ ζ‖)
            * (4 * ‖z₁ - z₂‖ / (‖z₁‖ * ‖z₂‖)) := integral_mul_const _ _
      _ ≤ (∫ ζ, ‖ψ ζ‖) * (4 * ‖z₁ - z₂‖ / (‖z₁‖ * ‖z₂‖)) :=
          mul_le_mul_of_nonneg_right
            (setIntegral_le_integral hψint (ae_of_all _ fun ζ => norm_nonneg _)) hK
  calc ‖Work.MRMT.cauchyTransform ψ z₁ - Work.MRMT.cauchyTransform ψ z₂‖
      = Real.pi⁻¹ * ‖∫ ζ in Metric.closedBall (0 : ℂ) M,
          (ψ ζ / (ζ - z₁) - ψ ζ / (ζ - z₂))‖ := by
        rw [hCT1, hCT2, ← mul_sub, norm_mul, Work.MRMT.Beltrami.decay_norm_cauchyConst,
          ← integral_sub hI1 hI2]
    _ ≤ Real.pi⁻¹ * ((∫ ζ, ‖ψ ζ‖) * (4 * ‖z₁ - z₂‖ / (‖z₁‖ * ‖z₂‖))) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = (4 * (∫ ζ, ‖ψ ζ‖) / Real.pi) * ‖z₁ - z₂‖ / (‖z₁‖ * ‖z₂‖) := by
        have hπ : (Real.pi : ℝ) ≠ 0 := Real.pi_ne_zero
        have h₁ : ‖z₁‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hz1₁)
        have h₂ : ‖z₂‖ ≠ 0 := ne_of_gt (lt_of_lt_of_le one_pos hz1₂)
        field_simp

theorem cauchyTransform_sub_le {ψ : ℂ → ℂ} (hψ : ContDiff ℝ 1 ψ) (hs : HasCompactSupport ψ) :
    ∃ C R : ℝ, 0 ≤ C ∧ ∀ z₁ z₂ : ℂ, R ≤ ‖z₁‖ → R ≤ ‖z₂‖ →
      ‖Work.MRMT.cauchyTransform ψ z₁ - Work.MRMT.cauchyTransform ψ z₂‖
        ≤ C * ‖z₁ - z₂‖ / (‖z₁‖ * ‖z₂‖) := by
  obtain ⟨M, hM0, hM⟩ := Work.MRMT.Beltrami.decay_exists_support_radius ψ hs
  have hψc : Continuous ψ := hψ.continuous
  have hψint : Integrable (fun ζ => ‖ψ ζ‖) volume :=
    (hψc.integrable_of_hasCompactSupport hs).norm
  have hInn : 0 ≤ ∫ ζ, ‖ψ ζ‖ := integral_nonneg fun ζ => norm_nonneg _
  refine ⟨4 * (∫ ζ, ‖ψ ζ‖) / Real.pi, max 1 (2 * M),
    div_nonneg (mul_nonneg (by norm_num) hInn) Real.pi_pos.le, ?_⟩
  intro z₁ z₂ hz₁ hz₂
  exact cauchyTransform_sub_le_aux hψc hM hψint
    (le_trans (le_max_left _ _) hz₁) (le_trans (le_max_right _ _) hz₁)
    (le_trans (le_max_left _ _) hz₂) (le_trans (le_max_right _ _) hz₂)

end Work.MRMT.Found
