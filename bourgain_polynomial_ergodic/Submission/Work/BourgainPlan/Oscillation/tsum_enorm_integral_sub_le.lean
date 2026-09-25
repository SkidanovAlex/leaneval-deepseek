import Mathlib
import Submission.Work.BourgainPlan.Oscillation.lacunary_truncated_maximal_l2
import Submission.Work.BourgainPlan.Oscillation.Lacunary.defs
import Submission.Work.BourgainPlan.Oscillation.oscBlock_plancherel

namespace Work.BourgainPlan.Oscillation

open MeasureTheory
open scoped BigOperators ENNReal

/-- The `ℓ²` bound for the Fourier coefficients of the multiplier difference.

Writing `F θ = (m₁ θ - m₂ θ) · trigP s g θ`, the quantity in the statement is
`∑' x, ‖ĉ_F(x)‖ₑ ^ 2` where `ĉ_F(x) = ∫₀¹ F θ · Echar x θ dθ` is the `x`-th Fourier
coefficient of `F`.  Plancherel (`oscBlock_plancherel`) turns this into `∫ |F|²`, and
the pointwise bound `|m₁ - m₂| ≤ C` together with the Plancherel identity for the
trigonometric polynomial `trigP s g` (`Lacunary.trig_lintegral`) gives the claim. -/
theorem tsum_enorm_integral_sub_le {m₁ m₂ : ℝ → ℂ} (hm₁ : Measurable m₁) (hm₂ : Measurable m₂)
    (hb₁ : ∃ B : ℝ, ∀ θ, ‖m₁ θ‖ ≤ B) (hb₂ : ∃ B : ℝ, ∀ θ, ‖m₂ θ‖ ≤ B)
    {C : ℝ} (hC : ∀ θ, ‖m₁ θ - m₂ θ‖ ≤ C) (g : ℤ → ℂ) (s : Finset ℤ) :
    ∑' x : ℤ, ‖(∫ θ in (0:ℝ)..1, m₁ θ * Work.BourgainPlan.Oscillation.Lacunary.trigP s g θ
          * Work.BourgainPlan.Oscillation.Lacunary.Echar x θ)
        - (∫ θ in (0:ℝ)..1, m₂ θ * Work.BourgainPlan.Oscillation.Lacunary.trigP s g θ
          * Work.BourgainPlan.Oscillation.Lacunary.Echar x θ)‖ₑ ^ (2:ℝ)
      ≤ ENNReal.ofReal (C ^ 2 * ∑ n ∈ s, ‖g n‖ ^ 2) := by
  obtain ⟨B₁, hB₁⟩ := hb₁
  obtain ⟨B₂, hB₂⟩ := hb₂
  set F : ℝ → ℂ := fun θ => (m₁ θ - m₂ θ) * Lacunary.trigP s g θ with hFdef
  have hB₁_nn : 0 ≤ B₁ := le_trans (norm_nonneg (m₁ 0)) (hB₁ 0)
  have hB₂_nn : 0 ≤ B₂ := le_trans (norm_nonneg (m₂ 0)) (hB₂ 0)
  have hC_nn : 0 ≤ C := le_trans (norm_nonneg (m₁ 0 - m₂ 0)) (hC 0)
  have htrig_meas : Measurable (Lacunary.trigP s g) := Lacunary.measurable_trigP s g
  -- Integrability of the two integrands, from the pointwise bounds on `m₁`, `m₂`.
  have hint₁ : ∀ x : ℤ, Integrable (fun θ => m₁ θ * Lacunary.trigP s g θ
      * Lacunary.Echar x θ) Lacunary.mu01 := by
    intro x
    refine Lacunary.integrable_Ioc_of_bound (C := B₁ * (∑ n ∈ s, ‖g n‖)) ?_ ?_
    · exact ((hm₁.mul htrig_meas).mul (Lacunary.continuous_Echar x).measurable)
    · intro θ
      rw [norm_mul, norm_mul, Lacunary.norm_Echar x θ, mul_one]
      exact mul_le_mul (hB₁ θ) (Lacunary.norm_trigP_le s g θ) (norm_nonneg _) hB₁_nn
  have hint₂ : ∀ x : ℤ, Integrable (fun θ => m₂ θ * Lacunary.trigP s g θ
      * Lacunary.Echar x θ) Lacunary.mu01 := by
    intro x
    refine Lacunary.integrable_Ioc_of_bound (C := B₂ * (∑ n ∈ s, ‖g n‖)) ?_ ?_
    · exact ((hm₂.mul htrig_meas).mul (Lacunary.continuous_Echar x).measurable)
    · intro θ
      rw [norm_mul, norm_mul, Lacunary.norm_Echar x θ, mul_one]
      exact mul_le_mul (hB₂ θ) (Lacunary.norm_trigP_le s g θ) (norm_nonneg _) hB₂_nn
  -- `F` is bounded, hence `L²` on `(0,1]`.
  have hF_meas : Measurable F := by
    rw [hFdef]; exact (hm₁.sub hm₂).mul htrig_meas
  have hF_memLp : MemLp F 2 (volume.restrict (Set.Ioc (0:ℝ) 1)) := by
    haveI := Lacunary.isFiniteMeasure_mu01
    refine MemLp.of_bound (p := 2) (μ := Lacunary.mu01) ?_ (C * (∑ n ∈ s, ‖g n‖)) ?_
    · rw [hFdef]; exact ((hm₁.sub hm₂).mul htrig_meas).aestronglyMeasurable
    · filter_upwards with θ
      rw [hFdef, norm_mul]
      exact mul_le_mul (hC θ) (Lacunary.norm_trigP_le s g θ) (norm_nonneg _) hC_nn
  -- The integrand of the statement is the Fourier coefficient of the multiplier difference.
  have hA : ∀ x : ℤ, (∫ θ in (0:ℝ)..1, m₁ θ * Lacunary.trigP s g θ * Lacunary.Echar x θ)
        - (∫ θ in (0:ℝ)..1, m₂ θ * Lacunary.trigP s g θ * Lacunary.Echar x θ)
      = fourierCoeffOn (by norm_num : (0:ℝ) < 1) F x := by
    intro x
    rw [Lacunary.intervalIntegral_eq_mu01 (fun θ => m₁ θ * Lacunary.trigP s g θ
          * Lacunary.Echar x θ),
        Lacunary.intervalIntegral_eq_mu01 (fun θ => m₂ θ * Lacunary.trigP s g θ
          * Lacunary.Echar x θ),
        ← integral_sub (hint₁ x) (hint₂ x),
        Lacunary.fourierCoeffOn_eq_Echar, Lacunary.intervalIntegral_eq_mu01]
    refine integral_congr_ae (Filter.Eventually.of_forall (fun θ => ?_))
    simp only [hFdef]
    ring
  -- Plancherel: the `ℓ²`-sum of the coefficients is the `L²`-norm of `F`.
  have hplan : (∑' x : ℤ, ‖(∫ θ in (0:ℝ)..1, m₁ θ * Lacunary.trigP s g θ
          * Lacunary.Echar x θ)
        - (∫ θ in (0:ℝ)..1, m₂ θ * Lacunary.trigP s g θ
          * Lacunary.Echar x θ)‖ₑ ^ (2:ℝ))
      = ∫⁻ x : ℤ, ‖fourierCoeffOn (by norm_num : (0:ℝ) < 1) F x‖ₑ ^ (2:ℝ)
          ∂MeasureTheory.Measure.count := by
    rw [← MeasureTheory.lintegral_count]
    exact MeasureTheory.lintegral_congr (fun x => by rw [hA x])
  rw [hplan, oscBlock_plancherel F hF_memLp]
  -- Pointwise bound `‖(m₁-m₂)·trigP‖ₑ² ≤ ofReal C² · ‖trigP‖ₑ²`.
  have hC2 : ENNReal.ofReal C ^ (2:ℝ) = ENNReal.ofReal (C ^ 2) := by
    rw [ENNReal.rpow_two]
    exact (ENNReal.ofReal_pow hC_nn 2).symm
  calc ∫⁻ (θ : ℝ) in Set.Ioc 0 1, ‖F θ‖ₑ ^ (2:ℝ)
      ≤ ∫⁻ (θ : ℝ) in Set.Ioc 0 1,
          ENNReal.ofReal (C ^ 2) * ‖Lacunary.trigP s g θ‖ₑ ^ (2:ℝ) := by
        refine lintegral_mono (fun θ => ?_)
        have h1 : ‖F θ‖ₑ ≤ ENNReal.ofReal C * ‖Lacunary.trigP s g θ‖ₑ := by
          rw [hFdef]
          simp only
          rw [enorm_mul]
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          rw [← ofReal_norm]
          exact ENNReal.ofReal_le_ofReal (hC θ)
        calc ‖F θ‖ₑ ^ (2:ℝ) ≤ (ENNReal.ofReal C * ‖Lacunary.trigP s g θ‖ₑ) ^ (2:ℝ) :=
              ENNReal.rpow_le_rpow h1 (by norm_num)
          _ = ENNReal.ofReal C ^ (2:ℝ) * ‖Lacunary.trigP s g θ‖ₑ ^ (2:ℝ) :=
              ENNReal.mul_rpow_of_nonneg _ _ (by norm_num)
          _ = ENNReal.ofReal (C ^ 2) * ‖Lacunary.trigP s g θ‖ₑ ^ (2:ℝ) := by rw [hC2]
    _ = ENNReal.ofReal (C ^ 2) * ∫⁻ (θ : ℝ) in Set.Ioc 0 1,
          ‖Lacunary.trigP s g θ‖ₑ ^ (2:ℝ) :=
        MeasureTheory.lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ = ENNReal.ofReal (C ^ 2) * ENNReal.ofReal (∑ n ∈ s, ‖g n‖ ^ 2) := by
        rw [show (∫⁻ (θ : ℝ) in Set.Ioc 0 1, ‖Lacunary.trigP s g θ‖ₑ ^ (2:ℝ))
            = ∫⁻ θ, ‖Lacunary.trigP s g θ‖ₑ ^ (2:ℝ) ∂Lacunary.mu01 from rfl,
          Lacunary.trig_lintegral]
    _ = ENNReal.ofReal (C ^ 2 * ∑ n ∈ s, ‖g n‖ ^ 2) :=
        (ENNReal.ofReal_mul (sq_nonneg C)).symm

end Work.BourgainPlan.Oscillation
