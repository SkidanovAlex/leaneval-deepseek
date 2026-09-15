import Mathlib
import Submission.Commons.Analysis.Complex.exists_bound_norm_fderiv_sq_of_differentiable_complex

open MeasureTheory Metric
open scoped ENNReal

namespace Commons.Analysis.Complex

/-- **Uniform `L²` bound for the derivative of a holomorphic function of several variables.**

There is a constant `C > 0`, depending only on the dimension `d` and the radius `R`, such that
for every entire function `g : (Fin d → ℂ) → ℂ` and every centre `z`,
`‖fderiv ℂ g z‖ ^ 2 ≤ C * ∫_{closedBall z R} ‖g‖ ^ 2`.

This strengthens `exists_bound_norm_fderiv_sq_of_differentiable_complex`, whose constant is a
priori allowed to depend on `g`: inspection of that proof shows the constant produced there,
`max 1 (d ^ 2 * K⁻¹ / ρ ^ 2)` with `ρ = R / 2` and `K = (π ρ ^ 2) ^ d`, is in fact independent
of `g` (and of `z`). The present proof reproduces that argument with the quantifiers in the
uniform order. -/
theorem fderiv_bound_uniform_of_differentiable_complex {d : ℕ} {R : ℝ} (hR : 0 < R) :
    ∃ C : ℝ, 0 < C ∧ ∀ (g : (Fin d → ℂ) → ℂ), Differentiable ℂ g → ∀ z : Fin d → ℂ,
      ‖fderiv ℂ g z‖ ^ 2 ≤ C * ∫ w in Metric.closedBall z R, ‖g w‖ ^ 2
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) := by
  set ρ : ℝ := R / 2 with hρdef
  have hρ : 0 < ρ := by rw [hρdef]; linarith
  set K : ℝ := (Real.pi * ρ ^ 2) ^ d with hKdef
  have hKpos : 0 < K := by rw [hKdef]; positivity
  set C₀ : ℝ := max 1 ((d : ℝ) ^ 2 * K⁻¹ / ρ ^ 2) with hC₀def
  refine ⟨C₀, ?_, ?_⟩
  · rw [hC₀def]; exact lt_max_iff.mpr (Or.inl zero_lt_one)
  · intro g hg z
    set J : ℝ := ∫ w in Metric.closedBall z R, ‖g w‖ ^ 2
        ∂(MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) with hJdef
    have hJnn : 0 ≤ J := by
      rw [hJdef]; exact integral_nonneg (fun w => by positivity)
    have hintegrable : IntegrableOn (fun w : Fin d → ℂ => ‖g w‖ ^ 2) (Metric.closedBall z R)
        (MeasureTheory.volume : MeasureTheory.Measure (Fin d → ℂ)) :=
      (hg.continuous.norm.pow 2).continuousOn.integrableOn_compact (isCompact_closedBall z R)
    have hcoord : ∀ j : Fin d,
        ‖(fderiv ℂ g z) (Pi.single j (1:ℂ))‖ ≤ Real.sqrt (K⁻¹ * J) / ρ := by
      intro j
      have hslice_diff : Differentiable ℂ
          (fun w : ℂ => g (z + w • (Pi.single j (1:ℂ) : Fin d → ℂ))) :=
        hg.comp (Differentiable.const_add z
          (differentiable_id.smul_const (Pi.single j (1:ℂ) : Fin d → ℂ)))
      refine norm_fderiv_single_le_of_slice_bound hρ j (hg z)
        hslice_diff.differentiableOn hslice_diff.continuous.continuousOn ?_
      intro w hw
      set u : Fin d → ℂ := z + w • (Pi.single j (1:ℂ) : Fin d → ℂ) with hudef
      have hdist : dist u z = ρ := by
        rw [hudef, dist_eq_norm, add_sub_cancel_left, norm_smul, Pi.norm_single, norm_one,
          mul_one, hw]
      have hsub : Metric.closedBall u ρ ⊆ Metric.closedBall z R := by
        intro v hv
        rw [mem_closedBall] at hv ⊢
        calc dist v z ≤ dist v u + dist u z := dist_triangle v u z
          _ ≤ ρ + ρ := add_le_add hv hdist.le
          _ = R := by rw [hρdef]; ring
      have hmono : ∫ v in Metric.closedBall u ρ, ‖g v‖ ^ 2 ≤ J := by
        rw [hJdef]
        refine setIntegral_mono_set hintegrable
          (Filter.Eventually.of_forall (fun v => by positivity)) ?_
        filter_upwards with v hv
        exact hsub hv
      have hana : AnalyticOnNhd ℂ g (Metric.closedBall u ρ) :=
        fun x _ => analyticAt_of_differentiableOn_closedBall (R := 1) one_pos hg.differentiableOn
      have hMV := meanValue_polydisc hρ hana
      rw [Commons.Analysis.Complex.polydisc_volume u hρ] at hMV
      have hstep : ‖g u‖ ^ 2 ≤ K⁻¹ * J := by
        calc ‖g u‖ ^ 2 ≤ ((Real.pi * ρ ^ 2) ^ d)⁻¹ *
              ∫ v in Metric.closedBall u ρ, ‖g v‖ ^ 2 := hMV
          _ ≤ ((Real.pi * ρ ^ 2) ^ d)⁻¹ * J :=
              mul_le_mul_of_nonneg_left hmono (by positivity)
          _ = K⁻¹ * J := by rw [hKdef]
      have h1 : Real.sqrt (‖g u‖ ^ 2) = ‖g u‖ := by
        rw [Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg _)]
      rw [← h1]
      exact Real.sqrt_le_sqrt hstep
    set M : ℝ := (d : ℝ) * Real.sqrt (K⁻¹ * J) / ρ with hMdef
    have hMnn : 0 ≤ M := by rw [hMdef]; positivity
    have hop : ‖fderiv ℂ g z‖ ≤ M := by
      refine ContinuousLinearMap.opNorm_le_bound _ hMnn ?_
      intro w
      have hdecomp : (∑ i : Fin d, w i • (Pi.single i (1:ℂ) : Fin d → ℂ)) = w := by
        rw [← Finset.univ_sum_single w]
        apply Finset.sum_congr rfl
        intro i _
        ext j
        by_cases h : j = i
        · subst h; simp
        · simp [Pi.single_eq_of_ne h]
      have hstep2 : (fderiv ℂ g z) w
          = ∑ i : Fin d, w i • (fderiv ℂ g z) (Pi.single i (1:ℂ)) := by
        conv_lhs => rw [← hdecomp, map_sum]
        simp only [map_smul]
      rw [hstep2]
      calc ‖∑ i : Fin d, w i • (fderiv ℂ g z) (Pi.single i (1:ℂ))‖
          ≤ ∑ i : Fin d, ‖w i • (fderiv ℂ g z) (Pi.single i (1:ℂ))‖ := norm_sum_le _ _
        _ = ∑ i : Fin d, ‖w i‖ * ‖(fderiv ℂ g z) (Pi.single i (1:ℂ))‖ := by
            apply Finset.sum_congr rfl; intro i _; rw [norm_smul]
        _ ≤ ∑ i : Fin d, ‖w i‖ * (Real.sqrt (K⁻¹ * J) / ρ) := by
            apply Finset.sum_le_sum; intro i _
            exact mul_le_mul_of_nonneg_left (hcoord i) (norm_nonneg _)
        _ = (∑ i : Fin d, ‖w i‖) * (Real.sqrt (K⁻¹ * J) / ρ) := by rw [Finset.sum_mul]
        _ ≤ ((d : ℝ) * ‖w‖) * (Real.sqrt (K⁻¹ * J) / ρ) := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            calc ∑ i : Fin d, ‖w i‖ ≤ ∑ _i : Fin d, ‖w‖ :=
                  Finset.sum_le_sum (fun i _ => norm_le_pi_norm w i)
              _ = (d : ℝ) * ‖w‖ := by
                  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        _ = M * ‖w‖ := by rw [hMdef]; ring
    have hMsq : M ^ 2 = ((d : ℝ) ^ 2 * K⁻¹ / ρ ^ 2) * J := by
      rw [hMdef, div_pow, mul_pow, Real.sq_sqrt (by positivity)]; ring
    have hle : ((d : ℝ) ^ 2 * K⁻¹ / ρ ^ 2) ≤ C₀ := by
      rw [hC₀def]; exact le_max_right _ _
    calc ‖fderiv ℂ g z‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hop 2
      _ = ((d : ℝ) ^ 2 * K⁻¹ / ρ ^ 2) * J := hMsq
      _ ≤ C₀ * J := mul_le_mul_of_nonneg_right hle hJnn

end Commons.Analysis.Complex
