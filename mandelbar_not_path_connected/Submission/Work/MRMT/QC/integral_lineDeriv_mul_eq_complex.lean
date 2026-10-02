import Mathlib

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open MeasureTheory

open Filter MeasureTheory Measure Module Metric Set Asymptotics
open scoped MeasureTheory Topology

namespace Work.MRMT.QC

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [FiniteDimensional ℝ E] [μ.IsAddHaarMeasure]

/-- A complex-valued Lipschitz function on a finite-dimensional real normed space is almost
everywhere line-differentiable in every direction.  This is the complex-valued instance of
Rademacher's theorem, obtained from `LipschitzWith.ae_differentiableAt` (which holds for values in
any finite-dimensional real space, in particular `ℂ`). -/
theorem ae_lineDifferentiableAt_complex {f : E → ℂ} {C : NNReal} (hf : LipschitzWith C f)
    (v : E) : ∀ᵐ x ∂μ, LineDifferentiableAt ℝ f x v :=
  hf.ae_differentiableAt.mono fun _x hx => hx.lineDifferentiableAt

/-- Dominated convergence statement for the difference quotients of a complex-valued Lipschitz
function, against an integrable complex-valued weight. -/
theorem integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul_complex
    {f g : E → ℂ} {C : NNReal} (hf : LipschitzWith C f) (hg : Integrable g μ) (v : E) :
    Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, lineDeriv ℝ f x v * g x ∂μ)) := by
  apply tendsto_integral_filter_of_dominated_convergence (fun x ↦ (C * ‖v‖) * ‖g x‖)
  · filter_upwards with t
    apply AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
    apply aestronglyMeasurable_const.fun_smul
    apply AEStronglyMeasurable.sub _ hf.continuous.measurable.aestronglyMeasurable
    apply AEMeasurable.aestronglyMeasurable
    exact hf.continuous.measurable.comp_aemeasurable' (aemeasurable_id'.add_const _)
  · filter_upwards [self_mem_nhdsWithin] with t (ht : 0 < t)
    filter_upwards with x
    calc ‖t⁻¹ • (f (x + t • v) - f x) * g x‖
      = (t⁻¹ * ‖f (x + t • v) - f x‖) * ‖g x‖ := by simp [ht.le]
    _ ≤ (t⁻¹ * (C * ‖(x + t • v) - x‖)) * ‖g x‖ := by
      gcongr; exact LipschitzWith.norm_sub_le hf (x + t • v) x
    _ = (C * ‖v‖) * ‖g x‖ := by simp [field, norm_smul, abs_of_nonneg ht.le]
  · exact hg.norm.const_mul _
  · filter_upwards [ae_lineDifferentiableAt_complex hf v] with x hx
    exact hx.hasLineDerivAt.tendsto_slope_zero_right.mul tendsto_const_nhds

/-- Dominated convergence statement for the difference quotients of a *compactly supported*
complex-valued Lipschitz function, against a continuous complex-valued weight. -/
theorem integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'_complex
    {f g : E → ℂ} {C : NNReal} (hf : LipschitzWith C f) (h'f : HasCompactSupport f)
    (hg : Continuous g) (v : E) :
    Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
      (𝓝 (∫ x, lineDeriv ℝ f x v * g x ∂μ)) := by
  let K := cthickening (‖v‖) (tsupport f)
  have K_compact : IsCompact K := IsCompact.cthickening h'f
  apply tendsto_integral_filter_of_dominated_convergence
      (K.indicator (fun x ↦ (C * ‖v‖) * ‖g x‖))
  · filter_upwards with t
    apply AEStronglyMeasurable.mul ?_ hg.aestronglyMeasurable
    apply aestronglyMeasurable_const.fun_smul
    apply AEStronglyMeasurable.sub _ hf.continuous.measurable.aestronglyMeasurable
    apply AEMeasurable.aestronglyMeasurable
    exact hf.continuous.measurable.comp_aemeasurable' (aemeasurable_id'.add_const _)
  · filter_upwards [Ioc_mem_nhdsGT zero_lt_one] with t ht
    have t_pos : 0 < t := ht.1
    filter_upwards with x
    by_cases hx : x ∈ K
    · calc ‖t⁻¹ • (f (x + t • v) - f x) * g x‖
        = (t⁻¹ * ‖f (x + t • v) - f x‖) * ‖g x‖ := by simp [t_pos.le]
      _ ≤ (t⁻¹ * (C * ‖(x + t • v) - x‖)) * ‖g x‖ := by
        gcongr; exact LipschitzWith.norm_sub_le hf (x + t • v) x
      _ = (C * ‖v‖) * ‖g x‖ := by simp [field, norm_smul, abs_of_nonneg t_pos.le]
      _ = K.indicator (fun x ↦ (C * ‖v‖) * ‖g x‖) x := by rw [indicator_of_mem hx]
    · have A : f x = 0 := by
        rw [← Function.notMem_support]
        contrapose hx
        exact self_subset_cthickening _ (subset_tsupport _ hx)
      have B : f (x + t • v) = 0 := by
        rw [← Function.notMem_support]
        contrapose hx
        apply mem_cthickening_of_dist_le _ _ (‖v‖) (tsupport f) (subset_tsupport _ hx)
        simp only [dist_eq_norm, sub_add_cancel_left, norm_neg, norm_smul, Real.norm_eq_abs,
          abs_of_nonneg t_pos.le]
        exact mul_le_of_le_one_left (norm_nonneg v) ht.2
      simp only [B, A, sub_self, smul_zero, zero_mul, norm_zero]
      exact indicator_nonneg (fun y _hy ↦ by positivity) _
  · rw [integrable_indicator_iff K_compact.measurableSet]
    exact ContinuousOn.integrableOn_compact K_compact (by fun_prop)
  · filter_upwards [ae_lineDifferentiableAt_complex hf v] with x hx
    exact hx.hasLineDerivAt.tendsto_slope_zero_right.mul tendsto_const_nhds

/-- Integration by parts for the line derivative, for complex-valued Lipschitz functions.

This is the complex-valued counterpart of `LipschitzWith.integral_lineDeriv_mul_eq`. -/
theorem integral_lineDeriv_mul_eq_complex {f g : E → ℂ} {C D : NNReal}
    (hf : LipschitzWith C f) (hg : LipschitzWith D g) (h'g : HasCompactSupport g) (v : E) :
    ∫ x, lineDeriv ℝ f x v * g x ∂μ = ∫ x, lineDeriv ℝ g x (-v) * f x ∂μ := by
  /- Write the line derivatives as limits of the difference quotients
  `(f (x + t • v) - f x) / t` and `(g (x - t • v) - g x) / t`, hence the integrals as the limits of
  the corresponding integrals, thanks to dominated convergence. At fixed positive `t` the two
  integrals coincide, by the change of variables `y = x + t • v` and commutativity of `ℂ`, so the
  limits coincide as well. -/
  have A : Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ) (𝓝[>] 0)
              (𝓝 (∫ x, lineDeriv ℝ f x v * g x ∂μ)) :=
    integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul_complex hf
      (hg.continuous.integrable_of_hasCompactSupport h'g) v
  have B : Tendsto (fun (t : ℝ) ↦ ∫ x, (t⁻¹ • (g (x + t • (-v)) - g x)) * f x ∂μ) (𝓝[>] 0)
              (𝓝 (∫ x, lineDeriv ℝ g x (-v) * f x ∂μ)) :=
    integral_inv_smul_sub_mul_tendsto_integral_lineDeriv_mul'_complex hg h'g hf.continuous (-v)
  suffices S1 : ∀ (t : ℝ), ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ =
                            ∫ x, (t⁻¹ • (g (x + t • (-v)) - g x)) * f x ∂μ by
    simp only [S1] at A
    exact tendsto_nhds_unique A B
  intro t
  have S3 : ∫ x, f (x + t • v) * g x ∂μ = ∫ x, f x * g (x + t • (-v)) ∂μ := by
    rw [← integral_add_right_eq_self _ (t • (-v))]; simp
  have S2 : ∫ x, (f (x + t • v) - f x) * g x ∂μ =
      ∫ x, f x * (g (x + t • (-v)) - g x) ∂μ := by
    have hI1 : Integrable (fun x => f (x + t • v) * g x) μ :=
      ((hf.continuous.comp (continuous_add_const _)).mul hg.continuous).integrable_of_hasCompactSupport
        h'g.mul_left
    have hI2 : Integrable (fun x => f x * g x) μ :=
      (hf.continuous.mul hg.continuous).integrable_of_hasCompactSupport h'g.mul_left
    have hI3 : Integrable (fun x => f x * g (x + t • (-v))) μ :=
      (hf.continuous.mul (hg.continuous.comp (continuous_add_const _))).integrable_of_hasCompactSupport
        ((h'g.comp_homeomorph (Homeomorph.addRight (t • (-v)))).mul_left)
    simp_rw [_root_.sub_mul, _root_.mul_sub]
    rw [integral_sub hI1 hI2, integral_sub hI3 hI2, S3]
  calc ∫ x, (t⁻¹ • (f (x + t • v) - f x)) * g x ∂μ
      = ∫ x, ((t⁻¹ : ℝ) : ℂ) * ((f (x + t • v) - f x) * g x) ∂μ := by
        apply integral_congr_ae; filter_upwards with x
        rw [Complex.real_smul]; ring
    _ = ((t⁻¹ : ℝ) : ℂ) * ∫ x, (f (x + t • v) - f x) * g x ∂μ := integral_const_mul _ _
    _ = ((t⁻¹ : ℝ) : ℂ) * ∫ x, f x * (g (x + t • (-v)) - g x) ∂μ := by rw [S2]
    _ = ((t⁻¹ : ℝ) : ℂ) * ∫ x, (g (x + t • (-v)) - g x) * f x ∂μ := by
        congr 1
        exact integral_congr_ae (Eventually.of_forall fun x => mul_comm _ _)
    _ = ∫ x, ((t⁻¹ : ℝ) : ℂ) * ((g (x + t • (-v)) - g x) * f x) ∂μ :=
        (integral_const_mul _ _).symm
    _ = ∫ x, (t⁻¹ • (g (x + t • (-v)) - g x)) * f x ∂μ := by
        apply integral_congr_ae; filter_upwards with x
        rw [Complex.real_smul]; ring

end Work.MRMT.QC
