import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Order.CompletePartialOrder
import Mathlib.Order.Interval.Basic
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.remov.slice5_rel
import Submission.Work.FTS.EllipticEst.remov.slice5_eqn_deriv2
import Submission.Work.FTS.EllipticEst.H2W.AngBW.Local.slice5_vweight_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.H2W

open MeasureTheory Set Filter
open scoped Real Topology Interval

/-! ## The `v²`-weighted slice bound

This is the "light weight" companion of `slice_step5`: it bounds
`∫_{Iθ} (u/cos θ)² sin(2θ)^{2-γ}` by the same right-hand side as Step 5.

The whole content is the *pointwise* bound of `Work.FTS.EllipticEst.remov.div_cos_sq_le_M`,

  `(u θ / cos θ)² ≤ 100 ∫_{Iθ} (u'')² sEta`   for `θ ∈ (0, π/2)`,

together with the trivial estimate `sin(2θ)^{2-γ} ≤ 1` on `Iθ` (which holds because
`sin(2θ) ∈ [0,1]` there and `2 - γ ≥ 1/2 > 0`).  Integrating over the finite interval
`Iθ` therefore gives `≤ 100 · (π/2) · ∫ (u'')² sEta ≤ 200 · RHS`.  No Hardy inequality
and no use of the equation `Lzero1 u = g` is needed. -/
theorem sliceStep5Vv0 : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
    1 ≤ γ → γ ≤ 3 / 2 →
    ContDiffOn ℝ 4 u (Set.Ioo 0 (Real.pi / 2)) →
    ContinuousOn u (Set.Icc 0 (Real.pi / 2)) →
    u 0 = 0 → u (Real.pi / 2) = 0 →
    (∀ θ ∈ Set.Ioo 0 (Real.pi / 2), Work.FTS.EllipticEst.Lzero1 u θ = g θ) →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv (deriv u))) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (u θ) ^ 2) Work.Spaces.Iθ →
    MeasureTheory.IntegrableOn (fun θ => (deriv (deriv g) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ →
    (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ))
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  refine ⟨200, by norm_num, ?_⟩
  intro γ u g hγ1 hγ2 hu4 hucont hu0 hu1 hode hI4 hI3 hI2 hI1 hI0 hIg2
  have hu2 : ContDiffOn ℝ 2 u (Set.Ioo 0 (Real.pi / 2)) := hu4.of_le (by norm_num)
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := measurableSet_Icc
  have hsin_nn_Iθ : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  set M : ℝ := ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
    Work.FTS.EllipticEst.sEta θ with hMdef
  have hM0 : 0 ≤ M := by
    rw [hMdef]
    exact MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.remov.sEta_nonneg_Iθ hθ))
  -- a.e. on `Iθ` the point lies in the open interval, where `div_cos_sq_le_M` applies
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    have h : Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ))).symm
    rw [(show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl),
      MeasureTheory.Measure.restrict_congr_set h]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hkey : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 100 * M := by
    filter_upwards [hae] with θ hθ
    have h1 : (u θ / Real.cos θ) ^ 2 ≤ 100 * M := by
      have h := Work.FTS.EllipticEst.remov.div_cos_sq_le_M u hu2 hucont hu0 hu1 hI2 θ hθ
      rwa [← hMdef] at h
    have hsin_nn : 0 ≤ Real.sin (2 * θ) :=
      Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
    have hw_le : Real.rpow (Real.sin (2 * θ)) (2 - γ) ≤ 1 :=
      Real.rpow_le_one hsin_nn (Real.sin_le_one _) (by linarith)
    have hw_nn : 0 ≤ Real.rpow (Real.sin (2 * θ)) (2 - γ) := Real.rpow_nonneg hsin_nn _
    calc (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)
        ≤ (100 * M) * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
          mul_le_mul_of_nonneg_right h1 hw_nn
      _ ≤ (100 * M) * 1 := mul_le_mul_of_nonneg_left hw_le (by linarith)
      _ = 100 * M := by ring
  have hvol : (volume : Measure ℝ) Work.Spaces.Iθ < ⊤ := by
    rw [(show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl), Real.volume_Icc]
    exact ENNReal.ofReal_lt_top
  have haesm : MeasureTheory.AEStronglyMeasurable
      (fun θ : ℝ => (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
    refine MeasureTheory.AEStronglyMeasurable.mul ?_ ?_
    · exact ((MeasureTheory.AEStronglyMeasurable.div₀
        (hucont.aestronglyMeasurable hIθ_meas)
        (Real.continuous_cos.measurable.aestronglyMeasurable)).pow 2)
    · exact ((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 2 - γ)).measurable.comp
        (Real.continuous_sin.measurable.comp
          (continuous_const.mul continuous_id).measurable)).aestronglyMeasurable
  have hkey' : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      ‖(u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ)‖ ≤ 100 * M := by
    filter_upwards [hkey, hae] with θ h1 hθ
    have hnn : 0 ≤ (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
      mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (Real.sin_nonneg_of_mem_Icc
        ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩) _)
    rw [Real.norm_eq_abs, abs_of_nonneg hnn]
    exact h1
  have hLHS_int : MeasureTheory.IntegrableOn
      (fun θ => (u θ / Real.cos θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (2 - γ))
      Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.of_bound hvol haesm (100 * M) hkey'
  have hconst_int : MeasureTheory.IntegrableOn (fun _ : ℝ => (100 * M : ℝ)) Work.Spaces.Iθ :=
    MeasureTheory.IntegrableOn.of_bound hvol MeasureTheory.aestronglyMeasurable_const (100 * M)
      (Filter.Eventually.of_forall fun x => by
        rw [Real.norm_eq_abs, abs_of_nonneg (by linarith [hM0] : (0 : ℝ) ≤ 100 * M)])
  have hvolreal : (volume : Measure ℝ).real Work.Spaces.Iθ = Real.pi / 2 := by
    rw [MeasureTheory.Measure.real_def,
      (show Work.Spaces.Iθ = Set.Icc 0 (Real.pi / 2) from rfl), Real.volume_Icc,
      ENNReal.toReal_ofReal (by linarith [Real.pi_pos]), sub_zero]
  have hLHS_le : (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ)) ≤ 100 * M * (Real.pi / 2) := by
    calc (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ))
        ≤ ∫ _θ in Work.Spaces.Iθ, (100 * M : ℝ) :=
          MeasureTheory.integral_mono_ae hLHS_int hconst_int hkey
      _ = 100 * M * (Real.pi / 2) := by
          rw [MeasureTheory.setIntegral_const, hvolreal, smul_eq_mul]; ring
  have hB2_0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
    MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin_nn_Iθ θ hθ) _))
  have hA3_0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
    MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin_nn_Iθ θ hθ) _))
  have hA1_0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg hIθ_meas (fun θ _ => sq_nonneg _)
  have hA0_0 : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg hIθ_meas (fun θ _ => sq_nonneg _)
  have hMleR : M ≤ (((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) +
        ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (2 - γ)) + M +
        ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) +
      ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 := by
    linarith [hB2_0, hA3_0, hA1_0, hA0_0]
  have hpi_le : 100 * (Real.pi / 2) ≤ 200 := by nlinarith [Real.pi_lt_four]
  calc (∫ θ in Work.Spaces.Iθ, (u θ / Real.cos θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (2 - γ))
      ≤ 100 * M * (Real.pi / 2) := hLHS_le
    _ = (100 * (Real.pi / 2)) * M := by ring
    _ ≤ 200 * M := mul_le_mul_of_nonneg_right hpi_le hM0
    _ ≤ 200 * ((((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - γ)) +
          ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (2 - γ)) + M +
          ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2) +
        ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) :=
        mul_le_mul_of_nonneg_left hMleR (by norm_num)

end Work.FTS.EllipticEst.H2W
