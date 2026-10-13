import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.FDeriv.Measurable
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

/-- The `(∂_θ(u/cos θ))²`-weighted slice bound of Step 5.

The content is `Work.FTS.EllipticEst.remov.slice5_vweight_le`, which bounds
`∫_{Iθ} (∂_θ(u/cos θ))² sin(2θ)^{4-γ'}` by a universal multiple of
`∫ (u'')² sEta + ∫ (u')² + ∫ u²`, with a constant that is *independent* of `γ'`
(namely `2000`) but which is only exposed to us existentially.  We therefore
instantiate it at the largest admitted exponent `γ' = 3/2` (weight `sin(2θ)^{5/2}`,
the smallest of the weights `sin(2θ)^{4-γ}`, `γ ∈ [1, 3/2]`, because `sin(2θ) ≤ 1`
on `Iθ`) and add the two nonnegative Step 5 terms `∫(g'')²ψ`,
`∫(u''')² sin(2θ)^{2-γ}` to the right-hand side. -/
theorem sliceStep5Vv1 : ∃ C : ℝ, 0 < C ∧ ∀ (γ : ℝ) (u g : ℝ → ℝ),
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
    (∫ θ in Work.Spaces.Iθ, (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ C * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := by
  obtain ⟨C₁, hC₁pos, hC₁⟩ :=
    Work.FTS.EllipticEst.remov.slice5_vweight_le (3 / 2) (by norm_num) le_rfl
  refine ⟨C₁ + 1, by linarith, ?_⟩
  intro γ u g hγ1 hγ2 hu4 hucont hu0 hu1 hode hI4 hI3 hI2 hI1 hI0 hIg2
  obtain ⟨_, hFv_int32, _, hFv_bnd⟩ :=
    hC₁ u (hu4.of_le (by norm_num)) hucont hu0 hu1 hI2 hI1 hI0
  -- elementary facts about the interval and the weight
  have hIθ_eq : Work.Spaces.Iθ = Set.Icc (0 : ℝ) (Real.pi / 2) := rfl
  have hIθ_meas : MeasurableSet Work.Spaces.Iθ := by
    rw [hIθ_eq]; exact measurableSet_Icc
  have hsin2_nn : ∀ θ ∈ Work.Spaces.Iθ, 0 ≤ Real.sin (2 * θ) := by
    intro θ hθ
    rw [hIθ_eq] at hθ
    exact Real.sin_nonneg_of_mem_Icc ⟨by linarith [hθ.1], by linarith [hθ.2, Real.pi_pos]⟩
  have hae : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      θ ∈ Set.Ioo 0 (Real.pi / 2) := by
    have h : Set.Icc (0 : ℝ) (Real.pi / 2) =ᵐ[volume] Set.Ioo 0 (Real.pi / 2) :=
      (MeasureTheory.Ioo_ae_eq_Icc (μ := (volume : Measure ℝ))).symm
    rw [hIθ_eq, MeasureTheory.Measure.restrict_congr_set h]
    exact MeasureTheory.ae_restrict_mem measurableSet_Ioo
  have hsin2pos_of_mem_Ioo : ∀ θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2),
      0 < Real.sin (2 * θ) := fun θ hθ =>
    Real.sin_pos_of_pos_of_lt_pi (by linarith [hθ.1]) (by linarith [hθ.2, Real.pi_pos])
  -- `sin(2θ)^{4-γ} ≤ sin(2θ)^{4-3/2}` on the open interval
  have hpt : ∀ᵐ θ ∂(volume : Measure ℝ).restrict Work.Spaces.Iθ,
      (deriv (fun t => u t / Real.cos t) θ) ^ 2 * Real.rpow (Real.sin (2 * θ)) (4 - γ)
        ≤ (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
            Real.rpow (Real.sin (2 * θ)) (4 - 3 / 2) := by
    filter_upwards [hae] with θ hθ
    have hs := hsin2pos_of_mem_Ioo θ hθ
    have hs1 : Real.sin (2 * θ) ≤ 1 := Real.sin_le_one _
    have hexp : 4 - 3 / 2 ≤ 4 - γ := by linarith
    exact mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge hs hs1 hexp)
      (sq_nonneg _)
  -- integrability of the `γ`-weighted integrand, by domination through the `3/2` one
  have hFv_int : MeasureTheory.IntegrableOn
      (fun θ => (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ)) Work.Spaces.Iθ := by
    refine MeasureTheory.Integrable.mono hFv_int32 ?_ ?_
    · refine MeasureTheory.AEStronglyMeasurable.mul ?_ ?_
      · exact ((measurable_deriv (fun t => u t / Real.cos t)).pow_const 2).aestronglyMeasurable
      · exact ((Real.continuous_rpow_const (by linarith : (0 : ℝ) ≤ 4 - γ)).measurable.comp
          (Real.continuous_sin.measurable.comp
            (continuous_const.mul continuous_id).measurable)).aestronglyMeasurable
    · filter_upwards [hpt, hae] with θ hθ hθ'
      have hs := hsin2pos_of_mem_Ioo θ hθ'
      have h1 : (0 : ℝ) ≤ deriv (fun t => u t / Real.cos t) θ ^ 2 *
          (Real.sin (2 * θ)).rpow (4 - γ) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
      have h2 : (0 : ℝ) ≤ deriv (fun θ' => u θ' / Real.cos θ') θ ^ 2 *
          (Real.sin (2 * θ)).rpow (4 - 3 / 2) :=
        mul_nonneg (sq_nonneg _) (Real.rpow_nonneg hs.le _)
      rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h1, abs_of_nonneg h2]
      exact hθ
  have hcmp := MeasureTheory.integral_mono_ae hFv_int hFv_int32 hpt
  -- nonnegativity of the five right-hand-side integrals
  have hA2nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
      Work.FTS.EllipticEst.sEta θ :=
    MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Work.FTS.EllipticEst.remov.sEta_nonneg_Iθ hθ))
  have hA1nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg hIθ_meas (fun θ _ => sq_nonneg _)
  have hA0nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (u θ) ^ 2 :=
    MeasureTheory.setIntegral_nonneg hIθ_meas (fun θ _ => sq_nonneg _)
  have hB2nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (4 - γ) :=
    MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2_nn θ hθ) _))
  have hA3nn : 0 ≤ ∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
      Real.rpow (Real.sin (2 * θ)) (2 - γ) :=
    MeasureTheory.setIntegral_nonneg hIθ_meas
      (fun θ hθ => mul_nonneg (sq_nonneg _) (Real.rpow_nonneg (hsin2_nn θ hθ) _))
  -- the mild amplification of the right-hand side
  have hPQ : (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ)
      + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)
      ≤ (∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := by
    linarith [hB2nn, hA3nn]
  have hP0 : 0 ≤ (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ)
      + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2) := by
    linarith [hA2nn, hA1nn, hA0nn]
  have hstep : C₁ * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
        Work.FTS.EllipticEst.sEta θ)
      + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
      + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2))
      ≤ (C₁ + 1) * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) :=
    mul_le_mul (by linarith : C₁ ≤ C₁ + 1) hPQ hP0 (by linarith : (0 : ℝ) ≤ C₁ + 1)
  calc (∫ θ in Work.Spaces.Iθ, (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
        Real.rpow (Real.sin (2 * θ)) (4 - γ))
      ≤ (∫ θ in Work.Spaces.Iθ, (deriv (fun t => u t / Real.cos t) θ) ^ 2 *
          Real.rpow (Real.sin (2 * θ)) (4 - 3 / 2)) := hcmp
    _ ≤ C₁ * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
            Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := hFv_bnd
    _ ≤ (C₁ + 1) * ((∫ θ in Work.Spaces.Iθ, (deriv (deriv g) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (4 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv (deriv u)) θ) ^ 2 *
              Real.rpow (Real.sin (2 * θ)) (2 - γ))
          + (∫ θ in Work.Spaces.Iθ, (deriv (deriv u) θ) ^ 2 *
              Work.FTS.EllipticEst.sEta θ)
          + (∫ θ in Work.Spaces.Iθ, (deriv u θ) ^ 2)
          + (∫ θ in Work.Spaces.Iθ, (u θ) ^ 2)) := hstep

end Work.FTS.EllipticEst.H2W
