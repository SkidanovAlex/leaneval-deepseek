import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.Integral.Prod
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeIbp
import Submission.Work.FTS.StrongEps.EComparison.SlotsZeroModeKey

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `SlotsZeroLayerSetBound` — the layer integral in product-measure form

The boundary-layer estimate of the zero-mode comparison argument is needed in two shapes:

* `layer_slice_le` / `layer_integral_le` (in `SlotsZeroModeIbp`) give, for a *fixed* `z > 0`,
  `∫_θ |Φ z θ|·1_{layer_n}(θ) ≤ 2C√(sliceEnergy Φ z)·(2δ_n)^((3+η)/2)`, and the corresponding
  `z`-integrated form over `[a,b]`;
* the surrounding development (`SlotsZeroModeKey2`, `SlotsZeroModeKey3`) consumes the layer
  density in the **product-measure** form
  `∫_{Q0} |Φ p.1 p.2|·1_{[a,b]}(p.1)·1_{layer_n}(p.2)`.

This file bridges the two: `setIntegral_absPhi_layer` is the Fubini identity identifying the
product-measure integral over the quadrant `Q0 = (0,∞) × (0,π/2)` with the iterated integral over
`z ∈ (0,∞)` and `θ ∈ Iθ = [0,π/2]`, and `SlotsZeroLayerSetBound` is the resulting bound.
-/

namespace Work.FTS.StrongEps.EComparison

open scoped Real Topology
open MeasureTheory Set Filter

/-- `Iθ = [0, π/2]` is measurable. -/
theorem measurableSet_Iθ : MeasurableSet Work.Spaces.Iθ := by
  show MeasurableSet (Set.Icc (0 : ℝ) (Real.pi / 2))
  exact measurableSet_Icc

/-- The layer `(0, 2δ_n) ∪ (π/2 - 2δ_n, π/2)` is measurable. -/
theorem layer_measurable (n : ℕ) : MeasurableSet (layer n) := by
  rw [layer_eq_union]
  exact measurableSet_Ioo.union measurableSet_Ioo

/-- The restricted measure of the quadrant is the product of the radial half-line with the
angular interval `Iθ`. -/
theorem restrict_Q0_eq_prod_Iθ :
    (volume.restrict Work.FTS.EllipticEst.Q0 : Measure (ℝ × ℝ))
      = ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := by
  rw [restrict_Q0_eq_prod, restrict_Ioo_eq_Iθ]

/-- **Fubini for the layer density.**  The product-measure integral over the quadrant of
`|Φ|·1_{[a,b]}(z)·1_{layer n}(θ)` equals the iterated integral over `z ∈ (0,∞)` and `θ ∈ Iθ`. -/
theorem setIntegral_absPhi_layer {Φ : ℝ → ℝ → ℝ} {a b : ℝ} {n : ℕ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hΦint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ)
    (hEint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)
      (Set.Icc a b)) :
    (∫ p in Work.FTS.EllipticEst.Q0,
        |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
      = ∫ z in Set.Ioi 0, ∫ θ in Work.Spaces.Iθ,
          |Φ z θ| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z * layerInd n θ := by
  classical
  have hcont : ContinuousOn (fun p : ℝ × ℝ => |Φ p.1 p.2|) Work.FTS.EllipticEst.Q0 :=
    continuousOn_absPhi_mode hsm
  have hind : Measurable (fun p : ℝ × ℝ =>
      (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1) :=
    (measurable_const.indicator measurableSet_Icc).comp measurable_fst
  have hlay : Measurable (fun p : ℝ × ℝ => layerInd n p.2) :=
    (measurable_const.indicator (layer_measurable n)).comp measurable_snd
  have hK : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1)
      Work.FTS.EllipticEst.Q0 := integrableOn_absPhi_box hsm hΦint hEint
  have hG : MeasureTheory.IntegrableOn (fun p : ℝ × ℝ =>
      |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
      Work.FTS.EllipticEst.Q0 := by
    refine Integrable.mono' hK ?_ ?_
    · exact ((hcont.aestronglyMeasurable Work.FTS.EllipticEst.isOpen_Q0.measurableSet).mul
        hind.aestronglyMeasurable).mul hlay.aestronglyMeasurable
    · filter_upwards with p
      simp only [Real.norm_eq_abs, abs_mul, abs_abs, layerInd]
      rw [abs_of_nonneg (indicator_one_nonneg (A := Set.Icc a b) p.1),
        abs_of_nonneg (indicator_one_nonneg (A := layer n) p.2)]
      simpa using mul_le_mul_of_nonneg_left (indicator_one_le_one (A := layer n) p.2)
        (mul_nonneg (abs_nonneg (Φ p.1 p.2)) (indicator_one_nonneg (A := Set.Icc a b) p.1))
  have hQ0 : (volume.restrict Work.FTS.EllipticEst.Q0 : Measure (ℝ × ℝ))
      = ((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
          ((volume : Measure ℝ).restrict Work.Spaces.Iθ) := restrict_Q0_eq_prod_Iθ
  have hint : MeasureTheory.Integrable (fun p : ℝ × ℝ =>
      |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
      (((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
        ((volume : Measure ℝ).restrict Work.Spaces.Iθ)) := by
    rw [← hQ0]
    exact hG
  have hfub := MeasureTheory.integral_prod (fun p : ℝ × ℝ =>
      |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2) hint
  rw [show (∫ p in Work.FTS.EllipticEst.Q0,
        |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2)
      = ∫ p, |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1 * layerInd n p.2
          ∂(((volume : Measure ℝ).restrict (Set.Ioi 0)).prod
            ((volume : Measure ℝ).restrict Work.Spaces.Iθ)) from by rw [hQ0]]
  exact hfub

/-- The boundary-layer bound in product-measure form: the `[a,b] × layer_n` part of `|Φ|` is
controlled by `2C·(2δ_n)^((3+η)/2)·∫_{[a,b]} √(sliceEnergy Φ)`. -/
theorem SlotsZeroLayerSetBound {Φ : ℝ → ℝ → ℝ} {C a b : ℝ}
    (hsm : ∀ k : ℕ, ContDiffOn ℝ k (Function.uncurry Φ)
      (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    (hΦint : ∀ z ∈ Set.Ioi (0 : ℝ),
      MeasureTheory.IntegrableOn (fun θ => |Φ z θ|) Work.Spaces.Iθ)
    (hC : ∀ z ∈ Set.Ioi (0 : ℝ), ∀ δ ∈ Set.Ioc (0 : ℝ) (Real.pi / 4),
      (∫ θ in Set.Ioo 0 δ, |Φ z θ|)
          ≤ C * Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)
              * δ ^ ((3 + Work.Spaces.eta) / 2) ∧
      (∫ θ in Set.Ioo (Real.pi / 2 - δ) (Real.pi / 2), |Φ z θ|)
          ≤ C * Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)
              * δ ^ ((3 + Work.Spaces.eta) / 2))
    (hEint : MeasureTheory.IntegrableOn (fun z => ∫ θ in Work.Spaces.Iθ, |Φ z θ|)
      (Set.Icc a b))
    (hEsqrt : MeasureTheory.IntegrableOn
      (fun z => Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)) (Set.Icc a b))
    (ha : 0 < a)
    {n : ℕ} (hn0 : 0 < 2 * Work.FTS.StrongEps.EComparison.delta n)
    (hn1 : 2 * Work.FTS.StrongEps.EComparison.delta n ≤ Real.pi / 4) :
    (∫ p in Work.FTS.EllipticEst.Q0,
        |Φ p.1 p.2| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) p.1
          * Work.FTS.StrongEps.EComparison.layerInd n p.2)
      ≤ 2 * C * (2 * Work.FTS.StrongEps.EComparison.delta n) ^ ((3 + Work.Spaces.eta) / 2)
          * (∫ z in Set.Icc a b,
              Real.sqrt (Work.FTS.StrongEps.EComparison.sliceEnergy Φ z)) := by
  classical
  have haIcc : Set.Icc a b ⊆ Set.Ioi (0 : ℝ) := fun z hz => lt_of_lt_of_le ha hz.1
  have hInd : ∀ z : ℝ, 0 ≤ (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z :=
    fun z => indicator_one_nonneg z
  rw [setIntegral_absPhi_layer hsm hΦint hEint]
  have hstep : (∫ z in Set.Ioi (0 : ℝ), ∫ θ in Work.Spaces.Iθ,
        |Φ z θ| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z * layerInd n θ)
      ≤ ∫ z in Set.Ioi (0 : ℝ), (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
          * (2 * C * Real.sqrt (sliceEnergy Φ z)
              * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2)) := by
    refine MeasureTheory.integral_mono_of_nonneg ?_ ?_ ?_
    · filter_upwards with z
      exact MeasureTheory.integral_nonneg fun θ =>
        mul_nonneg (mul_nonneg (abs_nonneg (Φ z θ)) (hInd z)) (indicator_one_nonneg θ)
    · -- integrability of the dominating slice expression
      have h1 : MeasureTheory.Integrable
          ((Set.Icc a b).indicator (fun z : ℝ => Real.sqrt (sliceEnergy Φ z))) volume :=
        hEsqrt.integrable_indicator measurableSet_Icc
      have h2 : MeasureTheory.Integrable
          ((Set.Icc a b).indicator (fun z : ℝ => Real.sqrt (sliceEnergy Φ z)))
          (volume.restrict (Set.Ioi (0 : ℝ))) :=
        h1.mono_measure MeasureTheory.Measure.restrict_le_self
      have h3 : MeasureTheory.Integrable (fun z => (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
          * Real.sqrt (sliceEnergy Φ z)) (volume.restrict (Set.Ioi (0 : ℝ))) := by
        refine h2.congr (Eventually.of_forall fun z => ?_)
        by_cases hz : z ∈ Set.Icc a b
        · simp only [Set.indicator_of_mem hz, one_mul]
        · simp only [Set.indicator_of_notMem hz, zero_mul]
      refine (h3.const_mul (2 * C * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2))).congr
        (Eventually.of_forall fun z => ?_)
      ring
    · refine MeasureTheory.ae_restrict_of_forall_mem measurableSet_Ioi fun z hz => ?_
      show (∫ θ in Work.Spaces.Iθ, |Φ z θ| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
            * layerInd n θ)
          ≤ (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
              * (2 * C * Real.sqrt (sliceEnergy Φ z)
                  * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2))
      have hc : (∫ θ in Work.Spaces.Iθ, |Φ z θ| * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
            * layerInd n θ)
          = (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
              * ∫ θ in Work.Spaces.Iθ, |Φ z θ| * layerInd n θ := by
        rw [← MeasureTheory.integral_const_mul]
        refine MeasureTheory.setIntegral_congr_fun measurableSet_Iθ (fun θ _ => ?_)
        ring
      rw [hc]
      exact mul_le_mul_of_nonneg_left (layer_slice_le hΦint hC hz hn0 hn1) (hInd z)
  refine hstep.trans ?_
  rw [show (fun z : ℝ => (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
        * (2 * C * Real.sqrt (sliceEnergy Φ z)
            * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2)))
      = fun z => (2 * C * (2 * delta n) ^ ((3 + Work.Spaces.eta) / 2))
          * ((Set.Icc a b).indicator (fun _ => (1 : ℝ)) z * Real.sqrt (sliceEnergy Φ z)) from by
    funext z; ring]
  rw [MeasureTheory.integral_const_mul]
  rw [show (∫ z in Set.Ioi (0 : ℝ), (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z
        * Real.sqrt (sliceEnergy Φ z))
      = ∫ z in Set.Ioi (0 : ℝ), Real.sqrt (sliceEnergy Φ z)
          * (Set.Icc a b).indicator (fun _ => (1 : ℝ)) z from by
    refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi (fun z _ => by ring)]
  rw [setIntegral_mul_indicator measurableSet_Icc haIcc]

end Work.FTS.StrongEps.EComparison
