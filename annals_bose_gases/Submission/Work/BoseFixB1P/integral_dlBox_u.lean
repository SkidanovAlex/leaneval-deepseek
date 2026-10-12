import Mathlib.Tactic.Have
import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1P.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1P

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal

open Submission.BoseGases
open Work.SmallBoxSliding

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false

/-- **Tube identity**: integrating over the sliding box `dlBox l d u` and then over all positions
`u` recovers the big-box integral.  For fixed `x` the set `{u | x ∈ dlBox l d u}` is a translate of
`acube 1` (volume `1`) when `x ∈ acube l` and empty otherwise, so
`int_u boxInd l d u x = 1_{acube l}(x)` (`Work.SmallBoxSliding.boxInd_integral_u`, PROVED);
Tonelli/Fubini for the nonnegative `|F|` gives both the integrability of the `u`-marginal and the
identity (the joint integrand is `boxInd l d p.1 p.2 * F p.2`; use
`Work.SmallBoxSliding.aemeasurable_ofReal_boxInd`, `lintegral_boxInd_u`,
`MeasureTheory.lintegral_prod`, `lintegral_lintegral_swap`, `lintegral_const_mul` and
`MeasureTheory.ofReal_integral_eq_lintegral_ofReal` to compute
`int^- p, ||boxInd p.1 p.2 * F p.2|| = ENNReal.ofReal (int_{acube l} ||F||) < top`, then Fubini via
`MeasureTheory.integral_integral_swap`). -/
theorem integral_dlBox_u {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d) {F : EuclideanSpace ℝ (Fin 3) → ℝ}
    (hF : Continuous F) :
    MeasureTheory.Integrable (fun u : EuclideanSpace ℝ (Fin 3) =>
        ∫ x in Submission.BoseGases.dlBox ℓ d u, F x)
      ∧ (∫ u : EuclideanSpace ℝ (Fin 3),
          ∫ x in Submission.BoseGases.dlBox ℓ d u, F x)
        = ∫ x in Submission.BoseGases.acube ℓ, F x := by
  classical
  -- the pointwise identification of the inner integral with the `boxInd`-weighted one
  have hinner : ∀ u : ℝ³, (∫ x : ℝ³, F x * boxInd ℓ d u x) = ∫ x in dlBox ℓ d u, F x := by
    intro u
    have hfun : (fun x : ℝ³ => F x * boxInd ℓ d u x) = (dlBox ℓ d u).indicator F := by
      funext x
      rw [boxInd]
      by_cases hx : x ∈ dlBox ℓ d u
      · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
      · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
    rw [hfun, MeasureTheory.integral_indicator (measurableSet_dlBox ℓ d u)]
  -- joint (a.e.) measurability of the box indicator on the product
  have hboxm : AEMeasurable (fun p : ℝ³ × ℝ³ => boxInd ℓ d p.1 p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
    have h : (fun p : ℝ³ × ℝ³ => boxInd ℓ d p.1 p.2)
        = {p : ℝ³ × ℝ³ | p.2 ∈ dlBox ℓ d p.1}.indicator (fun _ => (1 : ℝ)) := by
      funext p
      rw [boxInd]
      by_cases hp : p.2 ∈ dlBox ℓ d p.1
      · rw [Set.indicator_of_mem hp,
            Set.indicator_of_mem (show p ∈ {q : ℝ³ × ℝ³ | q.2 ∈ dlBox ℓ d q.1} from hp)]
      · rw [Set.indicator_of_notMem hp,
            Set.indicator_of_notMem (show p ∉ {q : ℝ³ × ℝ³ | q.2 ∈ dlBox ℓ d q.1} from hp)]
    rw [h]
    exact (measurable_const.indicator (measurableSet_boxIndSet ℓ d)).aemeasurable
  have hFm : AEMeasurable (fun p : ℝ³ × ℝ³ => F p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    (hF.measurable.comp measurable_snd).aemeasurable
  have hGae : AEStronglyMeasurable (fun p : ℝ³ × ℝ³ => F p.2 * boxInd ℓ d p.1 p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    (hFm.mul hboxm).aestronglyMeasurable
  -- `boxInd` is nonnegative, so its `enorm` is its `ofReal`
  have hbinn : ∀ p : ℝ³ × ℝ³, 0 ≤ boxInd ℓ d p.1 p.2 := by
    intro p; rw [boxInd]; exact Set.indicator_nonneg (fun _ _ => zero_le_one) p.2
  have hHeq : ∀ p : ℝ³ × ℝ³,
      ‖F p.2 * boxInd ℓ d p.1 p.2‖ₑ
        = ENNReal.ofReal |F p.2| * ENNReal.ofReal (boxInd ℓ d p.1 p.2) := by
    intro p
    rw [enorm_mul, Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal (hbinn p)]
  have hprodmeas : AEMeasurable
      (fun p : ℝ³ × ℝ³ => ENNReal.ofReal |F p.2| * ENNReal.ofReal (boxInd ℓ d p.1 p.2))
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) :=
    (ENNReal.measurable_ofReal.comp_aemeasurable
      ((hF.comp continuous_snd).abs.aemeasurable)).mul
      (ENNReal.measurable_ofReal.comp_aemeasurable hboxm)
  -- `|F|` is integrable on the big box (continuous on a compact set)
  have hcompact : IsCompact (acube ℓ) :=
    (Metric.isCompact_iff_isClosed_bounded).mpr ⟨acube_isClosed ℓ, acube_isBounded ℓ hℓ.le⟩
  have hintOn : IntegrableOn (fun x : ℝ³ => |F x|) (acube ℓ) :=
    ContinuousOn.integrableOn_compact hcompact hF.continuousOn.abs
  -- Tonelli: the joint `enorm`-integral is `ofReal (∫_{acube ℓ} |F|)`
  have hbound : ∫⁻ p : ℝ³ × ℝ³, ‖F p.2 * boxInd ℓ d p.1 p.2‖ₑ
      = ENNReal.ofReal (∫ x in acube ℓ, |F x|) := by
    calc ∫⁻ p : ℝ³ × ℝ³, ‖F p.2 * boxInd ℓ d p.1 p.2‖ₑ
        = ∫⁻ p : ℝ³ × ℝ³, ENNReal.ofReal |F p.2| * ENNReal.ofReal (boxInd ℓ d p.1 p.2) :=
          lintegral_congr hHeq
      _ = ∫⁻ u : ℝ³, ∫⁻ x : ℝ³,
            ENNReal.ofReal |F x| * ENNReal.ofReal (boxInd ℓ d u x) :=
          lintegral_prod _ hprodmeas
      _ = ∫⁻ x : ℝ³, ∫⁻ u : ℝ³,
            ENNReal.ofReal |F x| * ENNReal.ofReal (boxInd ℓ d u x) :=
          lintegral_lintegral_swap hprodmeas
      _ = ∫⁻ x : ℝ³, ENNReal.ofReal |F x| * (∫⁻ u : ℝ³, ENNReal.ofReal (boxInd ℓ d u x)) := by
          apply lintegral_congr; intro x
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ = ∫⁻ x : ℝ³, ENNReal.ofReal |F x| * (acube ℓ).indicator (fun _ => (1 : ℝ≥0∞)) x := by
          apply lintegral_congr; intro x
          rw [lintegral_boxInd_u hℓ hd x]
      _ = ∫⁻ x in acube ℓ, ENNReal.ofReal |F x| := by
          rw [← lintegral_indicator (acube_measurable ℓ)]
          apply lintegral_congr; intro x
          by_cases hx : x ∈ acube ℓ
          · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, mul_one]
          · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, mul_zero]
      _ = ENNReal.ofReal (∫ x in acube ℓ, |F x|) :=
          (ofReal_integral_eq_lintegral_ofReal hintOn
            (Filter.Eventually.of_forall (fun x => abs_nonneg (F x)))).symm
  -- hence the joint integrand is integrable
  have hGint : Integrable (fun p : ℝ³ × ℝ³ => F p.2 * boxInd ℓ d p.1 p.2)
      ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
    refine ⟨hGae, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    calc ∫⁻ a : ℝ³ × ℝ³, ‖F a.2 * boxInd ℓ d a.1 a.2‖ₑ
            ∂(volume.prod volume : Measure (ℝ³ × ℝ³))
        = ∫⁻ a : ℝ³ × ℝ³, ‖F a.2 * boxInd ℓ d a.1 a.2‖ₑ := rfl
      _ = ENNReal.ofReal (∫ x in acube ℓ, |F x|) := hbound
      _ < ⊤ := ENNReal.ofReal_lt_top
  refine ⟨?_, ?_⟩
  · -- integrability of the `u`-marginal, by Fubini
    have h := hGint.integral_prod_left
    exact h.congr (Filter.Eventually.of_forall hinner)
  · -- the identity, by the particle-number telescoping of the indicator layer
    have hswap : Integrable (fun p : ℝ³ × ℝ³ => F p.1 * boxInd ℓ d p.2 p.1)
        ((volume : Measure ℝ³).prod (volume : Measure ℝ³)) := by
      have h := (MeasureTheory.integrable_swap_iff
        (μ := (volume : Measure ℝ³)) (ν := (volume : Measure ℝ³))
        (f := fun p : ℝ³ × ℝ³ => F p.2 * boxInd ℓ d p.1 p.2)).mpr hGint
      have h' : ((fun p : ℝ³ × ℝ³ => F p.2 * boxInd ℓ d p.1 p.2) ∘ Prod.swap)
          = fun p : ℝ³ × ℝ³ => F p.1 * boxInd ℓ d p.2 p.1 := rfl
      rwa [h'] at h
    have hval := nBoxInd_integral_u hℓ hd F hswap
    calc (∫ u : ℝ³, ∫ x in dlBox ℓ d u, F x)
        = ∫ u : ℝ³, ∫ x : ℝ³, F x * boxInd ℓ d u x := by
          apply integral_congr_ae
          filter_upwards with u
          exact (hinner u).symm
      _ = ∫ x in acube ℓ, F x := hval

end Work.BoseFixB1P
