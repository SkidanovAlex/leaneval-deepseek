import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.BoseFixB1.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1S.corr

noncomputable section

open MeasureTheory Metric Filter
open scoped ContDiff Topology Real BigOperators ENNReal


set_option linter.unusedVariables false

/-! ## Elementary helpers -/

/-- Pointwise form of `∫ z, boxInd ℓ d u z * w z = ∫ z in dlBox ℓ d u, w z`. -/
private lemma boxInd_mul_eq_indicator (ℓ d : ℝ) (u z : EuclideanSpace ℝ (Fin 3)) (w : EuclideanSpace ℝ (Fin 3) → ℝ) :
    Work.SmallBoxSliding.boxInd ℓ d u z * w z
      = (Submission.BoseGases.dlBox ℓ d u).indicator w z := by
  by_cases hz : z ∈ Submission.BoseGases.dlBox ℓ d u
  · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hz, Set.indicator_of_mem hz, one_mul]
  · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hz, Set.indicator_of_notMem hz,
      zero_mul]

/-- `(u,x) ↦ 1_{B(u)}(x)` is jointly measurable. -/
private lemma measurable_uncurry_boxInd (ℓ d : ℝ) :
    Measurable (Function.uncurry (Work.SmallBoxSliding.boxInd ℓ d)) := by
  have hEq : Function.uncurry (Work.SmallBoxSliding.boxInd ℓ d)
      = {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1}.indicator
          (fun _ => (1 : ℝ)) := by
    funext p
    obtain ⟨u, x⟩ := p
    simp only [Function.uncurry_apply_pair]
    by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
    · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hx,
        Set.indicator_of_mem (show (u, x) ∈
          {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx)]
    · rw [Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hx,
        Set.indicator_of_notMem (show (u, x) ∉
          {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) | p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx)]
  rw [hEq]
  exact measurable_const.indicator (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d)

/-- The true box volume is nonnegative. -/
private lemma boxMass_nonneg (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
  rw [Work.SmallBoxSliding.boxMass_eq_measureReal, MeasureTheory.Measure.real_def]
  exact ENNReal.toReal_nonneg

/-- `|a⁻¹ x| ≤ C` from `0 ≤ a`, `0 ≤ C` and `|x| ≤ C a`. -/
private lemma abs_inv_mul_le {a x C : ℝ} (ha : 0 ≤ a) (hC : 0 ≤ C) (hx : |x| ≤ C * a) :
    |a⁻¹ * x| ≤ C := by
  rcases eq_or_lt_of_le ha with h0 | hpos
  · subst h0
    simp only [inv_zero, zero_mul, abs_zero]
    exact hC
  · rw [abs_mul, abs_inv, abs_of_pos hpos]
    have hinv : (0 : ℝ) ≤ a⁻¹ := inv_nonneg.mpr ha
    calc a⁻¹ * |x| ≤ a⁻¹ * (C * a) := mul_le_mul_of_nonneg_left hx hinv
      _ = C := by rw [mul_comm C a, ← mul_assoc, inv_mul_cancel₀ (ne_of_gt hpos), one_mul]

/-! ## The main theorem -/

/-- The sliding-box mean of a continuous state is measurable in the box centre and uniformly
bounded: for `0 < ℓ`, `0 < d` and continuous `w`, the map
`u ↦ (boxMass ℓ d u)⁻¹ ∫_{dlBox ℓ d u} w` is measurable with a uniform bound `C ≥ 0`.

Route: `∫ z, boxInd ℓ d u z * w z = ∫ z in dlBox ℓ d u, w z` with the joint integrand
`(u,z) ↦ boxInd ℓ d u z * w z` jointly measurable, `StronglyMeasurable.integral_prod_right'`
(as in `Work.UBBInputs9.B.pd_aux.aemeasurable_boxMean`); the bound `C = sup_{acube ℓ}|w|` from
`IsCompact.exists_bound_of_continuousOn` on the compact `acube ℓ` (note
`dlBox ℓ d u ⊆ acube ℓ`), `|∫_{dlBox} w| ≤ C * boxMass` and `0 ≤ boxMass`.

CAUTION: the identically-stated `Work.BoseFixB1S.corrMarg.measurable_and_bound_boxMean` is itself
a `sorry`; proving this by `exact`ing it would make the proof depend on `sorryAx`.  Prove it from
scratch. -/
theorem measurableBoxMeanKH {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hw : Continuous w) :
    Measurable (fun u : EuclideanSpace ℝ (Fin 3) =>
      (Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
        ∫ z in Submission.BoseGases.dlBox ℓ d u, w z)
    ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ u : EuclideanSpace ℝ (Fin 3),
        |(Work.SmallBoxSliding.boxMass ℓ d u)⁻¹ *
          ∫ z in Submission.BoseGases.dlBox ℓ d u, w z| ≤ C := by
  constructor
  · -- ### Measurability
    -- joint measurability of the `(u,z)`-integrand
    have hboxInd_meas : Measurable (Function.uncurry (Work.SmallBoxSliding.boxInd ℓ d)) :=
      measurable_uncurry_boxInd ℓ d
    have hjoint : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.SmallBoxSliding.boxInd ℓ d p.1 p.2 * w p.2) :=
      hboxInd_meas.mul (hw.measurable.comp measurable_snd)
    -- its parametric integral is strongly measurable in `u`
    have hint : StronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
        ∫ z : EuclideanSpace ℝ (Fin 3), Work.SmallBoxSliding.boxInd ℓ d u z * w z) :=
      MeasureTheory.StronglyMeasurable.integral_prod_right' hjoint.stronglyMeasurable
    -- rewrite the whole-space integral as an integral over the moving box `B(u)`
    have hconv : (fun u : EuclideanSpace ℝ (Fin 3) => ∫ z : EuclideanSpace ℝ (Fin 3), Work.SmallBoxSliding.boxInd ℓ d u z * w z)
        = fun u : EuclideanSpace ℝ (Fin 3) => ∫ z in Submission.BoseGases.dlBox ℓ d u, w z := by
      funext u
      rw [← MeasureTheory.integral_indicator (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)]
      exact MeasureTheory.integral_congr_ae
        (Filter.Eventually.of_forall fun z => boxInd_mul_eq_indicator ℓ d u z w)
    have hint_meas : Measurable (fun u : EuclideanSpace ℝ (Fin 3) =>
        ∫ z in Submission.BoseGases.dlBox ℓ d u, w z) :=
      hconv ▸ hint.measurable
    -- `boxMass` is measurable by the same argument with the constant integrand `1`
    have hmass : Measurable (fun u : EuclideanSpace ℝ (Fin 3) => Work.SmallBoxSliding.boxMass ℓ d u) := by
      have hs : StronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
          ∫ z : EuclideanSpace ℝ (Fin 3), Work.SmallBoxSliding.boxInd ℓ d u z) :=
        MeasureTheory.StronglyMeasurable.integral_prod_right'
          (f := Function.uncurry (Work.SmallBoxSliding.boxInd ℓ d))
          hboxInd_meas.stronglyMeasurable
      exact hs.measurable
    exact hmass.inv.mul hint_meas
  · -- ### Uniform bound
    obtain ⟨C₀, hC₀⟩ := (Work.UBBInputs9.B.acube_isCompact ℓ).exists_bound_of_continuousOn
      hw.continuousOn
    refine ⟨max C₀ 0, le_max_right _ _, fun u => ?_⟩
    have hCb : ∀ x ∈ Submission.BoseGases.acube ℓ, ‖w x‖ ≤ max C₀ 0 :=
      fun x hx => le_trans (hC₀ x hx) (le_max_left _ _)
    have hsub : Submission.BoseGases.dlBox ℓ d u ⊆ Submission.BoseGases.acube ℓ :=
      fun x hx => hx.1
    have hvol : (volume : Measure (EuclideanSpace ℝ (Fin 3))) (Submission.BoseGases.dlBox ℓ d u) < ⊤ :=
      Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u
    have hI : |∫ z in Submission.BoseGases.dlBox ℓ d u, w z|
        ≤ max C₀ 0 * Work.SmallBoxSliding.boxMass ℓ d u := by
      have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const (μ := (volume : Measure (EuclideanSpace ℝ (Fin 3))))
        (f := w) (s := Submission.BoseGases.dlBox ℓ d u) (C := max C₀ 0) hvol
        (fun z hz => hCb z (hsub hz))
      rw [Real.norm_eq_abs, ← Work.SmallBoxSliding.boxMass_eq_measureReal] at h
      exact h
    exact abs_inv_mul_le (boxMass_nonneg ℓ d u) (le_max_right _ _) hI

end

end Work.BoseFixB1S.corr
