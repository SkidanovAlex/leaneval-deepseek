import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.Analysis.Normed.Lp.MeasurableSpace
import Submission.Work.UBBInputs9.B.pd_aux.aemeasurable_boxMean
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `margAuxBoxMeanB1` — measurability and uniform boundedness of the sliding box mean

For `0 < ℓ`, `0 < d` and **continuous** `w : ℝ³ → ℝ`, the sliding-box mean

    u ↦ (1 / |B(u)|) · ∫_{B(u)} w ,      B(u) = acube ℓ ∩ ((ℓd)•u + acube (ℓd)) ,

where `boxMass ℓ d u = ∫_x 1_{B(u)}(x) dx = |B(u)|`, is Borel measurable in the box
centre `u` and uniformly bounded.  (This is the `c₀`-input of `margAuxBoundB1`: the
mean `(1/|B(u)|)∫_{B(u)} w` is the anchored mean `M(u)` of the sliding word.)

* **Measurability.**  The joint integrand `(u,z) ↦ 1_{B(u)}(z)·w z` is measurable:
  `1_{B(u)}(z)` is the indicator of the measurable set `{(u,z) | z ∈ dlBox ℓ d u}`
  (`Work.SmallBoxSliding.measurableSet_boxIndSet`).  Hence its parametric integral
  `u ↦ ∫ z, boxInd ℓ d u z · w z` is strongly measurable
  (`MeasureTheory.StronglyMeasurable.integral_prod_right'`, which needs no
  integrability), and it equals `u ↦ ∫ z in dlBox ℓ d u, w z`
  (`MeasureTheory.integral_indicator`).  `boxMass ℓ d u = ∫ z, boxInd ℓ d u z` is
  measurable by the same argument, and `(1/·) * (·)` is measurable
  (`StronglyMeasurable.measurable` upgrades to `Measurable` because `ℝ` is second
  countable).

* **Boundedness.**  `dlBox ℓ d u ⊆ acube ℓ` for *every* `u`, and `|w|` is bounded on
  the compact cube `acube ℓ` (`Submission.BoseGases.acube_compact`,
  `IsCompact.exists_bound_of_continuousOn`); with `C₀ = max C 0` we get
  `|∫ z in dlBox ℓ d u, w z| ≤ C₀ · |B(u)|` from
  `MeasureTheory.norm_setIntegral_le_of_norm_le_const`.  If `|B(u)| = 0` then
  `1 / |B(u)| = 0` (the `ℝ`-convention `1/0 = 0`) and the bound is trivial; if
  `|B(u)| > 0`, multiplying by the nonnegative factor `1/|B(u)|` and cancelling
  `|B(u)|⁻¹·|B(u)| = 1` gives the bound.  The constant `C₀` depends only on `w`
  and `ℓ` — *not* on `u` — so the bound is uniform over all box centres.
-/

noncomputable section

open MeasureTheory

namespace Work.BoseFixB1S.oneBodyB1

set_option linter.unusedVariables false

/-- The sliding-box volume `boxMass ℓ d u = |B(u)|` is nonnegative. -/
lemma boxMass_nonneg (ℓ d : ℝ) (u : EuclideanSpace ℝ (Fin 3)) :
    0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := by
  rw [Work.SmallBoxSliding.boxMass_eq_measureReal, Measure.real_def]
  exact ENNReal.toReal_nonneg

theorem margAuxBoxMeanB1 {ℓ d : ℝ} (hℓ : 0 < ℓ) (hd : 0 < d)
    {w : EuclideanSpace ℝ (Fin 3) → ℝ} (hw : Continuous w) :
    Measurable (fun u : EuclideanSpace ℝ (Fin 3) =>
        (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ z in Submission.BoseGases.dlBox ℓ d u, w z)
    ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ u : EuclideanSpace ℝ (Fin 3),
        |(1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ z in Submission.BoseGases.dlBox ℓ d u, w z| ≤ C := by
  constructor
  · -- ## Measurability of the box mean
    -- the box indicator is the indicator of a measurable set
    have hboxInd : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.SmallBoxSliding.boxInd ℓ d p.1 p.2) := by
      have heq : (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Work.SmallBoxSliding.boxInd ℓ d p.1 p.2)
          = {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
              p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1}.indicator (fun _ => (1 : ℝ)) := by
        funext p
        obtain ⟨u, x⟩ := p
        by_cases hx : x ∈ Submission.BoseGases.dlBox ℓ d u
        · rw [Set.indicator_of_mem (show (u, x) ∈
              {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
                p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx),
            Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hx]
        · rw [Set.indicator_of_notMem (show (u, x) ∉
              {p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) |
                p.2 ∈ Submission.BoseGases.dlBox ℓ d p.1} from hx),
            Work.SmallBoxSliding.boxInd, Set.indicator_of_notMem hx]
      rw [heq]
      exact measurable_const.indicator (Work.SmallBoxSliding.measurableSet_boxIndSet ℓ d)
    -- joint measurability of the integrand `(u,z) ↦ 1_{B(u)}(z) * w z`
    have hjointmeas : Measurable (fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
        Work.SmallBoxSliding.boxInd ℓ d p.1 p.2 * w p.2) :=
      hboxInd.mul (hw.measurable.comp measurable_snd)
    -- hence its parametric integral is strongly measurable in `u`
    have hint : StronglyMeasurable (fun u : EuclideanSpace ℝ (Fin 3) =>
        ∫ z : EuclideanSpace ℝ (Fin 3), Work.SmallBoxSliding.boxInd ℓ d u z * w z) := by
      have h := MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := volume)
        (f := fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Work.SmallBoxSliding.boxInd ℓ d p.1 p.2 * w p.2) hjointmeas.stronglyMeasurable
      simpa using h
    -- rewrite it as the integral over the moving box `B(u)`
    have hconv : (fun u : EuclideanSpace ℝ (Fin 3) =>
        ∫ z : EuclideanSpace ℝ (Fin 3), Work.SmallBoxSliding.boxInd ℓ d u z * w z)
        = fun u : EuclideanSpace ℝ (Fin 3) =>
          ∫ z in Submission.BoseGases.dlBox ℓ d u, w z := by
      funext u
      have hpt : (fun z : EuclideanSpace ℝ (Fin 3) =>
          Work.SmallBoxSliding.boxInd ℓ d u z * w z)
          = (Submission.BoseGases.dlBox ℓ d u).indicator w := by
        funext z
        by_cases hz : z ∈ Submission.BoseGases.dlBox ℓ d u
        · rw [Set.indicator_of_mem hz, Work.SmallBoxSliding.boxInd, Set.indicator_of_mem hz,
            one_mul]
        · rw [Set.indicator_of_notMem hz, Work.SmallBoxSliding.boxInd,
            Set.indicator_of_notMem hz, zero_mul]
      rw [hpt, MeasureTheory.integral_indicator (Work.SmallBoxSliding.measurableSet_dlBox ℓ d u)]
    have hInt : Measurable (fun u : EuclideanSpace ℝ (Fin 3) =>
        ∫ z in Submission.BoseGases.dlBox ℓ d u, w z) := by
      rw [← hconv]
      exact hint.measurable
    -- `boxMass` is measurable by the same argument with `w = 1`
    have hMass : Measurable (fun u : EuclideanSpace ℝ (Fin 3) =>
        Work.SmallBoxSliding.boxMass ℓ d u) := by
      have h := MeasureTheory.StronglyMeasurable.integral_prod_right' (ν := volume)
        (f := fun p : EuclideanSpace ℝ (Fin 3) × EuclideanSpace ℝ (Fin 3) =>
          Work.SmallBoxSliding.boxInd ℓ d p.1 p.2) hboxInd.stronglyMeasurable
      have h2 : (fun u : EuclideanSpace ℝ (Fin 3) =>
          ∫ z : EuclideanSpace ℝ (Fin 3), Work.SmallBoxSliding.boxInd ℓ d u z)
          = fun u : EuclideanSpace ℝ (Fin 3) => Work.SmallBoxSliding.boxMass ℓ d u := rfl
      rw [← h2]
      exact h.measurable
    exact (hMass.const_div 1).mul hInt
  · -- ## Uniform boundedness of the box mean
    -- bound `|w|` on the compact cube `acube ℓ`
    obtain ⟨C, hC⟩ := (Submission.BoseGases.acube_compact hℓ).exists_bound_of_continuousOn
      (f := w) hw.continuousOn
    refine ⟨max C 0, le_max_right _ _, fun u => ?_⟩
    have hpoint : ∀ z ∈ Submission.BoseGases.dlBox ℓ d u, ‖w z‖ ≤ max C 0 := by
      intro z hz
      rw [Real.norm_eq_abs]
      exact le_trans (hC z (Work.SmallBoxSliding.dlBox_subset_acube ℓ d u hz))
        (le_max_left _ _)
    -- `|∫_{B(u)} w| ≤ (max C 0) * |B(u)|`
    have hmain : |∫ z in Submission.BoseGases.dlBox ℓ d u, w z|
        ≤ (max C 0) * Work.SmallBoxSliding.boxMass ℓ d u := by
      have h := MeasureTheory.norm_setIntegral_le_of_norm_le_const
        (Work.SmallBoxSliding.volume_dlBox_lt_top hℓ d u) hpoint
      rw [Real.norm_eq_abs, ← Work.SmallBoxSliding.boxMass_eq_measureReal] at h
      exact h
    have hmnn : 0 ≤ Work.SmallBoxSliding.boxMass ℓ d u := boxMass_nonneg ℓ d u
    by_cases h0 : Work.SmallBoxSliding.boxMass ℓ d u = 0
    · -- the box has measure zero: `1 / 0 = 0` in `ℝ`
      rw [h0, div_zero, zero_mul, abs_zero]
      exact le_max_right _ _
    · -- the box has positive measure: cancel `|B(u)|`
      have hpos : 0 < Work.SmallBoxSliding.boxMass ℓ d u :=
        lt_of_le_of_ne hmnn (Ne.symm h0)
      have h1 : |(1 / Work.SmallBoxSliding.boxMass ℓ d u) *
          ∫ z in Submission.BoseGases.dlBox ℓ d u, w z|
          = (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            |∫ z in Submission.BoseGases.dlBox ℓ d u, w z| := by
        rw [abs_mul, abs_of_nonneg (div_nonneg zero_le_one hmnn)]
      rw [h1]
      calc (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
            |∫ z in Submission.BoseGases.dlBox ℓ d u, w z|
          ≤ (1 / Work.SmallBoxSliding.boxMass ℓ d u) *
              ((max C 0) * Work.SmallBoxSliding.boxMass ℓ d u) :=
            mul_le_mul_of_nonneg_left hmain (div_nonneg zero_le_one hmnn)
        _ = max C 0 := by
            rw [one_div, mul_comm (max C 0) (Work.SmallBoxSliding.boxMass ℓ d u),
              inv_mul_cancel_left₀ (ne_of_gt hpos)]

end Work.BoseFixB1S.oneBodyB1
