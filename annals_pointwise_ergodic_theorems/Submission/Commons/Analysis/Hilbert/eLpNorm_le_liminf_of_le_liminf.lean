import Mathlib.MeasureTheory.Function.LpSeminorm.Defs

namespace Commons.Analysis.Hilbert

open MeasureTheory Filter
open scoped ENNReal

theorem eLpNorm_le_liminf_of_le_liminf (u : Nat → Int → ENNReal) (U : Int → ENNReal) {p : Real} (hp : 0 < p) (h : ∀ n : Int, U n ≤ Filter.liminf (fun j => u j n) Filter.atTop) : MeasureTheory.eLpNorm U (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure Int) ≤ Filter.liminf (fun j => MeasureTheory.eLpNorm (u j) (ENNReal.ofReal p) (MeasureTheory.Measure.count : MeasureTheory.Measure Int)) Filter.atTop := by
  have hpne0 : ENNReal.ofReal p ≠ 0 := ENNReal.ofReal_ne_zero_iff.mpr hp
  have hpnetop : ENNReal.ofReal p ≠ ⊤ := ENNReal.ofReal_ne_top
  simp only [MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal hpne0 hpnetop,
    MeasureTheory.AEStronglyMeasurable.of_discrete,
    ENNReal.toReal_ofReal hp.le]
  simp_rw [enorm_eq_self]
  have hLM : (∫⁻ x : Int, U x ^ p ∂(MeasureTheory.Measure.count : MeasureTheory.Measure Int))
      ≤ Filter.liminf (fun j => ∫⁻ x : Int, u j x ^ p
          ∂(MeasureTheory.Measure.count : MeasureTheory.Measure Int)) Filter.atTop := by
    calc (∫⁻ x : Int, U x ^ p ∂(MeasureTheory.Measure.count : MeasureTheory.Measure Int))
        ≤ ∫⁻ x : Int, (Filter.liminf (fun j => u j x) Filter.atTop) ^ p
            ∂(MeasureTheory.Measure.count : MeasureTheory.Measure Int) :=
          MeasureTheory.lintegral_mono (fun x => ENNReal.rpow_le_rpow (h x) hp.le)
      _ = ∫⁻ x : Int, Filter.liminf (fun j => u j x ^ p) Filter.atTop
            ∂(MeasureTheory.Measure.count : MeasureTheory.Measure Int) := by
          apply MeasureTheory.lintegral_congr
          intro x
          have key : ENNReal.orderIsoRpow p hp (Filter.liminf (fun j => u j x) Filter.atTop)
              = Filter.liminf (fun j => ENNReal.orderIsoRpow p hp (u j x)) Filter.atTop := by
            refine (ENNReal.orderIsoRpow p hp).liminf_apply ?_ ?_ ?_ ?_
            all_goals isBoundedDefault
          simpa only [ENNReal.orderIsoRpow_apply] using key
      _ ≤ Filter.liminf (fun j => ∫⁻ x : Int, u j x ^ p
            ∂(MeasureTheory.Measure.count : MeasureTheory.Measure Int)) Filter.atTop := by
          apply MeasureTheory.lintegral_liminf_le'
          intro j
          exact (measurable_of_countable (fun x : Int => u j x ^ p)).aemeasurable
  calc (∫⁻ x : Int, U x ^ p ∂(MeasureTheory.Measure.count : MeasureTheory.Measure Int)) ^ (1 / p)
      ≤ (Filter.liminf (fun j => ∫⁻ x : Int, u j x ^ p
            ∂(MeasureTheory.Measure.count : MeasureTheory.Measure Int)) Filter.atTop) ^ (1 / p) :=
        ENNReal.rpow_le_rpow hLM (by positivity)
    _ = Filter.liminf (fun j => (∫⁻ x : Int, u j x ^ p
            ∂(MeasureTheory.Measure.count : MeasureTheory.Measure Int)) ^ (1 / p)) Filter.atTop := by
        have key : ENNReal.orderIsoRpow (1 / p) (by positivity)
              (Filter.liminf (fun j => ∫⁻ x : Int, u j x ^ p
                ∂(MeasureTheory.Measure.count : MeasureTheory.Measure Int)) Filter.atTop)
            = Filter.liminf (fun j => ENNReal.orderIsoRpow (1 / p) (by positivity)
                (∫⁻ x : Int, u j x ^ p
                  ∂(MeasureTheory.Measure.count : MeasureTheory.Measure Int))) Filter.atTop := by
          refine (ENNReal.orderIsoRpow (1 / p) (by positivity)).liminf_apply ?_ ?_ ?_ ?_
          all_goals isBoundedDefault
        simpa only [ENNReal.orderIsoRpow_apply] using key

end Commons.Analysis.Hilbert
