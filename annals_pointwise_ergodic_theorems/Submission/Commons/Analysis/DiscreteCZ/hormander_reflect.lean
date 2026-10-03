import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.MeasureTheory.Integral.Lebesgue.Countable

namespace Commons.Analysis.DiscreteCZ

open MeasureTheory Set
open scoped ENNReal

theorem hormander_reflect {K : ℤ → ℂ} {Ak : ℝ}
    (h : ∀ y : ℤ, y ≠ 0 → ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs}, ‖K (x - y) - K x‖ₑ
        ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) ≤ ENNReal.ofReal Ak) :
    ∀ y : ℤ, y ≠ 0 → ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs}, ‖K (-(x - y)) - K (-x)‖ₑ
        ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) ≤ ENNReal.ofReal Ak := by
  intro y hy
  have hy' : -y ≠ 0 := neg_ne_zero.mpr hy
  have hb := h (-y) hy'
  have hset : {x : ℤ | 2 * (-y).natAbs ≤ x.natAbs} = {x : ℤ | 2 * y.natAbs ≤ x.natAbs} := by
    ext x; rw [Set.mem_ofPred_eq, Set.mem_ofPred_eq, Int.natAbs_neg]
  rw [hset] at hb
  set f : ℤ → ℝ≥0∞ := fun u => ‖K (u - (-y)) - K u‖ₑ with hf
  have hs : MeasurableSet {x : ℤ | 2 * y.natAbs ≤ x.natAbs} := by measurability
  have key : ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs}, f (-x) ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ)
      = ∫⁻ x in {x : ℤ | 2 * y.natAbs ≤ x.natAbs}, f x ∂(MeasureTheory.Measure.count : MeasureTheory.Measure ℤ) := by
    rw [← lintegral_indicator hs, ← lintegral_indicator hs]
    rw [MeasureTheory.lintegral_count, MeasureTheory.lintegral_count]
    rw [← Equiv.tsum_eq (Equiv.neg ℤ) (Set.indicator {x : ℤ | 2 * y.natAbs ≤ x.natAbs} f)]
    congr 1
    funext x
    simp only [Set.indicator_apply]
    by_cases hx : x ∈ {a : ℤ | 2 * y.natAbs ≤ a.natAbs}
    · have hx' : (Equiv.neg ℤ) x ∈ {a : ℤ | 2 * y.natAbs ≤ a.natAbs} := by
        rw [Set.mem_ofPred_eq] at hx ⊢
        rwa [Equiv.neg_apply, Int.natAbs_neg]
      rw [if_pos hx, if_pos hx']
      rfl
    · have hx' : (Equiv.neg ℤ) x ∉ {a : ℤ | 2 * y.natAbs ≤ a.natAbs} := by
        rw [Set.mem_ofPred_eq] at hx ⊢
        rwa [Equiv.neg_apply, Int.natAbs_neg]
      rw [if_neg hx, if_neg hx']
  have hg : ∀ x : ℤ, ‖K (-(x - y)) - K (-x)‖ₑ = f (-x) := by
    intro x
    rw [hf]
    rw [show -(x - y) = -x - (-y) by ring]
  simp_rw [hg]
  rw [key]
  exact hb

end Commons.Analysis.DiscreteCZ