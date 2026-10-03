import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Data.Int.Star
import Mathlib.MeasureTheory.Measure.Count

namespace Commons.Analysis.DiscreteCZ

open MeasureTheory Set
open scoped ENNReal BigOperators

/-- The counting measure of `{x : ℤ | |x - c| < R}` is at most `2R`. -/
theorem count_natAbs_lt_le (c : ℤ) (R : ℕ) :
    MeasureTheory.Measure.count {x : ℤ | (x - c).natAbs < R}
      ≤ ((2 * R : ℕ) : ℝ≥0∞) := by
  have hsub : {x : ℤ | (x - c).natAbs < R}
      ⊆ (Finset.Icc (c - (R : ℤ) + 1) (c + (R : ℤ) - 1) : Set ℤ) := by
    intro x hx
    rw [Finset.mem_coe, Finset.mem_Icc]
    have h1 : ((x - c).natAbs : ℤ) < (R : ℤ) := by exact_mod_cast hx
    rw [Int.natCast_natAbs, abs_lt] at h1
    obtain ⟨h1a, h1b⟩ := h1
    constructor <;> omega
  calc MeasureTheory.Measure.count {x : ℤ | (x - c).natAbs < R}
      ≤ MeasureTheory.Measure.count
          ((Finset.Icc (c - (R : ℤ) + 1) (c + (R : ℤ) - 1) : Finset ℤ) : Set ℤ) :=
        measure_mono hsub
    _ = ((Finset.Icc (c - (R : ℤ) + 1) (c + (R : ℤ) - 1) : Finset ℤ).card : ℝ≥0∞) :=
        MeasureTheory.Measure.count_apply_finset _
    _ ≤ ((2 * R : ℕ) : ℝ≥0∞) := by
        rw [Nat.cast_le]
        rw [Int.card_Icc]
        apply Int.toNat_le.mpr
        push_cast
        linarith

end Commons.Analysis.DiscreteCZ