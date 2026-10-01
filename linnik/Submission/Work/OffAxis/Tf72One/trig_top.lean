import Mathlib
import Submission.Work.ZeroFreeTables.XY.CosTayAbs
import Submission.Work.ZeroFreeTables.XY.SinTayAbs

open scoped BigOperators

namespace Work.OffAxis.Tf72One

/-- The Taylor bound `CosTayAbs` turns a rational enclosure of
`(partial sum) ± (remainder bound)` into a rational enclosure of `Real.cos θ`. -/
theorem cos_bounds_of_tay (θ : ℝ) (N : ℕ) (lo hi : ℝ)
    (hlo : lo ≤ (∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial))
        - |θ|^(2*N+2)/((2*N+2).factorial))
    (hhi : (∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k)/((2*k).factorial))
        + |θ|^(2*N+2)/((2*N+2).factorial) ≤ hi) :
    lo ≤ Real.cos θ ∧ Real.cos θ ≤ hi := by
  obtain ⟨h1, h2⟩ := abs_sub_le_iff.mp (Work.ZeroFreeTables.XY.CosTayAbs θ N)
  exact ⟨by linarith, by linarith⟩

/-- The Taylor bound `SinTayAbs` turns a rational enclosure of
`(partial sum) ± (remainder bound)` into a rational enclosure of `Real.sin θ`. -/
theorem sin_bounds_of_tay (θ : ℝ) (N : ℕ) (lo hi : ℝ)
    (hlo : lo ≤ (∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k+1)/((2*k+1).factorial))
        - |θ|^(2*N+2)/((2*N+2).factorial))
    (hhi : (∑ k ∈ Finset.range (N+1), (-1:ℝ)^k * θ^(2*k+1)/((2*k+1).factorial))
        + |θ|^(2*N+2)/((2*N+2).factorial) ≤ hi) :
    lo ≤ Real.sin θ ∧ Real.sin θ ≤ hi := by
  obtain ⟨h1, h2⟩ := abs_sub_le_iff.mp (Work.ZeroFreeTables.XY.SinTayAbs θ N)
  exact ⟨by linarith, by linarith⟩

theorem cos_44_5 :
    (-8111931/10000000 : ℝ) ≤ Real.cos (44/5 : ℝ) ∧
      Real.cos (44/5 : ℝ) ≤ (-810993/1000000 : ℝ) := by
  refine cos_bounds_of_tay (44/5) 15 _ _ ?_ ?_ <;> norm_num [Finset.sum_range_succ]

theorem sin_44_5 :
    (5848171/10000000 : ℝ) ≤ Real.sin (44/5 : ℝ) ∧
      Real.sin (44/5 : ℝ) ≤ (5850173/10000000 : ℝ) := by
  refine sin_bounds_of_tay (44/5) 15 _ _ ?_ ?_ <;> norm_num [Finset.sum_range_succ]

theorem cos_46_5 :
    (-9749437/10000000 : ℝ) ≤ Real.cos (46/5 : ℝ) ∧
      Real.cos (46/5 : ℝ) ≤ (-9747436/10000000 : ℝ) := by
  refine cos_bounds_of_tay (46/5) 15 _ _ ?_ ?_ <;> norm_num [Finset.sum_range_succ]

theorem sin_46_5 :
    (2227899/10000000 : ℝ) ≤ Real.sin (46/5 : ℝ) ∧
      Real.sin (46/5 : ℝ) ≤ (22299/100000 : ℝ) := by
  refine sin_bounds_of_tay (46/5) 15 _ _ ?_ ?_ <;> norm_num [Finset.sum_range_succ]

theorem cos_48_5 :
    (-9847879/10000000 : ℝ) ≤ Real.cos (48/5 : ℝ) ∧
      Real.cos (48/5 : ℝ) ≤ (-9845877/10000000 : ℝ) := by
  refine cos_bounds_of_tay (48/5) 16 _ _ ?_ ?_ <;> norm_num [Finset.sum_range_succ]

theorem sin_48_5 :
    (-1744269/10000000 : ℝ) ≤ Real.sin (48/5 : ℝ) ∧
      Real.sin (48/5 : ℝ) ≤ (-1742267/10000000 : ℝ) := by
  refine sin_bounds_of_tay (48/5) 16 _ _ ?_ ?_ <;> norm_num [Finset.sum_range_succ]

theorem cos_10 :
    (-8391716/10000000 : ℝ) ≤ Real.cos (10 : ℝ) ∧
      Real.cos (10 : ℝ) ≤ (-8389711/10000000 : ℝ) := by
  refine cos_bounds_of_tay (10 : ℝ) 16 _ _ ?_ ?_ <;> norm_num [Finset.sum_range_succ]

theorem sin_10 :
    (-5441213/10000000 : ℝ) ≤ Real.sin (10 : ℝ) ∧
      Real.sin (10 : ℝ) ≤ (-5439208/10000000 : ℝ) := by
  refine sin_bounds_of_tay (10 : ℝ) 16 _ _ ?_ ?_ <;> norm_num [Finset.sum_range_succ]

/-- Rational enclosures (width `2·10⁻⁴`) of `cos θ`, `sin θ` at `θ = 44/5, 46/5, 48/5, 10`. -/
theorem trig_top : (-8111931/10000000 : ℝ) ≤ Real.cos (44/5 : ℝ) ∧ Real.cos (44/5 : ℝ) ≤ (-810993/1000000 : ℝ) ∧ (5848171/10000000 : ℝ) ≤ Real.sin (44/5 : ℝ) ∧ Real.sin (44/5 : ℝ) ≤ (5850173/10000000 : ℝ) ∧
  (-9749437/10000000 : ℝ) ≤ Real.cos (46/5 : ℝ) ∧ Real.cos (46/5 : ℝ) ≤ (-9747436/10000000 : ℝ) ∧ (2227899/10000000 : ℝ) ≤ Real.sin (46/5 : ℝ) ∧ Real.sin (46/5 : ℝ) ≤ (22299/100000 : ℝ) ∧
  (-9847879/10000000 : ℝ) ≤ Real.cos (48/5 : ℝ) ∧ Real.cos (48/5 : ℝ) ≤ (-9845877/10000000 : ℝ) ∧ (-1744269/10000000 : ℝ) ≤ Real.sin (48/5 : ℝ) ∧ Real.sin (48/5 : ℝ) ≤ (-1742267/10000000 : ℝ) ∧
  (-8391716/10000000 : ℝ) ≤ Real.cos (10 : ℝ) ∧ Real.cos (10 : ℝ) ≤ (-8389711/10000000 : ℝ) ∧ (-5441213/10000000 : ℝ) ≤ Real.sin (10 : ℝ) ∧ Real.sin (10 : ℝ) ≤ (-5439208/10000000 : ℝ) := by
  exact ⟨cos_44_5.1, cos_44_5.2, sin_44_5.1, sin_44_5.2,
    cos_46_5.1, cos_46_5.2, sin_46_5.1, sin_46_5.2,
    cos_48_5.1, cos_48_5.2, sin_48_5.1, sin_48_5.2,
    cos_10.1, cos_10.2, sin_10.1, sin_10.2⟩

end Work.OffAxis.Tf72One
