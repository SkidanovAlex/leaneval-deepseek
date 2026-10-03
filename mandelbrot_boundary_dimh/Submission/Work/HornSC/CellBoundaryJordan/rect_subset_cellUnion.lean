import Mathlib
import Submission.Work.HornSC.CellBoundaryJordan.BlockDefs

namespace Work.HornSC.CellBoundaryJordan

open Set

/-- One-dimensional covering: if `a < c` are integers and the real `x` satisfies
`a ≤ x ≤ c`, then `x` lies in the closed unit interval `[p, p+1]` for some integer
`p` with `a ≤ p < c`.  The intervals `[p,p+1]`, `a ≤ p < c`, tile `[a,c]`. -/
lemma exists_int_cover {a c : ℤ} {x : ℝ} (hac : a < c) (hlo : (a : ℝ) ≤ x)
    (hhi : x ≤ (c : ℝ)) :
    ∃ p : ℤ, a ≤ p ∧ p < c ∧ (p : ℝ) ≤ x ∧ x ≤ (p : ℝ) + 1 := by
  by_cases hfc : ⌊x⌋ < c
  · exact ⟨⌊x⌋, Int.le_floor.mpr hlo, hfc, Int.floor_le x,
      le_of_lt (Int.lt_floor_add_one x)⟩
  · push Not at hfc
    have hge : (c : ℝ) ≤ x := by
      have h2 : (c : ℝ) ≤ (⌊x⌋ : ℝ) := by exact_mod_cast hfc
      linarith [Int.floor_le x]
    refine ⟨c - 1, by omega, by omega, ?_, ?_⟩
    · push_cast; linarith
    · push_cast; linarith

lemma rect_subset_cellUnion {A : Finset (ℤ × ℤ)} {a c b d : ℤ} (hac : a < c) (hbd : b < d)
    (h : RectBlock A a c b d) :
    {w : ℂ | (a : ℝ) ≤ w.re ∧ w.re ≤ (c : ℝ) ∧ (b : ℝ) ≤ w.im ∧ w.im ≤ (d : ℝ)} ⊆
      cellUnion A := by
  intro w hw
  obtain ⟨hw1, hw2, hw3, hw4⟩ := hw
  obtain ⟨p1, hp1a, hp1c, hp1lo, hp1hi⟩ := exists_int_cover hac hw1 hw2
  obtain ⟨p2, hp2b, hp2d, hp2lo, hp2hi⟩ := exists_int_cover hbd hw3 hw4
  refine Set.mem_iUnion₂.mpr ⟨(p1, p2), h p1 p2 hp1a hp1c hp2b hp2d, ?_⟩
  exact mem_cell.mpr ⟨hp1lo, hp1hi, hp2lo, hp2hi⟩

end Work.HornSC.CellBoundaryJordan
