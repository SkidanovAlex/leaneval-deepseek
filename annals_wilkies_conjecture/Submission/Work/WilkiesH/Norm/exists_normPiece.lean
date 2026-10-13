import Mathlib
import Submission.Work.WilkiesH.Norm.Defs

namespace Work.WilkiesH.Norm

/-- For each real number, a shape whose region contains it.  The four regions
`(-∞,-1)`, `[-1,0]`, `[0,1]`, `(1,∞)` cover `ℝ`. -/
noncomputable def shapeOf (t : ℝ) : NormShape :=
  if t < -1 then .bigNeg else if t ≤ 0 then .neg else if t ≤ 1 then .pos else .big

lemma mem_shapeSet_shapeOf (t : ℝ) : t ∈ shapeSet (shapeOf t) := by
  unfold shapeOf
  split_ifs with h1 h2 h3
  · exact h1
  · exact ⟨not_lt.mp h1, h2⟩
  · exact ⟨le_of_lt (not_le.mp h2), h3⟩
  · exact not_le.mp h3

theorem exists_normPiece (n : ℕ) (x : Fin n → ℝ) : ∃ σ : Fin n → NormShape, x ∈ normPiece σ :=
  ⟨fun i => shapeOf (x i), fun i => mem_shapeSet_shapeOf (x i)⟩

end Work.WilkiesH.Norm
