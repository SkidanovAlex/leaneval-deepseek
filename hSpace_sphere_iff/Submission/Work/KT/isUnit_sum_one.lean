import Mathlib
import Submission.Work.KT.Defs

namespace Work.KT

/-- A block-diagonal matrix whose two diagonal blocks are the identity and a unit is a unit,
over an arbitrary ring (commutativity is not needed: the inverse is block-diagonal with the
inverse of the first block). -/
theorem isUnit_fromBlocks_diag {A : Type} [Ring A] {m k : ℕ}
    (u : (Matrix (Fin m) (Fin m) A)ˣ) :
    IsUnit (Matrix.fromBlocks (u : Matrix (Fin m) (Fin m) A) (0 : Matrix (Fin m) (Fin k) A)
      (0 : Matrix (Fin k) (Fin m) A) (1 : Matrix (Fin k) (Fin k) A)) := by
  refine ⟨⟨Matrix.fromBlocks (u : Matrix (Fin m) (Fin m) A) (0 : Matrix (Fin m) (Fin k) A)
      (0 : Matrix (Fin k) (Fin m) A) (1 : Matrix (Fin k) (Fin k) A),
    Matrix.fromBlocks (↑u⁻¹ : Matrix (Fin m) (Fin m) A) (0 : Matrix (Fin m) (Fin k) A)
      (0 : Matrix (Fin k) (Fin m) A) (1 : Matrix (Fin k) (Fin k) A), ?_, ?_⟩, rfl⟩
  · rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]
  · rw [Matrix.fromBlocks_multiply]; simp [Matrix.fromBlocks_one]

/-- `γ ⊕ 1_k` is invertible if `γ` is, for any ring. -/
theorem isUnit_sum_one {A : Type} [Ring A] {m k : ℕ} {γ : Matrix (Fin m) (Fin m) A}
    (hγ : IsUnit γ) : IsUnit ((Mat.sum ⟨m, γ⟩ (Mat.one A k)).2) := by
  obtain ⟨u, hu⟩ := hγ
  rw [← hu]
  refine IsUnit.map (Matrix.reindexRingEquiv A finSumFinEquiv) ?_
  exact isUnit_fromBlocks_diag u

end Work.KT
