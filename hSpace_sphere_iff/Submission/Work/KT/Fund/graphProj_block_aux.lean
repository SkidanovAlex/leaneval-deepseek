import Mathlib

/-!
# `Work.KT.Fund.graphProj_block_aux`

Two general facts about the totalized inverse `Ring.inverse` that the block decomposition of
`Work.KT.Fund.graphProj` rests on: it commutes with a ring equivalence (in particular with
`Matrix.reindex`), and it respects block diagonal matrices made of two units.
-/

namespace Work.KT.Fund

open Matrix

/-- `Ring.inverse` commutes with a ring equivalence. -/
theorem ringInverse_ringEquiv {R S : Type*} [Ring R] [Ring S] (f : R ≃+* S) (x : R) :
    Ring.inverse (f x) = f (Ring.inverse x) := by
  by_cases h : IsUnit x
  · obtain ⟨u, rfl⟩ := h
    have e1 : f (↑u : R) = ↑(Units.map (f : R →* S) u) := (Units.coe_map (f : R →* S) u).symm
    rw [e1, Ring.inverse_unit, Ring.inverse_unit]
    exact Units.coe_map_inv (f : R →* S) u
  · have hfx : ¬ IsUnit (f x) := fun hf =>
      h (by simpa using IsUnit.map (f.symm : S →* R) hf)
    rw [Ring.inverse_non_unit x h, Ring.inverse_non_unit (f x) hfx, map_zero]

/-- `Ring.inverse` commutes with `Matrix.reindex`. -/
theorem Matrix.ringInverse_reindex {R : Type*} [Ring R] {m n : Type*} [Fintype m] [DecidableEq m]
    [Fintype n] [DecidableEq n] (e : m ≃ n) (M : Matrix m m R) :
    Ring.inverse (Matrix.reindex e e M) = Matrix.reindex e e (Ring.inverse M) := by
  rw [← Matrix.coe_reindexRingEquiv R e]
  exact ringInverse_ringEquiv (Matrix.reindexRingEquiv R e) M

/-- `Ring.inverse` of a block diagonal matrix with invertible diagonal blocks. -/
theorem ringInverse_fromBlocks_diag {R : Type*} [Semiring R] {m n : Type*} [Fintype m] [Fintype n]
    [DecidableEq m] [DecidableEq n] (A : Matrix m m R) (B : Matrix n n R)
    (hA : IsUnit A) (hB : IsUnit B) :
    Ring.inverse (Matrix.fromBlocks A 0 0 B) =
      Matrix.fromBlocks (Ring.inverse A) 0 0 (Ring.inverse B) := by
  let u : (Matrix (m ⊕ n) (m ⊕ n) R)ˣ :=
    { val := Matrix.fromBlocks A 0 0 B
      inv := Matrix.fromBlocks (Ring.inverse A) 0 0 (Ring.inverse B)
      val_inv := by
        rw [Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
          Ring.mul_inverse_cancel A hA, Ring.mul_inverse_cancel B hB, Matrix.fromBlocks_one]
      inv_val := by
        rw [Matrix.fromBlocks_multiply]
        simp only [Matrix.mul_zero, Matrix.zero_mul, add_zero, zero_add,
          Ring.inverse_mul_cancel A hA, Ring.inverse_mul_cancel B hB, Matrix.fromBlocks_one] }
  rw [Ring.inverse_unit u]
  rfl

end Work.KT.Fund
