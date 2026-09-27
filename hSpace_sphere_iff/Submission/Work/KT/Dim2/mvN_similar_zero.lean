import Mathlib

namespace Work.KT.Dim2

open Matrix

/-- MvN-equivalent idempotents `p`, `q` become conjugate after adding zero blocks: the explicit
Morita matrix `[[1-p, b],[a, q-1]]` is an involution intertwining `diag(0,q)` and `diag(p,0)`. -/
theorem mvN_similar_zero {R : Type} [Ring R] {n m : ℕ}
    (p : Matrix (Fin n) (Fin n) R) (q : Matrix (Fin m) (Fin m) R)
    (hp : p * p = p) (hq : q * q = q)
    (a : Matrix (Fin m) (Fin n) R) (b : Matrix (Fin n) (Fin m) R)
    (ha : b * a = p) (hb : a * b = q) :
    ∃ u : Matrix (Fin (n + m)) (Fin (n + m)) R,
      u * u = 1 ∧
      u * Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 0 0 0 q) * u =
        Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks p 0 0 0) := by
  -- Auxiliary identities relating the off-diagonal blocks.
  have hpb : p * b = b * q := by rw [← ha, ← hb]; exact Matrix.mul_assoc b a b
  have hqa : q * a = a * p := by rw [← hb, ← ha]; exact Matrix.mul_assoc a b a
  -- The four blocks of `U * U`, where `U = [[1-p, b], [a, q-1]]`.
  have h1 : (1 - p) * (1 - p) + b * a = 1 := by
    have hpp : (1 - p) * (1 - p) = 1 - p := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hp]; abel
    rw [hpp, ha]; abel
  have h2 : (1 - p) * b + b * (q - 1) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hpb]; abel
  have h3 : a * (1 - p) + (q - 1) * a = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.one_mul, hqa]; abel
  have h4 : a * b + (q - 1) * (q - 1) = 1 := by
    have hqq : (q - 1) * (q - 1) = 1 - q := by
      rw [Matrix.sub_mul, Matrix.one_mul, Matrix.mul_sub, Matrix.mul_one, hq]; abel
    rw [hqq, hb]; abel
  -- The four blocks of `U * D * U`, where `D = [[0, 0], [0, q]]`.
  have h5 : b * q * a = p := by
    rw [← hb, ← Matrix.mul_assoc b a b, Matrix.mul_assoc (b * a) b a, ha, hp]
  have h6 : b * q * (q - 1) = 0 := by
    rw [Matrix.mul_sub, Matrix.mul_one, Matrix.mul_assoc b q q, hq, sub_self]
  have h7 : (q - 1) * q * a = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hq, sub_self, Matrix.zero_mul]
  have h8 : (q - 1) * q * (q - 1) = 0 := by
    rw [Matrix.sub_mul, Matrix.one_mul, hq, sub_self, Matrix.zero_mul]
  -- Block computations in the `⊕`-indexed world.
  have hUU : Matrix.fromBlocks (1 - p) b a (q - 1) * Matrix.fromBlocks (1 - p) b a (q - 1) = 1 := by
    rw [Matrix.fromBlocks_multiply, ← Matrix.fromBlocks_one, Matrix.fromBlocks_inj]
    exact ⟨h1, h2, h3, h4⟩
  have hUDU : Matrix.fromBlocks (1 - p) b a (q - 1) * Matrix.fromBlocks 0 0 0 q
      * Matrix.fromBlocks (1 - p) b a (q - 1) = Matrix.fromBlocks p 0 0 0 := by
    rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp only [Matrix.zero_mul, Matrix.mul_zero, zero_add]
    rw [Matrix.fromBlocks_inj]
    exact ⟨h5, h6, h7, h8⟩
  -- Transport to `Fin (n+m)` via the reindexing ring equivalence.
  refine ⟨Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks (1 - p) b a (q - 1)),
    ?_, ?_⟩
  · rw [← Matrix.coe_reindexRingEquiv (R := R) (e := finSumFinEquiv), ← map_mul, hUU, map_one]
  · rw [← Matrix.coe_reindexRingEquiv (R := R) (e := finSumFinEquiv)]
    rw [← map_mul, ← map_mul, hUDU]

end Work.KT.Dim2
