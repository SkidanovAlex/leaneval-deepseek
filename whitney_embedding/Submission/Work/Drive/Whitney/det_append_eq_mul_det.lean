import Mathlib

-- The hypothesis `hb` is part of the requested statement; the identity proved below is in fact
-- unconditional (pure multilinearity of `Basis.det`), so `hb` is deliberately not used.
set_option linter.unusedVariables false

namespace Work.Drive.Whitney

/-- **The determinant of a family completed along a complement frame.**

Let `b₀` be a basis of `F` indexed by `Fin (r + k)`, let `v : Fin r → F`, `n : Fin k → F` be such
that the concatenation `Fin.append v n` is linearly independent, and let `U : Fin k → F` be the
family whose coordinates in the basis `(v, n)` are given by the matrices `G : Matrix (Fin r) (Fin k)`
and `K : Matrix (Fin k) (Fin k)`, i.e. `U j = ∑ l, G l j • v l + ∑ i, K i j • n i`.  Then

`b₀.det (Fin.append v U) = b₀.det (Fin.append v n) * K.det`.

(Since `b₀` has `Fin (r+k)` indices and `Fin.append v n` is linearly independent, that family is a
basis, so `b₀.det (Fin.append v n) ≠ 0` and the identity shows that `Fin.append v U` is a basis iff
`K` is invertible.)

Proof: the linear map `L` with `L (v l) = v l` and `L (n i) = U i` satisfies
`Fin.append v U = L ∘ Fin.append v n`, so `Basis.det_comp` gives
`b₀.det (Fin.append v U) = LinearMap.det L * b₀.det (Fin.append v n)`; the matrix of `L` in the
basis `Fin.append v n` is the block matrix `[[1, G], [0, K]]` (after reindexing `Fin (r+k)` along
`finSumFinEquiv`), whose determinant is `K.det` by `Matrix.det_fromBlocks_zero₂₁`.

Here the same computation is done with the coordinate matrices: with `w := Fin.append v n` and
`u := Fin.append v U`, the family `u` has, in the coordinates of the family `w`, the block matrix
`C = Matrix.reindex finSumFinEquiv finSumFinEquiv (Matrix.fromBlocks 1 G 0 K)`; that is
`b₀.toMatrix u = b₀.toMatrix w * C`, whence `b₀.det u = b₀.det w * C.det` because
`b₀.det = fun v => Matrix.det (b₀.toMatrix v)`, and `C.det = K.det` by `Matrix.det_reindex_self`
and `Matrix.det_fromBlocks_zero₂₁`.  Note that no linear independence is actually needed: the
identity is the multilinearity of `b₀.det` in the columns of a block-triangular coordinate matrix. -/
theorem det_append_eq_mul_det {F : Type*} [AddCommGroup F] [Module ℝ F] {r k : ℕ}
    (b₀ : Module.Basis (Fin (r + k)) ℝ F) {v : Fin r → F} {n : Fin k → F}
    (hb : LinearIndependent ℝ (Fin.append v n))
    (U : Fin k → F) (K : Matrix (Fin k) (Fin k) ℝ) (G : Matrix (Fin r) (Fin k) ℝ)
    (hU : ∀ j : Fin k, U j = (∑ l : Fin r, G l j • v l) + (∑ i : Fin k, K i j • n i)) :
    b₀.det (Fin.append v U) = b₀.det (Fin.append v n) * K.det := by
  classical
  set w : Fin (r + k) → F := Fin.append v n with hw
  set u : Fin (r + k) → F := Fin.append v U with hu
  -- the coordinate change matrix: the block matrix `[[1, G], [0, K]]`, reindexed to `Fin (r+k)`
  set M : Matrix (Fin r ⊕ Fin k) (Fin r ⊕ Fin k) ℝ :=
    Matrix.fromBlocks (1 : Matrix (Fin r) (Fin r) ℝ) G 0 K with hM
  set C : Matrix (Fin (r + k)) (Fin (r + k)) ℝ :=
    Matrix.reindex finSumFinEquiv finSumFinEquiv M with hC
  have hCapp : ∀ (a : Fin (r + k)) (j : Fin (r + k)),
      C a j = M (finSumFinEquiv.symm a) (finSumFinEquiv.symm j) := by
    intro a j
    rw [hC, Matrix.reindex_apply, Matrix.submatrix_apply]
  -- the key coordinates: `u` is the family `w` with columns given by the block matrix
  have hcoord : ∀ j : Fin (r + k), u j = ∑ a : Fin (r + k), C a j • w a := by
    intro j
    rcases hs : finSumFinEquiv.symm j with l' | i'
    · -- `j` is in the `v` block: the column is the corresponding unit vector
      have hj : j = finSumFinEquiv (Sum.inl l') := by rw [← hs, Equiv.apply_symm_apply]
      have hCj : ∀ a : Fin (r + k), C a (finSumFinEquiv (Sum.inl l'))
          = M (finSumFinEquiv.symm a) (Sum.inl l') := by
        intro a; rw [hCapp, Equiv.symm_apply_apply]
      rw [hj]
      simp only [hCj]
      rw [← Equiv.sum_comp finSumFinEquiv
        (fun a => M (finSumFinEquiv.symm a) (Sum.inl l') • w a)]
      simp only [Equiv.symm_apply_apply]
      rw [Fintype.sum_sum_type]
      simp only [hM, hu, hw, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.append_left, Fin.append_right, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₂₁]
      have h1 : (∑ x : Fin r, (1 : Matrix (Fin r) (Fin r) ℝ) x l' • v x) = v l' := by
        rw [Finset.sum_eq_single l']
        · simp
        · intro b _ hb; simp [hb]
        · intro h; exact absurd (Finset.mem_univ l') h
      have h2 : (∑ x : Fin k, (0 : Matrix (Fin k) (Fin r) ℝ) x l' • n x) = 0 := by simp
      rw [h1, h2, add_zero]
    · -- `j` is in the `n` block: the column is the `j`-th column of `[[1, G], [0, K]]`
      have hj : j = finSumFinEquiv (Sum.inr i') := by rw [← hs, Equiv.apply_symm_apply]
      have hCj : ∀ a : Fin (r + k), C a (finSumFinEquiv (Sum.inr i'))
          = M (finSumFinEquiv.symm a) (Sum.inr i') := by
        intro a; rw [hCapp, Equiv.symm_apply_apply]
      rw [hj]
      simp only [hCj]
      rw [← Equiv.sum_comp finSumFinEquiv
        (fun a => M (finSumFinEquiv.symm a) (Sum.inr i') • w a)]
      simp only [Equiv.symm_apply_apply]
      rw [Fintype.sum_sum_type]
      simp only [hM, hu, hw, finSumFinEquiv_apply_left, finSumFinEquiv_apply_right,
        Fin.append_left, Fin.append_right, hU i', Matrix.fromBlocks_apply₁₂,
        Matrix.fromBlocks_apply₂₂]
  -- the coordinate matrices of `u` and of `w` differ by right multiplication by `C`
  have hmat : b₀.toMatrix u = b₀.toMatrix w * C := by
    ext i j
    rw [Matrix.mul_apply, Module.Basis.toMatrix_apply]
    have key : (b₀.repr (u j)) i = (∑ a, C a j • b₀.repr (w a)) i := by
      rw [hcoord j, map_sum]
      simp only [map_smul]
    rw [key]
    simp only [Module.Basis.toMatrix_apply, Finsupp.coe_finsetSum, Finset.sum_apply,
      Finsupp.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl (fun a _ => mul_comm _ _)
  have hdet : C.det = K.det := by
    rw [hC, Matrix.det_reindex_self, hM, Matrix.det_fromBlocks_zero₂₁, Matrix.det_one, one_mul]
  rw [Module.Basis.det_apply, Module.Basis.det_apply, hmat, Matrix.det_mul, hdet]

end Work.Drive.Whitney
