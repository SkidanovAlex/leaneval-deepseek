import Mathlib
import Submission.Work.LT.gb_rank_defs

/-!
# `ker (v ↦ xᵀ * v) = (colSpan x)^⊥` for the dot-product form

Auxiliary lemma for Kalachev--Panteleev Lemma 8 (as used in `Work.LT.gb_rank_le`).

For the standard dot product `GB.dot u v = ∑ i, u i * v i` on `Fin D → ZMod 2`, the
transpose of a matrix is the adjoint of multiplication by `x`:

  `GB.dot (GB.matVec (GB.matTranspose x) u) v = GB.dot u (GB.matVec x v)`.

Consequently the kernel of `v ↦ xᵀ * v` is the orthogonal complement (with respect to
the bilinear form `GB.dotForm D`, whose dot product is non-degenerate) of the column
space of `x`.  This is the step that turns "`u ⊥ colSpan x`" into "`xᵀ u = 0`", and
dually it lets one read off `dim ker (xᵀ) = D - matRank x`.
-/

namespace Work.LT

namespace GB

/-- Pairing a vector `w` with the `j`-th column of `x` gives the `j`-th coordinate of
`xᵀ * w`: the matrix transpose is the adjoint of the matrix-vector product for the dot
product `GB.dot`. -/
lemma dot_col_eq_matVec_transpose {D : ℕ} (x : Fin D × Fin D → ZMod 2)
    (w : Fin D → ZMod 2) (j : Fin D) :
    dot (col x j) w = matVec (matTranspose x) w j := by
  simp only [dot, col, matVec, matTranspose_apply]

end GB

/-- (file `Submission/Work/LT/gb_ker_matVecLin_transpose.lean`, inside `namespace Work.LT` / `namespace GB`, importing `Submission.Work.LT.gb_rank_defs`) The kernel of `v ↦ xᵀ * v` is the orthogonal complement (with respect to the dot product bilinear form `GB.dotForm D`, so `w ∈ (GB.dotForm D).orthogonal C ↔ ∀ c ∈ C, GB.dot c w = 0`) of the column space of `x`. -/
lemma gb_ker_matVecLin_transpose {D : ℕ} (x : Fin D × Fin D → ZMod 2) :
    LinearMap.ker (GB.matVecLin (GB.matTranspose x)) = (GB.dotForm D).orthogonal (GB.colSpan x) := by
  ext w
  simp only [LinearMap.mem_ker, LinearMap.BilinForm.orthogonal, Submodule.mem_orthogonalBilin,
    GB.dotForm_apply, GB.matVecLin_apply]
  constructor
  · -- `xᵀ * w = 0` kills the whole column space: on the generators this is
    -- `GB.dot_col_eq_matVec_transpose`, and it propagates by linearity in the first argument
    -- (via `GB.dotLin`, exploiting symmetry of the dot product).
    intro h n hn
    have hle : GB.colSpan x ≤ LinearMap.ker (GB.dotLin w) := by
      rw [GB.colSpan_le_iff]
      intro j
      rw [LinearMap.mem_ker, show GB.dotLin w (GB.col x j) = GB.dot w (GB.col x j) from rfl,
        GB.dot_comm, GB.dot_col_eq_matVec_transpose]
      simpa using congr_fun h j
    have h1 := hle hn
    rw [LinearMap.mem_ker] at h1
    rw [GB.dot_comm]
    exact h1
  · -- conversely, if `w` is orthogonal to every column then each coordinate of `xᵀ * w`
    -- is a pairing with a column, hence vanishes.
    intro h
    funext j
    exact (GB.dot_col_eq_matVec_transpose x w j).symm.trans
      (h (GB.col x j) (GB.col_mem_colSpan x j))

end Work.LT
