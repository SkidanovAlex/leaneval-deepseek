import Mathlib
import Submission.Work.KT.Psi.SubIncl
import Submission.Work.KT.Psi.clsM_eq_of_mvN
import Submission.Work.KT.Psi.mul_subIncl_mul_subInclT

/-!
# `Work.KT.Psi.clsM_submatrix` — the `K₀`-class of a matrix supported on a block

If an idempotent matrix `M` over a finite index type `ι` vanishes off the block determined by a
predicate `pr` on `ι` (`M i j = 0` whenever `¬ (pr i ∧ pr j)`), then its class in `K₀` is the class
of its `{i // pr i} × {i // pr i}`-minor.

The two matrices are Murray–von Neumann equivalent, with witnesses built from the inclusion matrix
`subIncl A pr : Matrix ι {i // pr i} A`:

* `u = (subIncl A pr)ᵀ * M : Matrix {i // pr i} ι A`,
* `v = M * subIncl A pr : Matrix ι {i // pr i} A`,

for which `v * u = M` (using `M * subIncl * (subIncl)ᵀ = M`, i.e. the hypothesis that `M` vanishes
off the block) and `u * v = M.submatrix Subtype.val Subtype.val` (using
`((subIncl A pr)ᵀ * M) * subIncl A pr = M.submatrix Subtype.val Subtype.val`).  The transport of
`clsM` along a Murray–von Neumann equivalence over two *different* index types is
`Work.KT.Psi.clsM_eq_of_mvN`.
-/

namespace Work.KT.Psi

open Matrix

noncomputable section

theorem clsM_submatrix {A : Type} [Ring A] {ι : Type} [Fintype ι]
    {pr : ι → Prop} [DecidablePred pr] (M : Matrix ι ι A) (hM : M * M = M)
    (hdiag : ∀ i j : ι, ¬ (pr i ∧ pr j) → M i j = 0) :
    Work.KT.Psi.clsM ι M = Work.KT.Psi.clsM {i // pr i} (M.submatrix Subtype.val Subtype.val) := by
  classical
  -- `v * u = M`
  have hvu : (M * subIncl A pr) * ((subIncl A pr)ᵀ * M) = M := by
    rw [← Matrix.mul_assoc (M * subIncl A pr) (subIncl A pr)ᵀ M,
      mul_subIncl_mul_subInclT (pr := pr) M hdiag, hM]
  -- `u * v` is the minor of `M`
  have huv : ((subIncl A pr)ᵀ * M) * (M * subIncl A pr) =
      M.submatrix Subtype.val Subtype.val := by
    rw [← Matrix.mul_assoc ((subIncl A pr)ᵀ * M) M (subIncl A pr),
      Matrix.mul_assoc (subIncl A pr)ᵀ M M, hM]
    exact subInclT_mul_subIncl pr M
  -- `u * M = u`
  have huM : ((subIncl A pr)ᵀ * M) * M = (subIncl A pr)ᵀ * M := by
    rw [Matrix.mul_assoc, hM]
  refine clsM_eq_of_mvN hM ?_ hvu huv
  -- the minor is idempotent: `(u*v)*(u*v) = u*(v*u)*v = u*M*v = (u*M)*v = u*v`
  calc (M.submatrix Subtype.val Subtype.val) * (M.submatrix Subtype.val Subtype.val)
      = (((subIncl A pr)ᵀ * M) * (M * subIncl A pr)) *
          (((subIncl A pr)ᵀ * M) * (M * subIncl A pr)) := by rw [huv]
    _ = ((subIncl A pr)ᵀ * M) *
          ((M * subIncl A pr) * (((subIncl A pr)ᵀ * M) * (M * subIncl A pr))) := by
        rw [Matrix.mul_assoc ((subIncl A pr)ᵀ * M) (M * subIncl A pr)
          (((subIncl A pr)ᵀ * M) * (M * subIncl A pr))]
    _ = ((subIncl A pr)ᵀ * M) *
          (((M * subIncl A pr) * ((subIncl A pr)ᵀ * M)) * (M * subIncl A pr)) := by
        rw [← Matrix.mul_assoc (M * subIncl A pr) ((subIncl A pr)ᵀ * M) (M * subIncl A pr)]
    _ = ((subIncl A pr)ᵀ * M) * (M * (M * subIncl A pr)) := by rw [hvu]
    _ = (((subIncl A pr)ᵀ * M) * M) * (M * subIncl A pr) :=
        (Matrix.mul_assoc ((subIncl A pr)ᵀ * M) M (M * subIncl A pr)).symm
    _ = ((subIncl A pr)ᵀ * M) * (M * subIncl A pr) := by rw [huM]
    _ = M.submatrix Subtype.val Subtype.val := huv

end

end Work.KT.Psi
