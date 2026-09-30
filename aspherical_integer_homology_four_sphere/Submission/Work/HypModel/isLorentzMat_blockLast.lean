import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

open scoped Matrix InnerProductSpace
open Matrix

/-- The block extension `diag(O, 1)` of an orthogonal `4 × 4` matrix `O` is a Lorentz
transformation of `ℝ^{1,4}`.

`blockLast O` is the `5 × 5` matrix `diag(O, 1)`: the top-left `4 × 4` block is `O` and the last
coordinate is fixed.  Its transpose is `diag(Oᵀ, 1)`, hence

`(blockLast O)ᵀ J (blockLast O) = diag(Oᵀ, 1) · diag(1,1,1,1,-1) · diag(O, 1)
                              = diag(Oᵀ O, -1) = diag(1,1,1,1,-1) = J`

because `Oᵀ O = 1` (the last diagonal entry of `J` being `-1` precisely cancels the `1` of
`blockLast`).  The positivity condition is `(blockLast O) 4 4 = 1 > 0`.

Both conditions are checked entrywise: `hOO` records the orthonormality of the columns of `O`
(`(Oᵀ O) i j = ∑ k, O k i * O k j`), and `key` is its four-term form, which is exactly the shape in
which the `4 × 4` block of the product appears after unfolding the sums over `Fin 5`. -/
theorem isLorentzMat_blockLast {O : Matrix (Fin 4) (Fin 4) ℝ} (hO : O.transpose * O = 1) :
    IsLorentzMat (blockLast O) := by
  -- The entries of `Oᵀ O = 1`: an orthonormality relation for the columns of `O`.
  have hOO : ∀ i j : Fin 4, (∑ k : Fin 4, O k i * O k j) = if i = j then 1 else 0 := by
    intro i j
    have h := congr_fun (congr_fun hO i) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_four] using h
  -- The same relation, in the unfolded four-term form produced by `Fin.sum_univ_five`.
  have key : ∀ i j : Fin 4, O 0 i * O 0 j + O 1 i * O 1 j + O 2 i * O 2 j + O 3 i * O 3 j
      = if i = j then 1 else 0 := by
    intro i j
    have h := hOO i j
    simpa [Fin.sum_univ_four] using h
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [blockLast, Matrix.mul_apply, Fin.sum_univ_five, Matrix.transpose_apply, J, key]
  · simp [blockLast]

end Work.HypModel
