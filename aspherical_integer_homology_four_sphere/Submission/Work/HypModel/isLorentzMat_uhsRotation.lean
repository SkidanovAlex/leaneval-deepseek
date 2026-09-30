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

/-- The rotation `x ↦ O x` of the horizontal coordinates of the upper half space model, `s` fixed,
is a Lorentz transformation whenever `O` is an orthogonal `3 × 3` matrix.

`uhsRotation O` is the block diagonal matrix `diag(O, 1, 1)`, so

`(uhsRotation O)ᵀ J (uhsRotation O) = diag(Oᵀ, 1, -1) · diag(O, 1, 1) = diag(Oᵀ O, 1, -1)`,

which is `diag(1,1,1,1,-1) = J` exactly because `Oᵀ O = 1`.  Both conditions of `IsLorentzMat`
are therefore direct computations: the identity is checked entrywise (the top-left `3 × 3` block
being the entries of `Oᵀ O = 1`), and the positivity condition is
`(uhsRotation O) 4 4 = 1 > 0`. -/
theorem isLorentzMat_uhsRotation {O : Matrix (Fin 3) (Fin 3) ℝ} (hO : O.transpose * O = 1) :
    IsLorentzMat (uhsRotation O) := by
  -- The entries of `Oᵀ O = 1`: an orthonormality relation for the columns of `O`.
  have hOO : ∀ i j : Fin 3, (∑ k : Fin 3, O k i * O k j) = if i = j then 1 else 0 := by
    intro i j
    have h := congr_fun (congr_fun hO i) j
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply, Fin.sum_univ_three] using h
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [uhsRotation, Matrix.mul_apply, Fin.sum_univ_five, Matrix.transpose_apply, J]
    all_goals first
      | simpa [Fin.sum_univ_three] using hOO 0 0
      | simpa [Fin.sum_univ_three] using hOO 0 1
      | simpa [Fin.sum_univ_three] using hOO 0 2
      | simpa [Fin.sum_univ_three] using hOO 1 0
      | simpa [Fin.sum_univ_three] using hOO 1 1
      | simpa [Fin.sum_univ_three] using hOO 1 2
      | simpa [Fin.sum_univ_three] using hOO 2 0
      | simpa [Fin.sum_univ_three] using hOO 2 1
      | simpa [Fin.sum_univ_three] using hOO 2 2
  · simp [uhsRotation]

end Work.HypModel
