import Mathlib
import Submission.Work.RTOwed.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Klein action composes with the inverse of a Lorentz matrix

The Klein model action of a Lorentz matrix `K` is

`mobiusKlein K y = uhsOfHyp (K *ᵥ hypOfKlein y)`.

If `K₁` and `K₂` are two Lorentz matrices and `y` a point of the open unit ball, then

`mobiusKlein K₂ y = mobius (K₂ * K₁⁻¹) (mobiusKlein K₁ y)`.

Interpreted backwards this says that *the Möbius transformation carrying the `K₁`-chart of `y` to
the `K₂`-chart of `y` is `mobius (K₂ K₁⁻¹)`*: this is exactly the shape of a transition function of
the fold charts, where the two developing matrices `N_j D_s` and `N_i D_r` play the roles of `K₂`
and `K₁` (`Work.RTOwed.transMat`).

Both sides are computed from the "inverse" direction of the fold maps (a `mobiusKlein` returns an
upper half space point, and the second `K`-action is a `mobius`).  The proof is the standard one:
the two maps `hypOfKlein`/`hypOfUHS` and `uhsOfHyp` are mutually inverse on the upper sheet of the
hyperboloid, and `*ᵥ` is associative with the matrix product, so the composite
`mobius (K₂ K₁⁻¹) ∘ mobiusKlein K₁` is `uhsOfHyp ∘ (K₂ K₁⁻¹) ∘ K₁ ∘ hypOfKlein`, which reduces to
`uhsOfHyp ∘ K₂ ∘ hypOfKlein` once `K₁⁻¹ * K₁ = 1`.

The only algebraic input is that a Lorentz matrix is invertible (`Aᵀ J A = J` forces
`(det A)² = 1`), which we record below.
-/

noncomputable section

open scoped Matrix

namespace Work.RTOwed

/-- The determinant of the Lorentz Gram matrix `J = diag(1,1,1,1,−1)` is `−1`. -/
theorem det_J_eq_neg_one : Matrix.det (Work.HypModel.J) = -1 := by
  rw [Work.HypModel.J, Matrix.det_diagonal]
  norm_num

/-- **A Lorentz matrix is invertible.**  Taking determinants in `Aᵀ J A = J` gives
`A.det * J.det * A.det = J.det`, and since `J.det = −1 ≠ 0` this forces `A.det ≠ 0`. -/
theorem isUnit_det_of_isLorentzMat {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : Work.HypModel.IsLorentzMat A) : IsUnit A.det := by
  rw [isUnit_iff_ne_zero]
  intro h0
  have h : A.det * Work.HypModel.J.det * A.det = Work.HypModel.J.det := by
    calc A.det * Work.HypModel.J.det * A.det = (Aᵀ * Work.HypModel.J * A).det := by
          rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
      _ = Work.HypModel.J.det := by rw [hA.1]
  rw [det_J_eq_neg_one, h0] at h
  norm_num at h

/-- **The `nonsing_inv` of a Lorentz matrix is a left inverse: `A⁻¹ * A = 1`.** -/
theorem nonsing_inv_mul_self_of_isLorentzMat {A : Matrix (Fin 5) (Fin 5) ℝ}
    (hA : Work.HypModel.IsLorentzMat A) : A⁻¹ * A = 1 :=
  Matrix.nonsing_inv_mul A (isUnit_det_of_isLorentzMat hA)

/-- **The Klein action of `K₂` is the Möbius action of `K₂ K₁⁻¹` applied to the Klein action of
`K₁`.**  For `w` in the open unit ball and `K₁, K₂` Lorentz matrices,
`mobiusKlein K₂ w = mobius (K₂ * K₁⁻¹) (mobiusKlein K₁ w)`.

This is the identity behind the fold-chart transition `transMat i j r s`, where
`K₁ = N_i D_r` and `K₂ = N_j D_s`. -/
theorem mobiusKlein_eq_mobius {K₁ K₂ : Matrix (Fin 5) (Fin 5) ℝ}
    (h₁ : Work.HypModel.IsLorentzMat K₁) (h₂ : Work.HypModel.IsLorentzMat K₂)
    {w : Work.FoldInst.E4} (hw : w ∈ Work.HypModel.ball) :
    Work.HypModel.mobiusKlein K₂ w =
      Work.HypModel.mobius (K₂ * K₁⁻¹) (Work.HypModel.mobiusKlein K₁ w) := by
  -- `K₂ K₁⁻¹` is again a Lorentz matrix
  have hK : Work.HypModel.IsLorentzMat (K₂ * K₁⁻¹) :=
    h₂.mul (Work.FoldInst.isLorentzMat_inv h₁)
  -- multiplicativity of the Klein action, read backwards
  rw [← Work.HypModel.mobiusKlein_mul hK h₁ hw]
  congr 1
  -- `(K₂ K₁⁻¹) K₁ = K₂`, using `K₁⁻¹ K₁ = 1`
  rw [Matrix.mul_assoc, nonsing_inv_mul_self_of_isLorentzMat h₁, Matrix.mul_one]

end Work.RTOwed
