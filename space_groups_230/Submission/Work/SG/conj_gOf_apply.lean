import Mathlib
import Submission.Work.SG.realize_defs

/-!
# Conjugating `gOf` back by `affInvLin`

`affInvLin M hM` is the affine map `y ↦ M⁻¹ y` and `gOf M A hO w` is the Euclidean motion
`x ↦ M A M⁻¹ x + M w`.  Conjugating the latter by `affInvLin M hM` therefore cancels the
change of basis `M` and gives the affine map `x ↦ A x + w`:

  `(affInvLin M hM) * gOf M A hO w * (affInvLin M hM)⁻¹ = x ↦ A x + w`.

The statement below records this pointwise.  Note that the orthogonal-matrix hypothesis `hO`
is irrelevant to the value of the composite: `gOf` evaluates the same way for any proof of
orthogonality, so the proof below never uses `hO`.
-/

namespace Work.SG

open LeanEval.Geometry.SpaceGroupsProblem

/-- For an invertible real `3 × 3` matrix `M`, `M⁻¹ (M z) = z`. -/
lemma mulVec_inv_mul (M : RMat) (hM : M.det ≠ 0) (z : Fin 3 → ℝ) :
    Matrix.mulVec M⁻¹ (Matrix.mulVec M z) = z := by
  rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul M (isUnit_iff_ne_zero.mpr hM),
    Matrix.one_mulVec]

/-- `(M A M⁻¹) (M y) = M (A y)`: the change of basis `M` conjugates the integer matrix `A`
into `oConj M A`, and the two factors cancel on a vector of the form `M y`. -/
lemma mulVec_oConj_mul (M : RMat) (hM : M.det ≠ 0) (A : IMat) (y : Fin 3 → ℝ) :
    Matrix.mulVec (oConj M A) (Matrix.mulVec M y)
      = Matrix.mulVec M (Matrix.mulVec (realMat A) y) := by
  rw [oConj, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_inv_mul M hM y]

theorem conj_gOf_apply (M : Work.SG.RMat) (hM : M.det ≠ 0) (A : Work.SG.IMat)
    (hO : Matrix.transpose (Work.SG.oConj M A) * (Work.SG.oConj M A) = 1)
    (w : Fin 3 → ℝ) (x : LeanEval.Geometry.SpaceGroupsProblem.E 3) :
    ((Work.SG.affInvLin M hM) * Work.SG.gOf M A hO w * (Work.SG.affInvLin M hM)⁻¹) x
      = WithLp.toLp 2 (Matrix.mulVec (Work.SG.realMat A) x.ofLp + w) := by
  -- `(f * g * h) x = f (g (h x))`
  simp only [AffineEquiv.coe_mul, Function.comp_apply]
  -- the middle factor is `gOf M A hO w` (coercions from `EuclideanIsom` to `AffineGroup`
  -- are definitionally the identity on the underlying function)
  change (affInvLin M hM) (gOf M A hO w ((affInvLin M hM)⁻¹ x))
    = WithLp.toLp 2 (Matrix.mulVec (realMat A) x.ofLp + w)
  -- evaluate the three affine maps
  rw [affInvLin_symm_apply, gOf_apply, affInvLin_apply]
  -- simplify `WithLp` coercions and distribute `M⁻¹ *ᵥ ·` over the sum
  simp only [WithLp.ofLp_add, Matrix.mulVec_add]
  -- `M⁻¹ (M A M⁻¹ (M x) + M w) = M⁻¹ ((M A M⁻¹) (M x)) + M⁻¹ (M w)`
  rw [mulVec_oConj_mul M hM A x.ofLp]
  simp only [mulVec_inv_mul M hM]

end Work.SG
