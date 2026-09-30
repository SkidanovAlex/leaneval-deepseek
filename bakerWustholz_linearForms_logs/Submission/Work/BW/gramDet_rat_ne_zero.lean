import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open Matrix

namespace Work.BW

/-- The Gram matrix of a `ℚ`-linearly independent family of rational vectors is nonsingular. -/
lemma gramDet_rat_ne_zero {n r : ℕ} (f : Fin r → Fin n → ℚ) (hf : LinearIndependent ℚ f) :
    (Matrix.of (fun a a' : Fin r => ∑ i, f a i * f a' i)).det ≠ 0 := by
  -- View `f` as a matrix `A` whose rows are the vectors `f a`.
  -- The Gram matrix is `A * Aᵀ = A * Aᴴ` (the star on `ℚ` is trivial).
  -- `A.vecMul x = ∑ a, x a • f a`, so linear independence of `f`
  -- says exactly that `A.vecMul` is injective.  Then `A * Aᴴ` is positive definite,
  -- hence has positive (in particular nonzero) determinant.
  have hvec : ∀ x : Fin r → ℚ, (Matrix.of f).vecMul x = ∑ a, x a • f a := by
    intro x
    rw [Matrix.vecMul_eq_sum]
    rfl
  have hInj : Function.Injective (Matrix.of f).vecMul := by
    rw [linearIndependent_iff_injective_fintypeLinearCombination] at hf
    intro x y hxy
    apply hf
    simpa only [Fintype.linearCombination_apply, hvec] using hxy
  have hpos : ((Matrix.of f) * (Matrix.of f)ᴴ).PosDef :=
    Matrix.PosDef.mul_conjTranspose_self _ hInj
  have hG : (Matrix.of f) * (Matrix.of f)ᴴ
      = Matrix.of (fun a a' : Fin r => ∑ i, f a i * f a' i) := by
    ext a b
    simp [Matrix.mul_apply]
  rw [← hG]
  exact ne_of_gt (Matrix.PosDef.det_pos hpos)

end Work.BW
