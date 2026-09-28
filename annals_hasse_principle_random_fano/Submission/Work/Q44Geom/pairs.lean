import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.Q44Geom.defs

/-!
# Planes through `ℓ` and directions in a complement

Given independent `b₁ b₂` in `ℚ⁵` and a family `w : Fin 3 → ℚ⁵` such that `(w, b₁, b₂)` is a
basis of `ℚ⁵`, the `3`-dimensional subspaces `P` containing `b₁` and `b₂` are exactly the
subspaces `span{b₁,b₂} ⊔ toV w L` for a unique `1`-dimensional `L ⊆ ℚ³` (`uniqueDirection`).
-/

set_option autoImplicit false
set_option linter.unusedVariables false
noncomputable section

open MvPolynomial

namespace Work.Q44Geom

/-- The parametrisation `p ↦ Σ_a p_a • w a`. -/
def toV (w : Fin 3 → Fin 5 → ℚ) : (Fin 3 → ℚ) →ₗ[ℚ] (Fin 5 → ℚ) where
  toFun p := ∑ a : Fin 3, p a • w a
  map_add' p q := by
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
  map_smul' c p := by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_smul, Finset.smul_sum]

theorem toV_apply (w : Fin 3 → Fin 5 → ℚ) (p : Fin 3 → ℚ) :
    toV w p = ∑ a : Fin 3, p a • w a := rfl

end Work.Q44Geom
