import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# The Klein lift intertwines `rot4 O` with the Lorentz matrix `blockLast O`

For an orthogonal `4 × 4` matrix `O` (that is, `Oᵀ * O = 1`) the Klein lift of the hyperboloid
satisfies `hypOfKlein (rot4 O y) = blockLast O *ᵥ hypOfKlein y`: the linear map `rot4 O` that `O`
induces on the Klein ball is the restriction, to the null rays, of the Lorentz transformation
`blockLast O`.

The proof is a computation resting on two facts.

* `blockLast O` maps the null ray `ray y = (y, 1)` to the null ray `ray (rot4 O y)` — the last
  coordinate is untouched and the first four are multiplied by `O`.
* `rot4 O` preserves the Euclidean inner product (the general fact that an orthogonal matrix
  preserves the dot product), hence `‖rot4 O y‖² = ‖y‖²`, so the normalising factors
  `(√(1 - ‖·‖²))⁻¹` on the two sides agree.

No hypothesis `y ∈ ball` is needed: both sides are the same linear rescaling of the same ray.
-/

noncomputable section

namespace Work.HypModel

open scoped Matrix InnerProductSpace

/-- `rot4 O` is multiplication by `O` on the coordinates of `E4`. -/
private theorem rot4_coe (O : Matrix (Fin 4) (Fin 4) ℝ) (y : E4) :
    (rot4 O y : Fin 4 → ℝ) = O *ᵥ (y : Fin 4 → ℝ) := by
  ext i
  fin_cases i <;> simp [rot4, Matrix.mulVec, dotProduct, Fin.sum_univ_four]

/-- `rot4 O` preserves the Euclidean inner product when `Oᵀ * O = 1`. -/
private theorem inner_rot4 {O : Matrix (Fin 4) (Fin 4) ℝ} (hO : O.transpose * O = 1) (u v : E4) :
    ⟪rot4 O u, rot4 O v⟫_ℝ = ⟪u, v⟫_ℝ := by
  rw [inner_eq_dotProduct, inner_eq_dotProduct, rot4_coe, rot4_coe]
  rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, hO,
    Matrix.one_mulVec]

/-- `blockLast O` carries the null ray over `y` to the null ray over `rot4 O y`. -/
private theorem blockLast_mulVec_ray (O : Matrix (Fin 4) (Fin 4) ℝ) (y : E4) :
    (blockLast O).mulVec (ray y) = ray (rot4 O y) := by
  ext i
  fin_cases i <;>
    simp [blockLast, rot4, ray, Matrix.mulVec, dotProduct, Fin.sum_univ_five, Fin.sum_univ_four]

theorem hypOfKlein_blockLast {O : Matrix (Fin 4) (Fin 4) ℝ} (hO : O.transpose * O = 1) (y : E4) :
    hypOfKlein (rot4 O y) = (blockLast O).mulVec (hypOfKlein y) := by
  have hnorm : ‖rot4 O y‖ ^ 2 = ‖y‖ ^ 2 := by
    rw [← real_inner_self_eq_norm_sq, ← real_inner_self_eq_norm_sq]
    exact inner_rot4 hO y y
  simp only [hypOfKlein]
  rw [Matrix.mulVec_smul, blockLast_mulVec_ray, hnorm]

end Work.HypModel
