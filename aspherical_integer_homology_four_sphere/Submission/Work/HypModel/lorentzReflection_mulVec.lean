import Mathlib
import Submission.Work.HypModel.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

open scoped Matrix

/-- **The Lorentz reflection is a linear reflection.**  For every vector `x ∈ ℝ^{1,4}`,

`(lorentzReflection v) *ᵥ x = x − 2⟨x,v⟩/⟨v,v⟩ · v`.

Since `lorentzReflection v = 1 − (2/⟨v,v⟩) • (v ⊗ Jv)`, the product `(v ⊗ Jv) *ᵥ x` equals
`⟨x,v⟩ • v`; here `(J *ᵥ v) ⬝ x = x ⬝ (J *ᵥ v) = ⟨x,v⟩` by symmetry of the dot product. -/
theorem lorentzReflection_mulVec (v x : V5) (hv : lorentz v v ≠ 0) :
    (lorentzReflection v).mulVec x = x - (2 * lorentz x v / lorentz v v) • v := by
  ext i
  fin_cases i <;>
    simp [lorentzReflection, Matrix.mulVec, Matrix.vecMulVec_apply, dotProduct,
      Fin.sum_univ_five, J_mulVec, lorentz] <;>
    ring

end Work.HypModel
