import Mathlib
import Submission.Work.LLink.Count
import Submission.Work.Reflect.PolyId
set_option maxRecDepth 100000

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.LLink

open CategoryTheory AlgebraicGeometry AlgebraicGeometry.Scheme MotivicInvariants Order

/-- The inverse of the inverse of a birational map is the original map.  (`symm` swaps the
forward and inverse rational maps.) -/
lemma birationalMap_symm_symm {X Y : Scheme.{0}} [IrreducibleSpace X] [IrreducibleSpace Y]
    (φ : X.BirationalMap Y) : φ.symm.symm = φ := by
  ext; simp [BirationalMap.symm_hom, BirationalMap.symm_inv]

/-- The invariant coefficient changes sign under inversion of the birational map:
`cInv 𝕜 z φ⁻¹ = - cInv 𝕜 z φ` (the exceptional divisors created and contracted are swapped). -/
theorem cInv_eq_neg_symm (𝕜 : Type) [Field 𝕜] {X Y Z : Scheme.{0}} [IrreducibleSpace X]
    [IrreducibleSpace Y] [X.Over (Spec (.of 𝕜))] [Y.Over (Spec (.of 𝕜))]
    [Z.Over (Spec (.of 𝕜))] (z : Z) (φ : X.BirationalMap Y) :
    cInv 𝕜 z φ.symm = -cInv 𝕜 z φ := by
  have h : φ.symm.symm = φ := birationalMap_symm_symm φ
  simp only [cInv, h]
  first | refl_ring1 | ring

end Work.LLink
