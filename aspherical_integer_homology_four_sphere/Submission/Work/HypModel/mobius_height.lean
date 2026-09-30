import Mathlib
import Submission.Work.HypModel.Basic
import Submission.Work.HypModel.uhsOfHyp_hypOfUHS

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.HypModel

open scoped Matrix

/-- If a Lorentz matrix `A` (`Aᵀ J A = J`) fixes the null vector `∞ = (0,0,0,1,1)`, then it
preserves the linear form `x ↦ lorentz x infty = x₃ - x₄`.

Indeed `Aᵀ J A = J` together with `A *ᵥ infty = infty` gives
`Aᵀ *ᵥ (J *ᵥ infty) = J *ᵥ infty`, and then
`lorentz (A x) infty = (A x) ⬝ᵥ (J *ᵥ infty) = x ⬝ᵥ (Aᵀ *ᵥ (J *ᵥ infty)) = x ⬝ᵥ (J *ᵥ infty)
= lorentz x infty`. -/
theorem lorentz_mulVec_infty {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A)
    (hN : A *ᵥ infty = infty) (x : V5) :
    lorentz (A *ᵥ x) infty = lorentz x infty := by
  have hJ : Aᵀ *ᵥ (J *ᵥ infty) = J *ᵥ infty := by
    have h := congrArg (fun M : Matrix (Fin 5) (Fin 5) ℝ => M *ᵥ infty) hA.1
    rw [← Matrix.mulVec_mulVec, hN, ← Matrix.mulVec_mulVec] at h
    exact h
  rw [lorentz_eq_dotProduct, lorentz_eq_dotProduct, dotProduct_mulVec_transpose, hJ]

/-- **A Lorentz transformation fixing `∞` preserves the height of the upper half space model.**

For `P = hypOfUHS q` (with `q 3 > 0`), the identity `lorentz_mulVec_infty` says that
`(A P)₃ - (A P)₄ = P₃ - P₄`, i.e. `(A P)₄ - (A P)₃ = P₄ - P₃ = (q 3)⁻¹`.  Since
`(mobius A q) 3 = ((A P)₄ - (A P)₃)⁻¹`, the height is `q 3`. -/
theorem mobius_height {A : Matrix (Fin 5) (Fin 5) ℝ} (hA : IsLorentzMat A)
    (hN : A.mulVec infty = infty) {q : E4} (hq : 0 < q 3) : (mobius A q) 3 = q 3 := by
  have hq3 : q 3 ≠ 0 := ne_of_gt hq
  have hP : hypOfUHS q 4 - hypOfUHS q 3 = (q 3)⁻¹ := hypOfUHS_four_sub_three hq3
  have hkey : (A *ᵥ hypOfUHS q) 4 - (A *ᵥ hypOfUHS q) 3 = hypOfUHS q 4 - hypOfUHS q 3 := by
    have h := lorentz_mulVec_infty hA hN (hypOfUHS q)
    rw [lorentz_left_infty, lorentz_left_infty] at h
    linarith
  rw [mobius, uhsOfHyp_apply_three, hkey, hP, inv_inv]

end Work.HypModel
