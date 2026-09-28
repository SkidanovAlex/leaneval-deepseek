import Mathlib
import Submission.Work.SSS.baseRowDefs
import Submission.Work.SSS.LESFacts
import Submission.Work.SSS.E2Aux.homologyZeroIsoCokernel

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `E²_{0,0}` as `E¹_{0,0} / ker(E¹_{0,0} → H_0(F_1))`

For the first page of the spectral sequence of a saturated filtration `ξ`, the `(0,0)` term of the
second page is the quotient of `E¹_{0,0} = H_0(F_0)` by the image of the first differential
`d¹ : E¹_{1,0} → E¹_{0,0}`.  For `s = 0` the map `jF : H_0(F_0) → E¹_{0,0}` is the identity, so
`d¹ = kF` is the connecting map of `0 → F_0 → F_1 → F_1/F_0 → 0`, and exactness of the associated
long exact sequence (`Work.SSS.range_kF_eq_ker_incF`) identifies its image with
`ker(H_0(F_0) → H_0(F_1))`.  This is the form in which the `(0,0)` term is consumed by the
bottom-row argument.
-/

set_option autoImplicit false

namespace Work.SSS.Lem

open CategoryTheory CategoryTheory.Limits

-- ℤ-modules carry two definitionally distinct `Module ℤ` structures (the structural one, and the
-- canonical one coming from the additive group structure); disable the canonical one so that the
-- layout of subtypes and quotients agrees with the structural instance.
attribute [-instance] AddCommGroup.toIntModule

theorem E2_zero_zero_quot {C : ChainComplex (ModuleCat ℤ) ℕ} (ξ : Work.SSS.Filtration C) :
    Nonempty (↥(Work.SSS.E2 ξ 0 0) ≃ₗ[ℤ]
      (↥(Work.SSS.E1 ξ 0 0) ⧸
        (LinearMap.ker (HomologicalComplex.homologyMap (Work.SSS.incF ξ.F 0) 0).hom))) := by
  -- In the `E¹` row complex the differential landing in degree `0` is `d¹ : E¹_{1,0} → E¹_{0,0}`.
  have hd : (Work.SSS.E1Complex ξ 0).d 1 0 = Work.SSS.d1 ξ 0 0 := by
    dsimp only [Work.SSS.E1Complex]
    exact ChainComplex.of_d (fun s => Work.SSS.E1 ξ s 0) (fun s => Work.SSS.d1 ξ s 0) 0
  -- For `s = 0` the map `jF` is the identity, hence `d¹ = kF`.
  have hd1 : Work.SSS.d1 ξ 0 0 = Work.SSS.kF ξ 0 0 := by
    rw [Work.SSS.d1]
    simp only [Work.SSS.jF]
    exact Category.comp_id _
  -- Exactness of `H_1(F_1/F_0) → H_0(F_0) → H_0(F_1)` gives `im kF = ker (incF_*)`.
  have heq : LinearMap.range ((Work.SSS.E1Complex ξ 0).d 1 0).hom
      = LinearMap.ker (HomologicalComplex.homologyMap (Work.SSS.incF ξ.F 0) 0).hom := by
    rw [hd, hd1]
    exact Work.SSS.range_kF_eq_ker_incF ξ 0 0
  -- `E²_{0,0} = H_0(E¹_{*,0}) ≅ cokernel (d¹ : E¹_{1,0} → E¹_{0,0})`.
  obtain ⟨e1⟩ := Work.SSS.E2Aux.homologyZeroIsoCokernel (Work.SSS.E1Complex ξ 0)
  -- `cokernel (d¹) ≅ E¹_{0,0} ⧸ im d¹ = E¹_{0,0} ⧸ ker (incF_*)`.
  refine ⟨e1.toLinearEquiv.trans
    ((ModuleCat.cokernelIsoRangeQuotient ((Work.SSS.E1Complex ξ 0).d 1 0)).toLinearEquiv.trans
      (Submodule.quotEquivOfEq _ _ heq))⟩

end Work.SSS.Lem
