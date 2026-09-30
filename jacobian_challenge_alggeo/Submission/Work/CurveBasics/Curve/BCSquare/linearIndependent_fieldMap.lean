import Mathlib
import Submission.Work.CurveBasics.BCSquare
import Submission.Work.CurveBasics.BaseChange.mem_range_germ_iff
import Submission.Work.CurveBasics.SeparatingElement.linearIndependent_pow_of_isDomain_tensor
import Submission.Work.CurveBasics.Curve.BCSquare.fieldMapTensor
import Submission.Work.CurveBasics.Curve.BCSquare.tensorLift_injective

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option autoImplicit false

open scoped TensorProduct

namespace Work.CurveBasics.Curve.BCSquare

open Work.CurveBasics CategoryTheory Limits AlgebraicGeometry in
universe u in
theorem linearIndependent_fieldMap {k : Type u} [Field k] {F : Type u} [Field F] [Algebra k F]
    {C : Curve k} {C' : Curve F} (S : Curve.BCSquare C C') {ι : Type u}
    {v : ι → C.functionField} (hv : LinearIndependent k v) :
    LinearIndependent F (fun i => S.fieldMap.hom (v i)) := by
  classical
  -- Base change of linear independence: `v i ⊗ 1` is `F`-linearly independent in `F ⊗[k] K(C)`.
  have hw : LinearIndependent F (fun i => (1 : F) ⊗ₜ[k] v i) :=
    SeparatingElement.linearIndependent_tmul_one hv
  rw [linearIndependent_iff] at hw ⊢
  intro l hl
  -- Rewrite the given `F`-linear relation as a `Finset` sum.
  have hl' : ∑ i ∈ l.support, l i • S.fieldMap.hom (v i) = 0 := by
    rw [Finsupp.linearCombination_apply, Finsupp.sum] at hl
    exact hl
  -- Push the relation through the injective map `F ⊗[k] K(C) ⟶ K(C')`.
  apply hw l
  rw [Finsupp.linearCombination_apply, Finsupp.sum]
  refine tensorLift_injective S ?_
  rw [map_zero, map_sum]
  rw [Finset.sum_congr rfl (fun i _ => ?_)]
  · exact hl'
  · rw [tensorLift_smul, tensorLift_one_tmul]

end Work.CurveBasics.Curve.BCSquare
