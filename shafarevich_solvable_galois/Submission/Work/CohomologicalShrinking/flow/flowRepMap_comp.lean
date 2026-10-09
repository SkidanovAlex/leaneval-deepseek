import Mathlib
import Submission.Work.CohomologicalShrinking.FlowGroupMap
import Submission.Work.CohomologicalShrinking.OperatorMap
import Submission.Work.CohomologicalShrinking.functorial.gradedMapLin_comp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.flow

open scoped TensorProduct

/-- The underlying `𝔽_p`-linear map of the coefficient morphism `flowRepMap Φ` is the
tensor product `gradedMapLin Φ ⊗ id` on `E(m,τ) ⊗ T`. -/
lemma flowRepMap_hom_toLinearMap (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (T : Type*) [AddCommGroup T]
    [Module (ZMod p) T] [DistribMulAction G T] [SMulCommClass G (ZMod p) T] :
    (flowRepMap (p := p) G i j Φ T).hom.toLinearMap =
      (gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T := rfl

theorem flowRepMap_comp (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j : ℕ) {m n l : ℕ}
    (Φ : OperatorMap G m n) (Ψ : OperatorMap G n l) (T : Type*) [AddCommGroup T]
    [Module (ZMod p) T] [DistribMulAction G T] [SMulCommClass G (ZMod p) T] :
    CategoryTheory.CategoryStruct.comp (flowRepMap (p := p) G i j Φ T)
        ((Rep.resFunctor (flowGroupMap p G i j Φ)).map (flowRepMap (p := p) G i j Ψ T))
      = flowRepMap (p := p) G i j (OperatorMap.comp Ψ Φ) T := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.toLinearMap_injective
  dsimp only
  -- Pin the right hand side down as a morphism whose target is *syntactically* the source
  -- objects used on the left (they are equal only up to definitional equality).
  let B' : flowRep p G m i j T ⟶
      Rep.res (flowGroupMap p G i j Φ) (Rep.res (flowGroupMap p G i j Ψ) (flowRep p G l i j T)) :=
    flowRepMap (p := p) G i j (OperatorMap.comp Ψ Φ) T
  change (Rep.Hom.hom (CategoryTheory.CategoryStruct.comp (flowRepMap (p := p) G i j Φ T)
      ((Rep.resFunctor (flowGroupMap p G i j Φ)).map (flowRepMap (p := p) G i j Ψ T)))).toLinearMap
    = (Rep.Hom.hom B').toLinearMap
  have hB'lin : B'.hom.toLinearMap =
      (gradedMapLin p (OperatorMap.comp Ψ Φ).toHom
        (OperatorMap.comp Ψ Φ).surjective i j).rTensor T :=
    flowRepMap_hom_toLinearMap p G i j (OperatorMap.comp Ψ Φ) T
  rw [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, Rep.resMap_hom_toLinearMap,
      flowRepMap_hom_toLinearMap, flowRepMap_hom_toLinearMap, hB'lin]
  rw [show (gradedMapLin p (OperatorMap.comp Ψ Φ).toHom
              (OperatorMap.comp Ψ Φ).surjective i j)
        = ((gradedMapLin p Ψ.toHom Ψ.surjective i j).comp
            (gradedMapLin p Φ.toHom Φ.surjective i j)) from
      Work.CohomologicalShrinking.functorial.gradedMapLin_comp p Φ.toHom Φ.surjective Ψ.toHom Ψ.surjective i j,
      LinearMap.rTensor_comp]

end Work.CohomologicalShrinking.flow
