import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Tactic.Have
import Mathlib.Algebra.Field.ZMod
import Mathlib.Combinatorics.Quiver.ReflQuiver
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Submission.Work.CohomologicalShrinking.FlowGroupMap
import Submission.Work.CohomologicalShrinking.OperatorMap
import Submission.Work.CohomologicalShrinking.functorial.gradedMapLin_comp
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option maxHeartbeats 800000

namespace Work.CohomologicalShrinking.flow

open Work.CohomologicalShrinking CategoryTheory

attribute [local instance] Classical.decEq

/-! ## Composition compatibility of the structure maps -/

/-- Composition compatibility of the rank-change maps on the quotients `F(-)/F(-)^{(ν)}`. -/
theorem flowQuotMap_comp_aux (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n l : ℕ}
    (Φ : OperatorMap G m n) (Ψ : OperatorMap G n l) :
    flowQuotMap p G i j (OperatorMap.comp Ψ Φ) =
      (flowQuotMap p G i j Ψ).comp (flowQuotMap p G i j Φ) := by
  ext x
  simp only [MonoidHom.comp_apply, flowQuotMap_mk]
  congr 1

/-- Composition compatibility of the rank-change maps on the semidirect products
`F(-)/F(-)^{(ν)} ⋊ G`. -/
theorem flowGroupMap_comp_aux (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n l : ℕ}
    (Φ : OperatorMap G m n) (Ψ : OperatorMap G n l) :
    flowGroupMap p G i j (OperatorMap.comp Ψ Φ) =
      (flowGroupMap p G i j Ψ).comp (flowGroupMap p G i j Φ) := by
  ext x
  · simp only [flowGroupMap, SemidirectProduct.map_left, MonoidHom.comp_apply]
    rw [flowQuotMap_comp_aux]
    rfl
  · simp only [flowGroupMap, SemidirectProduct.map_right, MonoidHom.comp_apply,
      MonoidHom.id_apply]

/-- Composition compatibility of the morphisms of coefficient representations
`E(m,τ)⊗T ⟶ E(n,τ)⊗T`: the morphism induced by `Ψ.comp Φ` is the composite of those induced
by `Φ` and by `Ψ`. -/
theorem flowRepMap_comp_aux (p : ℕ) [Fact p.Prime] (G : Type*) [Group G] (i j : ℕ) {m n l : ℕ}
    (Φ : OperatorMap G m n) (Ψ : OperatorMap G n l) (T : Type*) [AddCommGroup T]
    [Module (ZMod p) T] [DistribMulAction G T] [SMulCommClass G (ZMod p) T] :
    CategoryTheory.CategoryStruct.comp (flowRepMap (p := p) G i j Φ T)
        ((Rep.resFunctor (flowGroupMap p G i j Φ)).map (flowRepMap (p := p) G i j Ψ T))
      = flowRepMap (p := p) G i j (OperatorMap.comp Ψ Φ) T := by
  apply Rep.hom_ext
  apply Representation.IntertwiningMap.ext
  rw [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap, Rep.resMap_hom_toLinearMap]
  change (gradedMapLin p Ψ.toHom Ψ.surjective i j).rTensor T ∘ₗ
      (gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T
    = (gradedMapLin p (OperatorMap.comp Ψ Φ).toHom (OperatorMap.comp Ψ Φ).surjective i j).rTensor T
  rw [← LinearMap.rTensor_comp]
  congr 1
  exact (functorial.gradedMapLin_comp p Φ.toHom Φ.surjective Ψ.toHom Ψ.surjective i j).symm

/-! ## The composite coefficient morphism in flattened form -/

/-- The composite `E(m,τ)⊗T ⟶ E(l,τ)⊗T` of the coefficient morphisms induced by `Φ` and `Ψ`,
with its codomain displayed as `Res(flowGroupMap Ψ ∘ flowGroupMap Φ)(E(l,τ)⊗T)`.  This is
`def`-equal to the composite with codomain `Res(flowGroupMap Φ)(Res(flowGroupMap Ψ)(E(l,τ)⊗T))`;
the flattened form is the one expected by `groupHomology.map_congr`. -/
noncomputable abbrev flowRepMapComp (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (i j : ℕ)
    {m n l : ℕ} (Φ : OperatorMap G m n) (Ψ : OperatorMap G n l) (T : Type)
    [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    flowRep p G m i j T ⟶
      Rep.res ((flowGroupMap p G i j Ψ).comp (flowGroupMap p G i j Φ)) (flowRep p G l i j T) :=
  show (flowRep p G m i j T ⟶ Rep.res (flowGroupMap p G i j Φ)
      (Rep.res (flowGroupMap p G i j Ψ) (flowRep p G l i j T))) from
    (flowRepMap (p := p) G i j Φ T ≫
      (Rep.resFunctor (flowGroupMap p G i j Φ)).map (flowRepMap (p := p) G i j Ψ T))

/-! ## Functoriality of `flowZMap` -/

theorem flowZMap_comp (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (i j : ℕ) {m n l : ℕ}
    (Φ : OperatorMap G m n) (Ψ : OperatorMap G n l) (T : Type) [AddCommGroup T]
    [Module (ZMod p) T] [DistribMulAction G T] [SMulCommClass G (ZMod p) T] :
    flowZMap (p := p) G i j (OperatorMap.comp Ψ Φ) T =
      (flowZMap (p := p) G i j Ψ T).comp (flowZMap (p := p) G i j Φ T) := by
  have hgrp := flowGroupMap_comp_aux p G i j Φ Ψ
  -- `groupHomology.map` is functorial: reduce to the level of `ModuleCat` morphisms
  have key : groupHomology.map (flowGroupMap p G i j (OperatorMap.comp Ψ Φ))
        (flowRepMap (p := p) G i j (OperatorMap.comp Ψ Φ) T) 1 =
      groupHomology.map (flowGroupMap p G i j Φ) (flowRepMap (p := p) G i j Φ T) 1 ≫
      groupHomology.map (flowGroupMap p G i j Ψ) (flowRepMap (p := p) G i j Ψ T) 1 := by
    refine (groupHomology.map_congr (A := flowRep p G m i j T) (B := flowRep p G l i j T)
      (φ := flowRepMap (p := p) G i j (OperatorMap.comp Ψ Φ) T)
      hgrp (ψ := flowRepMapComp p G i j Φ Ψ T) ?_ 1).trans ?_
    · -- the two coefficient morphisms have the same underlying `𝔽_p`-linear map
      rw [Rep.hom_comp, Representation.IntertwiningMap.comp_toLinearMap,
        Rep.resMap_hom_toLinearMap]
      change (gradedMapLin p (OperatorMap.comp Ψ Φ).toHom
            (OperatorMap.comp Ψ Φ).surjective i j).rTensor T
        = (gradedMapLin p Ψ.toHom Ψ.surjective i j).rTensor T ∘ₗ
          (gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T
      rw [← LinearMap.rTensor_comp]
      congr 1
      exact functorial.gradedMapLin_comp p Φ.toHom Φ.surjective Ψ.toHom Ψ.surjective i j
    · rw [show flowRepMapComp p G i j Φ Ψ T = (flowRepMap (p := p) G i j Φ T ≫
          (Rep.resFunctor (flowGroupMap p G i j Φ)).map (flowRepMap (p := p) G i j Ψ T)) from rfl]
      exact groupHomology.map_comp (flowGroupMap p G i j Φ) (flowGroupMap p G i j Ψ)
        (flowRepMap (p := p) G i j Φ T) (flowRepMap (p := p) G i j Ψ T) 1
  have key' : (groupHomology.map (flowGroupMap p G i j (OperatorMap.comp Ψ Φ))
        (flowRepMap (p := p) G i j (OperatorMap.comp Ψ Φ) T) 1).hom
      = ((groupHomology.map (flowGroupMap p G i j Ψ) (flowRepMap (p := p) G i j Ψ T) 1).hom).comp
        ((groupHomology.map (flowGroupMap p G i j Φ) (flowRepMap (p := p) G i j Φ T) 1).hom) := by
    rw [key, ModuleCat.hom_comp]
  apply AddMonoidHom.ext
  intro x
  change (groupHomology.map (flowGroupMap p G i j (OperatorMap.comp Ψ Φ))
        (flowRepMap (p := p) G i j (OperatorMap.comp Ψ Φ) T) 1).hom x
    = (groupHomology.map (flowGroupMap p G i j Ψ) (flowRepMap (p := p) G i j Ψ T) 1).hom
        ((groupHomology.map (flowGroupMap p G i j Φ) (flowRepMap (p := p) G i j Φ T) 1).hom x)
  rw [key']
  rfl

end Work.CohomologicalShrinking.flow
