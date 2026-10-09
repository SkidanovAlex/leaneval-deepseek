/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Rank change for the semidirect products `F(m)/F(m)^{(ν)} ⋊ G`

A surjective `G`-operator homomorphism `Φ : F(m) ⇢ F(n)` induces

* a homomorphism `flowGroupMap Φ : F(m)/F(m)^{(ν)} ⋊ G →* F(n)/F(n)^{(ν)} ⋊ G` (`i,j` fixed),
* hence a map `flowZMap Φ : H₁(Γ_m, E(m,τ)⊗T) →+ H₁(Γ_n, E(n,τ)⊗T)` on group homology,

which is the `zMap` of `Work.CohomologicalShrinking.SemidirectShrinkingData`.  (The morphism of
coefficient representations `flowRepMap Φ` and the equivariance facts are in `FlowMap.lean`.)

**Universe restriction.**  Mathlib's group homology requires the coefficient ring, the group and
the module to live in one universe; since `ZMod p : Type`, `flowZMap` is stated for `G : Type` and
`T : Type`.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.FlowMap
import Submission.Work.CohomologicalShrinking.flow.flowQuotMap_smul
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

open scoped TensorProduct

universe u

variable {p : ℕ}

/-- The rank-change homomorphism `F(m)/F(m)^{(ν)} ⋊ G →* F(n)/F(n)^{(ν)} ⋊ G` induced by a
surjective `G`-operator homomorphism `F(m) ⇢ F(n)`. -/
noncomputable def flowGroupMap (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) : flowGroup p G m i j →* flowGroup p G n i j :=
  SemidirectProduct.map (flowQuotMap p G i j Φ) (MonoidHom.id G)
    (fun g => MonoidHom.ext (fun x => flow.flowQuotMap_smul p G i j Φ g x))

theorem flowGroupMap_inl (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (x : flowQuotient p G m i j) :
    flowGroupMap p G i j Φ (flowInl (G := G) p m i j x) =
      flowInl (G := G) p n i j (flowQuotMap p G i j Φ x) :=
  SemidirectProduct.map_inl _ _ _ x

theorem flowQuot_flowGroupMap (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (γ : flowGroup p G m i j) :
    flowQuot p G n i j (flowGroupMap p G i j Φ γ) = flowQuot p G m i j γ :=
  rfl

theorem flowGroupMap_subtype (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (x : flowNormal p G m i j) :
    flowGroupMap p G i j Φ (x : flowGroup p G m i j) =
      (flowNormalSubMap p G i j Φ x : flowGroup p G n i j) := by
  have hx : (x : flowGroup p G m i j) =
      flowInl (G := G) p m i j ((flowNormalEquiv (G := G) p m i j).symm x) := by
    rw [← flowNormalEquiv_apply (G := G) p m i j ((flowNormalEquiv (G := G) p m i j).symm x),
      MulEquiv.apply_symm_apply]
  rw [hx, flowGroupMap_inl, flowNormalSubMap_coe]

/-- The morphism of coefficient representations `E(m,τ)⊗T ⟶ Res(flowGroupMap Φ)(E(n,τ)⊗T)`
induced by a surjective `G`-operator homomorphism `Φ : F(m) ⇢ F(n)`. -/
noncomputable def flowRepMap (p : ℕ) [NeZero p] (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (T : Type*) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction G T] [SMulCommClass G (ZMod p) T] :
    flowRep p G m i j T ⟶ Rep.res (flowGroupMap p G i j Φ) (flowRep p G n i j T) :=
  Rep.ofHom (LinearMap.intertwiningMap_of_isIntertwiningMap
    (ρ := (flowRep p G m i j T).ρ)
    (σ := (Rep.res (flowGroupMap p G i j Φ) (flowRep p G n i j T)).ρ)
    (f := (gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T) (fun γ x => by
      rw [flowRep_ρ_apply, Rep.res_obj_ρ, MonoidHom.comp_apply, flowRep_ρ_apply,
        flowQuot_flowGroupMap]
      exact flowRepG_isIntertwining p G i j Φ T (flowQuot p G m i j γ) x))

/-! ## Rank change on group homology -/

/-- The map induced by a surjective `G`-operator homomorphism `Φ : F(m) ⇢ F(n)` on group
homology with coefficients in `E(-,τ) ⊗ T`. -/
noncomputable def flowZMap (p : ℕ) [Fact p.Prime] (G : Type) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (T : Type) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction G T] [SMulCommClass G (ZMod p) T] :
    groupHomology.H1 (flowRep p G m i j T) →+
      groupHomology.H1 (flowRep p G n i j T) :=
  (groupHomology.map (flowGroupMap p G i j Φ) (flowRepMap (p := p) G i j Φ T) 1).hom

end Work.CohomologicalShrinking
