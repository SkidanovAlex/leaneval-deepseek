/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The semidirect product `F(m)/F(m)^{(ν)} ⋊ G`

Schmidt–Wingberg's Proposition 7 (i) is a statement about the cohomology of the group

`F(m)/F(m)^{(ν)} ⋊ G`,     `ν = (i,j)`,

where `F(m)` is the free `G`-operator group of rank `m`.  This file builds that group from the
discrete model `Work.Shrinking.freeOperatorGroup G m = FreeGroup (Fin m × G)` of `F(m)` and the
refined filtration `refinedTerm` of §2.

Careful: the paper's `F(m)^{(ν)}` is the *refined term* `refinedTerm p F i j = (F_i ∩ F^j)F_{i+1}`,
so that `F(m)/F(m)^{(ν)}` is the quotient of `F(m)` by `refinedTerm`; it is **not** the graded
piece `refinedQuotient p F i j = F^{(ν)}/F^{(ν+1)}` (the latter is the paper's `E(m,τ)`, the
coefficient module).  We therefore work with

* `Work.CohomologicalShrinking.flowTerm p G m i j` : the subgroup `F(m)^{(i,j)}`;
* `Work.CohomologicalShrinking.flowQuotient p G m i j` : the quotient `F(m)/F(m)^{(i,j)}`, modelled
  as `⊤ ⧸ (F(m)^{(i,j)}).subgroupOf ⊤` so that the descended operator action of `G` is available
  from `Work.Shrinking.quotActionHom`;
* `Work.CohomologicalShrinking.flowGroup p G m i j` : the semidirect product
  `F(m)/F(m)^{(i,j)} ⋊ G`;
* `Work.CohomologicalShrinking.flowNormal` : the normal subgroup `F(m)/F(m)^{(i,j)} ◁ Γ`, with its
  identification `flowNormalEquiv` with `flowQuotient`;
* `Work.CohomologicalShrinking.flowQuotEquiv` : `Γ ⧸ F(m)/F(m)^{(i,j)} ≃* G`;
* `Work.CohomologicalShrinking.flowQuotMap` : the map `F(m)/F(m)^{(ν)} →* F(n)/F(n)^{(ν)}`
  induced by a surjective `G`-operator homomorphism `F(m) ⇢ F(n)`; its `G`-equivariance
  (`Work.CohomologicalShrinking.flowQuotMap_smul`) is proved in
  `Submission.Work.CohomologicalShrinking.flow.flowQuotMap_smul`, and it is used in
  `FlowMap.lean` to build the rank-change homomorphism `flowGroupMap`.

The map on the *graded pieces* `E(m,τ) → E(n,τ)` (Schmidt–Wingberg's `ψ_*`) is
`Work.CohomologicalShrinking.flowNormalMap` = `gradedMapMul` of `Functorial.lean`.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Functorial
import Submission.Work.CohomologicalShrinking.Shrinking
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

universe u

variable {p : ℕ}

/-! ## The quotient `F(m)/F(m)^{(i,j)}` and its `G`-action -/

/-- Schmidt–Wingberg's `F(m)^{(i,j)} = (F(m)_i ∩ F(m)^j)F(m)_{i+1}`, the refined term of the
`p`-central filtration of the free `G`-operator group `F(m) = FreeGroup (Fin m × G)`. -/
noncomputable abbrev flowTerm (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Subgroup (Work.Shrinking.freeOperatorGroup G m) :=
  refinedTerm p (Work.Shrinking.freeOperatorGroup G m) i j

/-- The quotient `F(m)/F(m)^{(i,j)}`, modelled as the quotient of `⊤ ≤ F(m)` (which is
`F(m)` itself) so that the descended action of `G` is `Work.Shrinking.quotActionHom`. -/
noncomputable abbrev flowQuotient (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) : Type _ :=
  (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)) ⧸ (flowTerm p G m i j).subgroupOf ⊤

/-- The operator action of `G` on `F(m)/F(m)^{(i,j)}`. -/
noncomputable def flowAction (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    G →* MulAut (flowQuotient p G m i j) :=
  Work.Shrinking.quotActionHom (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))
    (flowTerm p G m i j)
    (fun g => Subgroup.map_top_of_surjective _ (MulDistribMulAction.toMulAut G _ g).surjective)
    (fun g => map_refinedTerm_eq p (MulDistribMulAction.toMulAut G _ g) i j)

/-- The descended `G`-action on `F(m)/F(m)^{(i,j)}` by group automorphisms. -/
noncomputable instance instFlowMulDistribMulAction (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    MulDistribMulAction G (flowQuotient p G m i j) where
  smul g x := flowAction p G m i j g x
  one_smul x := by
    show flowAction p G m i j 1 x = x
    rw [map_one]; rfl
  mul_smul g h x := by
    show flowAction p G m i j (g * h) x
      = flowAction p G m i j g (flowAction p G m i j h x)
    rw [map_mul]; rfl
  smul_mul g x y := map_mul (flowAction p G m i j g) x y
  smul_one g := map_one (flowAction p G m i j g)

/-- **The semidirect product `F(m)/F(m)^{(i,j)} ⋊ G`** of Schmidt–Wingberg's Proposition 7 (i). -/
noncomputable abbrev flowGroup (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) : Type _ :=
  SemidirectProduct (flowQuotient p G m i j) G (flowAction p G m i j)

/-- The normal subgroup `F(m)/F(m)^{(i,j)} ◁ F(m)/F(m)^{(i,j)} ⋊ G` (the left factor). -/
noncomputable abbrev flowNormal (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Subgroup (flowGroup p G m i j) :=
  (SemidirectProduct.inl : flowQuotient p G m i j →* flowGroup p G m i j).range

instance (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) : (flowNormal p G m i j).Normal := by
  rw [flowNormal, SemidirectProduct.range_inl_eq_ker_rightHom]
  infer_instance

/-- The inclusion of the normal subgroup `F(m)/F(m)^{(i,j)}` into the semidirect product. -/
noncomputable def flowInl (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowQuotient p G m i j →* flowGroup p G m i j :=
  SemidirectProduct.inl

theorem flowInl_range (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    (flowInl (G := G) p m i j).range = flowNormal p G m i j := rfl

theorem flowInl_injective (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Injective (flowInl (G := G) p m i j) :=
  SemidirectProduct.inl_injective

/-- The projection `F(m)/F(m)^{(i,j)} ⋊ G →* G`. -/
noncomputable def flowQuot (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowGroup p G m i j →* G :=
  SemidirectProduct.rightHom

theorem flowQuot_ker (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    (flowQuot (G := G) p m i j).ker = flowNormal p G m i j := by
  rw [flowQuot, flowNormal, SemidirectProduct.range_inl_eq_ker_rightHom]

theorem flowQuot_inl (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (n : flowQuotient p G m i j) :
    flowQuot (G := G) p m i j (flowInl (G := G) p m i j n) = 1 :=
  SemidirectProduct.rightHom_inl n

theorem flowQuot_surjective (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    Function.Surjective (flowQuot (G := G) p m i j) :=
  SemidirectProduct.rightHom_surjective

/-- The identification `F(m)/F(m)^{(i,j)} ⋊ G ⧸ F(m)/F(m)^{(i,j)} ≃* G`. -/
noncomputable def flowQuotEquiv (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowGroup p G m i j ⧸ flowNormal p G m i j ≃* G :=
  (QuotientGroup.quotientMulEquivOfEq (flowQuot_ker p G m i j).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (flowQuot_surjective p G m i j))

/-- The identification of the normal subgroup `F(m)/F(m)^{(i,j)}` with the abstract quotient
`flowQuotient p G m i j`. -/
noncomputable def flowNormalEquiv (p : ℕ) (G : Type*) [Group G] (m i j : ℕ) :
    flowQuotient p G m i j ≃* flowNormal p G m i j :=
  MulEquiv.ofBijective
    ({ toFun := fun n => ⟨flowInl (G := G) p m i j n, ⟨n, rfl⟩⟩
       map_one' := Subtype.ext (map_one _)
       map_mul' := fun a b => Subtype.ext (map_mul _ a b) } :
      flowQuotient p G m i j →* flowNormal p G m i j)
    ⟨fun a b h => flowInl_injective p G m i j (congrArg Subtype.val h),
     fun y => ⟨Classical.choose y.2, Subtype.ext (Classical.choose_spec y.2)⟩⟩

@[simp] theorem flowNormalEquiv_apply (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (n : flowQuotient p G m i j) :
    ((flowNormalEquiv (G := G) p m i j n : flowNormal p G m i j) : flowGroup p G m i j) =
      flowInl (G := G) p m i j n := rfl

/-! ## The graded map `E(m,τ) → E(n,τ)` -/

/-- The homomorphism of the graded pieces `E(m,τ) → E(n,τ)` induced by a surjective `G`-operator
homomorphism `F(m) ⇢ F(n)` (Schmidt–Wingberg's `ψ_*`; this is `gradedMapMul` of
`Functorial.lean`). -/
noncomputable def flowNormalMap (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) :
    refinedQuotient p (Work.Shrinking.freeOperatorGroup G m) i j →*
      refinedQuotient p (Work.Shrinking.freeOperatorGroup G n) i j :=
  gradedMapMul p Φ.toHom Φ.surjective i j

@[simp] theorem flowNormalMap_of (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n)
    (x : refinedTerm p (Work.Shrinking.freeOperatorGroup G m) i j) :
    flowNormalMap p G i j Φ (QuotientGroup.mk'
      ((refinedTerm p (Work.Shrinking.freeOperatorGroup G m) (tauSucc i j).1
        (tauSucc i j).2).subgroupOf
        (refinedTerm p (Work.Shrinking.freeOperatorGroup G m) i j)) x) =
      QuotientGroup.mk' _ (refinedMap p Φ.toHom Φ.surjective i j x) :=
  gradedMapMul_of p Φ.toHom Φ.surjective i j x

/-! ## The rank-change map `F(m)/F(m)^{(ν)} →* F(n)/F(n)^{(ν)}` -/

/-- The homomorphism `F(m)/F(m)^{(ν)} →* F(n)/F(n)^{(ν)}` induced by a surjective `G`-operator
homomorphism `F(m) ⇢ F(n)`. -/
noncomputable def flowQuotMap (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) : flowQuotient p G m i j →* flowQuotient p G n i j :=
  QuotientGroup.map _ _
    ((Φ.toHom.comp (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m)).subtype).codRestrict ⊤
      (fun _ => Subgroup.mem_top _))
    (by
      intro x hx
      change Φ.toHom (x : Work.Shrinking.freeOperatorGroup G m) ∈ flowTerm p G n i j
      rw [Subgroup.mem_subgroupOf] at hx
      exact map_refinedTerm_le_of_surjective p Φ.toHom Φ.surjective i j
        (Subgroup.mem_map_of_mem Φ.toHom hx))

theorem flowQuotMap_mk (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (x : (⊤ : Subgroup (Work.Shrinking.freeOperatorGroup G m))) :
    flowQuotMap p G i j Φ (QuotientGroup.mk' _ x) =
      QuotientGroup.mk' _ ⟨Φ.toHom x, Subgroup.mem_top _⟩ :=
  QuotientGroup.map_mk' _ _ _ _ x

end Work.CohomologicalShrinking
