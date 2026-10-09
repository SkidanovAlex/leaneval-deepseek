/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# The coefficient module `E(m,τ) ⊗ T` as a representation of `F(m)/F(m)^{(ν)} ⋊ G`

Schmidt–Wingberg's Proposition 7 (i) concerns the group cohomology of `Γ = F(m)/F(m)^{(ν)} ⋊ G`
with coefficients in `E(m,τ) ⊗ T`, where `F(m)/F(m)^{(ν)}` acts **trivially** and `G` acts
through the operator action on `E(m,τ) = F(m)^{(ν)}/F(m)^{(ν+1)}` and the given action on `T`.

This file builds that representation (as an object of `Rep (ZMod p) Γ`, the coefficient category
of `Mathlib.RepresentationTheory.Homological.GroupHomology`), together with the fact that
`F(m)/F(m)^{(ν)}` acts trivially on it — the hypothesis of the corestriction–coinflation sequence
`groupHomology.H1CoresCoinfOfTrivial`.

## Main definitions

* `Work.CohomologicalShrinking.flowRep` : `E(m,τ) ⊗ T` as a `ZMod p`-linear representation of
  `Γ = F(m)/F(m)^{(ν)} ⋊ G`;
* `Work.CohomologicalShrinking.flowRep_isTrivial` : the normal subgroup `F(m)/F(m)^{(ν)}` acts
  trivially.
-/

import Mathlib
import Submission.Work.CohomologicalShrinking.Semidirect

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

open scoped TensorProduct

universe u

variable {p : ℕ}

/-! ## The pullback of the `G`-action to `Γ` -/

/-- The action of `Γ = F(m)/F(m)^{(ν)} ⋊ G` on `E(m,τ) ⊗ T`, obtained by pulling back the
`G`-action along the projection `Γ →* G`. -/
noncomputable instance flowDistribMulAction (p : ℕ) [NeZero p] (G : Type*) [Group G] (m i j : ℕ)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    DistribMulAction (flowGroup p G m i j) (E p G m i j ⊗[ZMod p] T) :=
  DistribMulAction.compHom _ (flowQuot p G m i j)

theorem flow_smul_tmul (p : ℕ) [NeZero p] (G : Type*) [Group G] (m i j : ℕ)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] (γ : flowGroup p G m i j) (e : E p G m i j) (t : T) :
    γ • (e ⊗ₜ[ZMod p] t) =
      (flowQuot p G m i j γ • e) ⊗ₜ[ZMod p] (flowQuot p G m i j γ • t) :=
  rfl

/-- The pulled back action is `𝔽_p`-linear. -/
noncomputable instance flowSMulCommClass (p : ℕ) [NeZero p] (G : Type*) [Group G] (m i j : ℕ)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    SMulCommClass (flowGroup p G m i j) (ZMod p) (E p G m i j ⊗[ZMod p] T) where
  smul_comm γ c x := by
    show (flowQuot p G m i j γ) • (c • x) = c • ((flowQuot p G m i j γ) • x)
    exact SMulCommClass.smul_comm (flowQuot p G m i j γ) c x

/-! ## The representation -/

/-- The `G`-representation `E(m,τ) ⊗ T` (the coefficient module of Proposition 7 (i), before
pulling back to `Γ`). -/
noncomputable abbrev flowRepG (p : ℕ) [NeZero p] (G : Type*) [Group G] (m i j : ℕ)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] : Rep (ZMod p) G :=
  Rep.of (X := E p G m i j ⊗[ZMod p] T)
    (Representation.ofDistribMulAction (ZMod p) G (E p G m i j ⊗[ZMod p] T))

/-- **The coefficient module of Proposition 7 (i)**: `E(m,τ) ⊗ T` as a `ZMod p`-linear
representation of `Γ = F(m)/F(m)^{(ν)} ⋊ G`, where `Γ` acts through the projection `Γ →* G`. -/
noncomputable abbrev flowRep (p : ℕ) [NeZero p] (G : Type*) [Group G] (m i j : ℕ)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] : Rep (ZMod p) (flowGroup p G m i j) :=
  Rep.res (flowQuot p G m i j) (flowRepG p G m i j T)

theorem flowRep_V (p : ℕ) [NeZero p] (G : Type*) [Group G] (m i j : ℕ)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    (flowRepG p G m i j T).V = (E p G m i j ⊗[ZMod p] T) := rfl

theorem flowRep_res (p : ℕ) [NeZero p] (G : Type*) [Group G] (m i j : ℕ)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    flowRep p G m i j T = Rep.res (flowQuot p G m i j) (flowRepG p G m i j T) := rfl

/-- The action of `Γ` on `E(m,τ) ⊗ T` only depends on the image of the element in `G`. -/
theorem flowRep_ρ_apply (p : ℕ) [NeZero p] (G : Type*) [Group G] (m i j : ℕ)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] (γ : flowGroup p G m i j) :
    (flowRep p G m i j T).ρ γ = (flowRepG p G m i j T).ρ (flowQuot p G m i j γ) := rfl

/-- The normal subgroup `F(m)/F(m)^{(ν)}` acts trivially on `E(m,τ) ⊗ T`. -/
instance flowRep_isTrivial (p : ℕ) [NeZero p] (G : Type*) [Group G] (m i j : ℕ)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    Representation.IsTrivial
      ((flowRep p G m i j T).ρ.comp (flowNormal p G m i j).subtype) where
  out s := by
    have hs : (s : flowGroup p G m i j) ∈ (flowQuot p G m i j).ker := by
      rw [flowQuot_ker]; exact s.2
    have hs1 : flowQuot p G m i j (s : flowGroup p G m i j) = 1 := MonoidHom.mem_ker.1 hs
    rw [show ((flowRep p G m i j T).ρ.comp (flowNormal p G m i j).subtype) s
        = (flowRepG p G m i j T).ρ (1 : G) from by rw [← hs1]; rfl]
    exact map_one _

end Work.CohomologicalShrinking
