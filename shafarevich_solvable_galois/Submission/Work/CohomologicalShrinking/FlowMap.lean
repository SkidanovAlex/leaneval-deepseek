import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.RepresentationTheory.Rep.Basic
import Submission.Work.CohomologicalShrinking.FlowRep

attribute [local instance] Classical.decEq

namespace Work.CohomologicalShrinking

open scoped TensorProduct

universe u

variable {p : ℕ}

/-! ## The rank-change homomorphism on the normal subgroups -/

/-- The rank-change homomorphism on the normal subgroups `F(m)/F(m)^{(ν)} →* F(n)/F(n)^{(ν)}`,
transported along `flowNormalEquiv`. -/
noncomputable def flowNormalSubMap (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) : flowNormal p G m i j →* flowNormal p G n i j :=
  ((flowNormalEquiv (G := G) p n i j).toMonoidHom).comp
    ((flowQuotMap (G := G) p i j Φ).comp
      (flowNormalEquiv (G := G) p m i j).symm.toMonoidHom)

theorem flowNormalSubMap_coe (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (x : flowNormal p G m i j) :
    ((flowNormalSubMap p G i j Φ x : flowNormal p G n i j) : flowGroup p G n i j) =
      flowInl (G := G) p n i j
        (flowQuotMap p G i j Φ ((flowNormalEquiv (G := G) p m i j).symm x)) := rfl

/-! ## Rank change on the coefficient representation -/

theorem flowRepG_ρ_apply (p : ℕ) [NeZero p] (G : Type*) [Group G] (m i j : ℕ)
    (T : Type*) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] (g : G) (x : E p G m i j ⊗[ZMod p] T) :
    (flowRepG p G m i j T).ρ g x = g • x :=
  Representation.ofDistribMulAction_apply_apply g x

/-- The intertwining identity underlying `flowRepMap`, stated for `E(m,τ) ⊗ T`-typed elements. -/
theorem flowRepG_isIntertwining (p : ℕ) [NeZero p] (G : Type*) [Group G] (i j : ℕ) {m n : ℕ}
    (Φ : OperatorMap G m n) (T : Type*) [AddCommGroup T] [Module (ZMod p) T]
    [DistribMulAction G T] [SMulCommClass G (ZMod p) T] (g : G)
    (x : E p G m i j ⊗[ZMod p] T) :
    (gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T ((flowRepG p G m i j T).ρ g x) =
      (flowRepG p G n i j T).ρ g
        ((gradedMapLin p Φ.toHom Φ.surjective i j).rTensor T x) := by
  rw [flowRepG_ρ_apply, flowRepG_ρ_apply]
  exact rTensor_equiv p (G := G) (f := gradedMapLin p Φ.toHom Φ.surjective i j)
    (fun g z => gradedMapLin_smul p Φ.toHom Φ.surjective Φ.equivariant i j g z) g x

end Work.CohomologicalShrinking
