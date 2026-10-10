import Mathlib.GroupTheory.SemidirectProduct
import Mathlib.Algebra.Field.ZMod
import Mathlib.RepresentationTheory.Homological.GroupHomology.Functoriality
import Submission.Work.CohomologicalShrinking.FlowRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking.hochschildSerre

open Work.CohomologicalShrinking

/-- The identification `Γ ⧸ N ≃* G` of the semidirect product with its `G`-quotient sends the
class of `γ` to `flowQuot γ`. -/
theorem flowQuotEquiv_mk (p : ℕ) (G : Type*) [Group G] (m i j : ℕ)
    (γ : flowGroup p G m i j) :
    flowQuotEquiv p G m i j (QuotientGroup.mk (s := flowNormal p G m i j) γ) =
      flowQuot p G m i j γ := by
  rw [flowQuotEquiv, MulEquiv.trans_apply, QuotientGroup.quotientMulEquivOfEq_mk]
  change (QuotientGroup.kerLift (flowQuot p G m i j)) (QuotientGroup.mk γ) = flowQuot p G m i j γ
  rw [QuotientGroup.kerLift_mk]

/-- **The Hochschild–Serre vanishing of the normal factor.**  The representation `E(m,τ) ⊗ T`
pulled back to `Γ = F(m)/F(m)^{(ν)} ⋊ G` from the `G`-action is trivial on the normal subgroup
`N = F(m)/F(m)^{(ν)}`; hence `H₁` of the representation induced on `Γ ⧸ N` agrees with `H₁` of
the `G`-representation `E(m,τ) ⊗ T` along the identification `Γ ⧸ N ≃* G`. -/
theorem flowQuotH1Equiv (p : ℕ) [Fact p.Prime] (G : Type) [Group G] [Fintype G] (m i j : ℕ)
    (T : Type) [AddCommGroup T] [Module (ZMod p) T] [DistribMulAction G T]
    [SMulCommClass G (ZMod p) T] :
    Nonempty (groupHomology.H1 (Rep.ofQuotient (flowRep p G m i j T) (flowNormal p G m i j)) ≃+
      groupHomology.H1 (flowRepG p G m i j T)) := by
  classical
  refine ⟨(CategoryTheory.Iso.toLinearEquiv (groupHomology.mapIso
    (A := Rep.ofQuotient (flowRep p G m i j T) (flowNormal p G m i j))
    (B := flowRepG p G m i j T)
    (flowQuotEquiv p G m i j)
    (LinearEquiv.refl (ZMod p) ((Rep.ofQuotient (flowRep p G m i j T)
      (flowNormal p G m i j)).V))
    ?_ 1)).toAddEquiv⟩
  intro q
  induction q using QuotientGroup.induction_on with
  | H γ =>
    rw [flowQuotEquiv_mk, LinearEquiv.refl_toLinearMap, LinearMap.id_comp, LinearMap.comp_id]
    rw [← QuotientGroup.mk'_apply (flowNormal p G m i j)]
    rfl

end Work.CohomologicalShrinking.hochschildSerre
