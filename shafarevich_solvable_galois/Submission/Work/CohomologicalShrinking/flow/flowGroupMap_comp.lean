import Mathlib
import Submission.Work.CohomologicalShrinking.FlowGroupMap
import Submission.Work.CohomologicalShrinking.OperatorMap
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.CohomologicalShrinking

/-- The rank-change maps on the quotients `F(m)/F(m)^{(ν)} →* F(n)/F(n)^{(ν)}` are functorial:
composing the operator maps composes the induced quotient maps. -/
private theorem flowQuotMap_comp (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n l : ℕ}
    (Φ : OperatorMap G m n) (Ψ : OperatorMap G n l) :
    flowQuotMap p G i j (OperatorMap.comp Ψ Φ) =
      (flowQuotMap p G i j Ψ).comp (flowQuotMap p G i j Φ) := by
  ext x
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, MonoidHom.comp_apply, flowQuotMap_mk,
    flowQuotMap_mk, flowQuotMap_mk]
  rfl

end Work.CohomologicalShrinking

namespace Work.CohomologicalShrinking.flow

/-- The rank-change homomorphisms `F(m)/F(m)^{(ν)} ⋊ G →* F(n)/F(n)^{(ν)} ⋊ G` induced by
surjective `G`-operator homomorphisms are functorial. -/
theorem flowGroupMap_comp (p : ℕ) (G : Type*) [Group G] (i j : ℕ) {m n l : ℕ}
    (Φ : OperatorMap G m n) (Ψ : OperatorMap G n l) :
    flowGroupMap p G i j (OperatorMap.comp Ψ Φ) =
      (flowGroupMap p G i j Ψ).comp (flowGroupMap p G i j Φ) := by
  apply MonoidHom.ext
  intro x
  rw [← SemidirectProduct.inl_left_mul_inr_right x]
  unfold flowGroupMap
  simp only [map_mul, MonoidHom.comp_apply, SemidirectProduct.map_inl, SemidirectProduct.map_inr,
    MonoidHom.id_apply, flowQuotMap_comp]

end Work.CohomologicalShrinking.flow
