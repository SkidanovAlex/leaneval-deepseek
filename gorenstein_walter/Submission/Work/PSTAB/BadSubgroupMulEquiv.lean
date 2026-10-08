import Mathlib

namespace Work.PSTAB

/-- A multiplicative equivalence transports the property "there is a unique element of order two". -/
lemma MulEquiv.existsUnique_of_orderOf_eq_two {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : ∃! z : G, orderOf z = 2) : ∃! w : H, orderOf w = 2 := by
  obtain ⟨z, hz, huniq⟩ := h
  refine ⟨e z, ?_, ?_⟩
  · change orderOf (e z) = 2
    rw [MulEquiv.orderOf_eq]; exact hz
  · intro w hw
    have h1 : e.symm w = z := by
      apply huniq
      rw [MulEquiv.orderOf_eq]; exact hw
    rw [← h1]; simp

lemma BadSubgroupMulEquiv {L L₀ : Type*} [Group L] [Group L₀] (e : L ≃* L₀) (Q₀ : Subgroup L₀)
    (h2 : IsPGroup 2 Q₀) (hnc : ¬ IsCyclic Q₀) (hu : ∃! z : Q₀, orderOf z = 2) :
    ∃ Q : Subgroup L, IsPGroup 2 Q ∧ ¬ IsCyclic Q ∧ ∃! z : Q, orderOf z = 2 := by
  refine ⟨Q₀.map (e.symm : L₀ →* L), h2.map _, ?_, ?_⟩
  · intro hcyc
    exact hnc ((MulEquiv.isCyclic ((e.symm).subgroupMap Q₀)).mpr hcyc)
  · exact MulEquiv.existsUnique_of_orderOf_eq_two ((e.symm).subgroupMap Q₀) hu

end Work.PSTAB
