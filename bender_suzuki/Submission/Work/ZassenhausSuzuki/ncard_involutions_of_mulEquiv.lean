import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ZassenhausSuzuki

/-- The number of involutions of the ambient group `G` lying in a subgroup `Q` equals the
number of involutions of any group `P` isomorphic to `Q`.

The bijection is the composite of the canonical identification `Q ↪ G` with the isomorphism
`e : Q ≃* P`; both directions preserve the order of an element. -/
theorem ncard_involutions_of_mulEquiv {G : Type*} [Group G] [Finite G] {Q : Subgroup G}
    {P : Type*} [Group P] [Finite P] (e : ↥Q ≃* P) :
    ({x : G | x ∈ Q ∧ orderOf x = 2} : Set G).ncard =
      ({y : P | orderOf y = 2} : Set P).ncard := by
  apply Set.ncard_congr (f := fun x hx => e ⟨x, hx.1⟩)
  · intro x hx
    show orderOf (e ⟨x, hx.1⟩) = 2
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe ⟨x, hx.1⟩]
    exact hx.2
  · intro a b ha hb hab
    have h : (⟨a, ha.1⟩ : ↥Q) = ⟨b, hb.1⟩ := e.injective hab
    simpa using congrArg Subtype.val h
  · intro y hy
    refine ⟨e.symm y, ⟨(e.symm y).2, ?_⟩, ?_⟩
    · rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e (e.symm y), MulEquiv.apply_symm_apply]
      exact hy
    · exact e.apply_symm_apply y

end Work.ZassenhausSuzuki
