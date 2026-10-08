import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Two elementary identifications of "subgroup of a subgroup" types (area `ThompsonFrobenius`)

Transport plumbing for the steps of Theorem D.  For subgroups `A`, `N`, `L` of a group `G`:

* `subgroupOfMulEquivInf A L : ↥(A.subgroupOf L) ≃* ↥(A ⊓ L)` — the elements of `A` lying in
  `L`, viewed either inside `↥L` or inside `G`;
* `normalizerSubgroupOfEquiv N L : ↥((N ⊓ L).subgroupOf N) ≃* ↥(N.subgroupOf L)` — the elements of
  `N` lying in `L`, viewed either inside `↥N` or inside `↥L`.

Both are needed to move a `HasNormalPComplement` hypothesis (proved for the ambient normalizer
`N_G(Q)`) to a smaller normalizer `N_L(Q)`.
-/

set_option autoImplicit false

namespace Work.ThompsonFrobenius

/-- `A ∩ L` seen inside the subgroup `↥L` is the same group as `A ⊓ L` seen inside `G`. -/
noncomputable def subgroupOfMulEquivInf {G : Type*} [Group G] (A L : Subgroup G) :
    ↥(A.subgroupOf L) ≃* ↥(A ⊓ L) where
  toFun x := ⟨(x.1 : G), ⟨x.2, x.1.2⟩⟩
  invFun y := ⟨⟨(y.1 : G), y.2.2⟩, y.2.1⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_mul' x y := by ext; rfl

/-- `N ∩ L` seen inside the subgroup `↥N` is the same group as `N ∩ L` seen inside `↥L`. -/
noncomputable def normalizerSubgroupOfEquiv {G : Type*} [Group G] (N L : Subgroup G) :
    ↥((N ⊓ L).subgroupOf N) ≃* ↥(N.subgroupOf L) where
  toFun x := ⟨⟨(x.1 : G), x.2.2⟩, x.2.1⟩
  invFun y := ⟨⟨(y.1 : G), y.2⟩, ⟨y.2, y.1.2⟩⟩
  left_inv x := by ext; rfl
  right_inv y := by ext; rfl
  map_mul' x y := by ext; rfl

end Work.ThompsonFrobenius
