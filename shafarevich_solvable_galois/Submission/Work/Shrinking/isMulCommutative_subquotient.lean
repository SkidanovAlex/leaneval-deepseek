import Mathlib.GroupTheory.Commutator.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

open scoped commutatorElement

namespace Work.Shrinking

/-- A subquotient `H/K` (with `K` normal in the ambient group; `K` need not be contained
in `H`) is commutative as soon as `[H, H] ≤ K`.  This is the "`P_n/P_{n+1}` is abelian" half
of the elementary-abelian-`p` property of the quotients of the descending `p`-central series.

Proof: `rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]` reduces to
`commutator ↥H ≤ K.subgroupOf H`; note `commutator ↥H = ⁅⊤, ⊤⁆` and use
`Subgroup.map_subtype_commutator` (or `Subgroup.commutator_le` with
`Subgroup.commutator_mem_commutator` and `Subgroup.mem_subgroupOf`) together with the
hypothesis `⁅H, H⁆ ≤ K`. -/
theorem isMulCommutative_subquotient {P : Type*} [Group P] {H K : Subgroup P}
    [K.Normal] (h : ⁅H, H⁆ ≤ K) : IsMulCommutative (H ⧸ K.subgroupOf H) := by
  rw [Subgroup.Normal.quotient_commutative_iff_commutator_le]
  rw [_root_.commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [Subgroup.mem_subgroupOf]
  rw [show ((⁅g₁, g₂⁆ : ↥H) : P) = ⁅(g₁ : P), (g₂ : P)⁆ from by
    simp [commutatorElement_def]]
  exact Subgroup.commutator_le.mp h g₁ g₁.2 g₂ g₂.2

end Work.Shrinking
