import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Coprime

/-- A proper subgroup `R` of a finite `p`-group `T` is properly contained in its normalizer
inside `T`, i.e. `R < T ⊓ N_G(R)`.

This is the *normalizer condition* for a finite `p`-group: `T` is nilpotent (a finite `p`-group
is nilpotent), and a nilpotent group satisfies `H < N_G(H)` for every proper subgroup `H`.  The
normalizer of `R` inside `T` is `T ⊓ N_G(R)`, which is what identifies the two normalizers. -/
theorem lt_inf_normalizer_of_lt {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {R T : Subgroup G} (hT : IsPGroup p T) (hRT : R < T) :
    R < T ⊓ Subgroup.normalizer (R : Set G) := by
  -- A finite `p`-group is nilpotent, hence satisfies the normalizer condition.
  have hnil : Group.IsNilpotent T := hT.isNilpotent
  have hnc : NormalizerCondition T := @Group.normalizerCondition_of_isNilpotent T _ hnil
  -- `R` viewed inside `T` is a proper subgroup of `T`.
  have htop : R.subgroupOf T < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop'
    rw [Subgroup.subgroupOf_eq_top] at htop'
    exact hRT.ne (le_antisymm hRT.le htop')
  have h1 : R.subgroupOf T < Subgroup.normalizer (R.subgroupOf T) := hnc _ htop
  -- The normalizer of `R` in `T` is `T ⊓ N_G(R)`.
  rw [← Subgroup.subgroupOf_normalizer_eq hRT.le] at h1
  refine lt_of_le_of_ne (le_inf hRT.le Subgroup.le_normalizer) ?_
  intro h
  have h2 : R.subgroupOf T = (Subgroup.normalizer (R : Set G)).subgroupOf T := by
    have h3 := congrArg (fun S : Subgroup G => S.subgroupOf T) h
    simpa using h3
  exact h1.ne h2

end Work.Coprime
