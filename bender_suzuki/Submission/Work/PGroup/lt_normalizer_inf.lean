import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PGroup

/-- **Normalizer condition for finite `p`-groups.**  If `P` is a finite `p`-group and `R < P`,
then `R` is properly contained in its normalizer in `P`.

Mathlib route: `↥P` is a finite nilpotent group (`IsPGroup.isNilpotent`, using `Fact.mk hp`), hence
satisfies `NormalizerCondition` (`normalizerCondition_of_isNilpotent`); apply it to the subgroup of
`↥P` corresponding to `R` and translate `N_{↥P}(R) = P ⊓ N_G(R)` back to `G`. -/
theorem lt_normalizer_inf {G : Type*} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {P R : Subgroup G} (hP : IsPGroup p P) (hR : R < P) :
    R < P ⊓ Subgroup.normalizer (R : Set G) := by
  -- Regard `p` as a prime in the typeclass sense, for the hypotheses of Mathlib's lemmas.
  haveI : Fact p.Prime := ⟨hp⟩
  -- `P`, being a finite `p`-group, is nilpotent, hence satisfies the normalizer condition.
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  have hnc : NormalizerCondition P := @Group.normalizerCondition_of_isNilpotent P _ hnil
  -- `R` viewed as a subgroup of `P` is proper.
  have htop : R.subgroupOf P < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop'
    rw [Subgroup.subgroupOf_eq_top] at htop'
    exact hR.ne (le_antisymm hR.le htop')
  -- Normalizer condition applied to `R.subgroupOf P` inside `P`.
  have h1 : R.subgroupOf P < Subgroup.normalizer (R.subgroupOf P) := hnc _ htop
  -- Identify the normalizer of `R` inside `P` with `P ⊓ N_G(R)`, restricted to `P`.
  rw [← Subgroup.subgroupOf_normalizer_eq hR.le] at h1
  -- `R ≤ P ⊓ N_G(R)`; it remains to see the inclusion is strict.
  refine lt_of_le_of_ne (le_inf hR.le Subgroup.le_normalizer) ?_
  intro h
  have h2 : R.subgroupOf P = (Subgroup.normalizer (R : Set G)).subgroupOf P := by
    have h3 := congrArg (fun S : Subgroup G => S.subgroupOf P) h
    simpa using h3
  exact h1.ne h2

end Work.PGroup
