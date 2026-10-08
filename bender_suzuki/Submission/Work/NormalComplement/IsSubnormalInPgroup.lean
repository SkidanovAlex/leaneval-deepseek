import Mathlib
import Submission.Blueprint.Interfaces

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Subgroups of a `p`-group are subnormal

`Submission.Blueprint.IsSubnormalIn Y X` is the reflexive-transitive closure of the relation
"`Y ≤ X` and `Y` is normal in `X`".  A subgroup of a (finite) `p`-group is subnormal: `p`-groups
are nilpotent, hence satisfy the normalizer condition, and one climbs the normalizer chain.

This is the subnormality input that Ch. II §4 Prop. 3 (subnormal-`Y` form,
`Submission.Blueprint.ChIIFourP3SubnormalProp`) needs in the case-2 step of Ch. III §2 Prop. 1,
where `Y = U₁ ≤ U` with `U` a `p`-group.
-/

namespace Work.NormalComplement

open Submission.Blueprint

variable {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]

/-- A proper subgroup of a `p`-group is properly contained in its normalizer. -/
lemma lt_inf_normalizer_of_isPGroup_v2 {Q U : Subgroup G} (hUQ : U < Q) (hQ : IsPGroup p Q) :
    U < Q ⊓ Subgroup.normalizer (U : Set G) := by
  have hnil : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hNC : NormalizerCondition ↥Q := Group.normalizerCondition_of_isNilpotent
  have hne : U.subgroupOf Q ≠ ⊤ := by
    intro h
    refine hUQ.2 ?_
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥Q) ∈ U.subgroupOf Q := by rw [h]; trivial
    simpa [Subgroup.mem_subgroupOf] using h1
  have hsub : U.subgroupOf Q ≠ Subgroup.normalizer (U.subgroupOf Q) := fun h =>
    hne ((normalizerCondition_iff_only_full_group_self_normalizing.mp hNC
      (U.subgroupOf Q) h.symm))
  have hle : U.subgroupOf Q ≤ Subgroup.normalizer (U.subgroupOf Q) := Subgroup.le_normalizer
  have hlt : U.subgroupOf Q < Subgroup.normalizer (U.subgroupOf Q) := lt_of_le_of_ne hle hsub
  have heq : Subgroup.normalizer (U.subgroupOf Q) = (Subgroup.normalizer (U : Set G)).subgroupOf Q :=
    (Subgroup.subgroupOf_normalizer_eq hUQ.1).symm
  rw [heq] at hlt
  refine lt_of_le_of_ne ?_ ?_
  · intro x hx
    exact ⟨hUQ.1 hx, Subgroup.le_normalizer hx⟩
  · intro h
    refine hlt.2 (le_of_eq ?_)
    rw [← Subgroup.inf_subgroupOf_left, ← h]

/-- **A subgroup of a finite `p`-group is subnormal.**  `Y ≤ X` with `X` a `p`-group satisfies
`IsSubnormalIn Y X`. -/
theorem isSubnormalIn_of_isPGroup {Y X : Subgroup G} (hYX : Y ≤ X) (hX : IsPGroup p X) :
    IsSubnormalIn Y X := by
  suffices h : ∀ m : ℕ, ∀ Y : Subgroup G, Y ≤ X → Nat.card X - Nat.card Y = m →
      IsSubnormalIn Y X by
    exact h _ Y hYX rfl
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro Y hYX hm
    rcases eq_or_lt_of_le hYX with heq | hlt
    · subst heq; exact Relation.ReflTransGen.refl
    · have hYlt : Y < X ⊓ Subgroup.normalizer (Y : Set G) :=
        lt_inf_normalizer_of_isPGroup_v2 hlt hX
      have hY1X : (X ⊓ Subgroup.normalizer (Y : Set G)) ≤ X := inf_le_left
      have hYle : Y ≤ X ⊓ Subgroup.normalizer (Y : Set G) := le_inf hYX Subgroup.le_normalizer
      have hYne1 : Y ≠ X ⊓ Subgroup.normalizer (Y : Set G) := fun h => hYlt.2 (le_of_eq h.symm)
      have hcardlt : Nat.card Y < Nat.card ↥(X ⊓ Subgroup.normalizer (Y : Set G)) := by
        have hdvd : Nat.card Y ∣ Nat.card ↥(X ⊓ Subgroup.normalizer (Y : Set G)) := by
          rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYle).toEquiv]
          exact Subgroup.card_subgroup_dvd_card _
        exact lt_of_le_of_ne (Nat.le_of_dvd Nat.card_pos hdvd) (fun hc =>
          hYne1 (Subgroup.eq_of_le_of_card_ge hYle (le_of_eq hc.symm)))
      have hmeas : Nat.card X - Nat.card ↥(X ⊓ Subgroup.normalizer (Y : Set G)) < m := by
        have hle1X : Nat.card ↥(X ⊓ Subgroup.normalizer (Y : Set G)) ≤ Nat.card X :=
          Nat.le_of_dvd Nat.card_pos (by
            rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hY1X).toEquiv]
            exact Subgroup.card_subgroup_dvd_card _)
        omega
      have ihY1 : IsSubnormalIn (X ⊓ Subgroup.normalizer (Y : Set G)) X :=
        ih _ hmeas _ hY1X rfl
      have hstep : Y ≤ X ⊓ Subgroup.normalizer (Y : Set G) ∧
          (Y.subgroupOf (X ⊓ Subgroup.normalizer (Y : Set G))).Normal :=
        ⟨hYle, Subgroup.normal_subgroupOf_of_le_normalizer inf_le_right⟩
      exact Relation.ReflTransGen.head hstep ihY1

end Work.NormalComplement
