/-
Area A9 (normal `p`-complement theorems), transfer interface.

The classical criterion for a finite group `G` to have a normal `p`-complement is the existence of
a homomorphism `φ : G →* A` into a `p`-group `A` whose restriction to a Sylow `p`-subgroup `P ≤ G`
is injective.  The direction `←` is the "transfer engine"
`Work.NPC.hasNormalPComplement_of_hom_to_pGroup` of `Submission/Work/NPC/Engine.lean`: if `φ` is
such a map then `ker φ` is a normal `p`-complement (`|ker φ| = [G : P]` is coprime to `p` and
`G ⧸ ker φ` embeds in the `p`-group `A`).

The direction `→` is the trivial one: if `N` is a normal `p`-complement then the quotient map
`G →* G ⧸ N` lands in the `p`-group `G ⧸ N` and is injective on `P`, because `P ⊓ N = ⊥`
(`|P ⊓ N|` divides both the `p`-power `|P|` and the `p`-coprime number `|N|`).

The only subtlety is universes: the statement quantifies over `A : Type u₂` for an `arbitrary`
universe level `u₂`, while the quotient `G ⧸ N` a priori lives in the universe of `G`.  Since
`G ⧸ N` is finite, we may replace it by a group in any universe, using `Shrink` together with the
fact (`small_of_finite` below) that a finite type is `Small` at every universe level.
-/
import Mathlib
import Submission.Work.NPC.Defs
import Submission.Work.NPC.Engine

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option linter.style.haveILetI false

namespace Work.NPC.Transfer

/-- Every finite type is small in every universe: it is equivalent to `Fin n` for some `n`, hence
to a type in any universe level. -/
theorem small_of_finite.{w, u} {α : Type u} [Finite α] : Small.{w} α := by
  haveI : Fintype α := Fintype.ofFinite α
  exact Small.mk' ((Fintype.equivFin α).trans Equiv.ulift.symm)

theorem hasNormalPComplement_iff_exists_hom {G : Type*} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (P : Sylow p G) :
    Work.NPC.HasNormalPComplement p G ↔ ∃ (A : Type _) (_ : Group A) (_ : Finite A) (φ : G →* A),
      IsPGroup p A ∧ Function.Injective (φ.domRestrict (P : Subgroup G)) := by
  constructor
  · -- `→` : a normal `p`-complement `N` gives the quotient map `G →* G ⧸ N`, which is injective
    -- on `P`; the finite `p`-group `G ⧸ N` is then moved to the universe of `A` via `Shrink`.
    rintro ⟨N, hN⟩
    haveI hNn : N.Normal := hN.normal
    -- `P ⊓ N = ⊥`, since `|P ⊓ N|` divides both the `p`-power `|P|` and `|N|`, which is
    -- coprime to `p`.
    have hdisj : Disjoint N (P : Subgroup G) := by
      rw [disjoint_iff]
      have hbot : (P : Subgroup G) ⊓ N = ⊥ := by
        have hpg : IsPGroup p ↥((P : Subgroup G) ⊓ N) :=
          IsPGroup.of_injective P.isPGroup' (Subgroup.inclusion inf_le_left)
            (Subgroup.inclusion_injective inf_le_left)
        obtain ⟨k, hk⟩ := hpg.exists_card_eq
        have hdvd : Nat.card ↥((P : Subgroup G) ⊓ N) ∣ Nat.card ↥N :=
          Subgroup.card_dvd_of_le inf_le_right
        have h1 : p ^ k = 1 :=
          ((hN.coprime_card.pow_right k).symm).eq_one_of_dvd (hk ▸ hdvd)
        exact Subgroup.eq_bot_of_card_eq _ (hk.trans h1)
      rw [inf_comm]
      exact hbot
    haveI : Small (G ⧸ N) := small_of_finite
    have hfin : Finite (Shrink (G ⧸ N)) :=
      Finite.of_injective (Shrink.mulEquiv (α := G ⧸ N))
        (Shrink.mulEquiv (α := G ⧸ N)).injective
    refine ⟨Shrink (G ⧸ N), inferInstance, hfin,
      (Shrink.mulEquiv (α := G ⧸ N)).symm.toMonoidHom.comp (QuotientGroup.mk' N), ?_, ?_⟩
    · -- the image is a `p`-group, being isomorphic to the `p`-group `G ⧸ N`
      exact IsPGroup.of_equiv hN.isPGroup_quotient (Shrink.mulEquiv (α := G ⧸ N)).symm
    · -- injectivity on `P`
      have hker : ((QuotientGroup.mk' N).domRestrict (P : Subgroup G)).ker =
          N.subgroupOf (P : Subgroup G) := by
        change ((QuotientGroup.mk' N).comp (P : Subgroup G).subtype).ker = _
        rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
        exact Subgroup.comap_subtype N _
      have hinjq : Function.Injective ((QuotientGroup.mk' N).domRestrict (P : Subgroup G)) := by
        refine (MonoidHom.ker_eq_bot_iff _).mp ?_
        rw [hker, Subgroup.subgroupOf_eq_bot]
        exact hdisj
      intro x y hxy
      apply hinjq
      exact (Shrink.mulEquiv (α := G ⧸ N)).symm.injective hxy
  · -- `←` : the transfer engine of `Submission/Work/NPC/Engine.lean`.
    rintro ⟨A, grpA, finA, φ, hA, hφ⟩
    letI : Group A := grpA
    haveI : Finite A := finA
    exact Work.NPC.hasNormalPComplement_of_hom_to_pGroup P φ hA hφ

end Work.NPC.Transfer
