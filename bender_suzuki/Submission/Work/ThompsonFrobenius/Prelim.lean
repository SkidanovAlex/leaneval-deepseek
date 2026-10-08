import Mathlib
import Submission.Work.NPC.All
import Submission.Work.HallHigman.Basic
import Submission.Work.ThompsonFrobenius.BlueprintZJ

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Small helpers for the minimal-counterexample steps of Theorem D (area `ThompsonFrobenius`)

* `isPGroup_of_le`: a subgroup of a `p`-group is a `p`-group;
* `isPiNat_card_of_isPGroup`: the order of a `p`-subgroup is a `p`-power, so a `{p}`-number;
* `exists_map_conj_le_sylow`: every `p`-subgroup conjugates into any given Sylow `p`-subgroup;
* `hasNormalPComplement_normalizer_map_conj_iff`: `HasNormalPComplement` of the normalizer is
  invariant under conjugating the subgroup;
* `card_le_card_sylow_of_isPGroup`: a `p`-subgroup has order at most that of any Sylow.
-/

set_option autoImplicit false

open scoped Pointwise

namespace Work.ThompsonFrobenius

/-- A subgroup of a `p`-group is a `p`-group. -/
theorem isPGroup_of_le {p : ℕ} {G : Type*} [Group G] {A B : Subgroup G}
    (hB : IsPGroup p B) (hAB : A ≤ B) : IsPGroup p A :=
  IsPGroup.of_equiv (hB.to_subgroup (A.subgroupOf B))
    (Subgroup.subgroupOfEquivOfLe hAB)

/-- The order of a finite `p`-subgroup is a power of `p`, hence a `{p}`-number. -/
theorem isPiNat_card_of_isPGroup {p : ℕ} [Fact p.Prime] {G : Type*} [Group G] [Finite G]
    {H : Subgroup G} (hH : IsPGroup p H) :
    Work.HallHigman.IsPiNat (· = p) (Nat.card ↥H) := by
  obtain ⟨n, hn⟩ := hH.exists_card_eq
  intro q hq hqd
  rw [hn] at hqd
  exact (Nat.prime_dvd_prime_iff_eq hq (Fact.out : p.Prime)).mp (hq.dvd_of_dvd_pow hqd)

/-- Every `p`-subgroup of a finite group conjugates into any given Sylow `p`-subgroup
(Sylow's second theorem). -/
theorem exists_map_conj_le_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {R : Subgroup G} (hR : IsPGroup p R) (P : Sylow p G) :
    ∃ g : G, R.map (MulAut.conj g).toMonoidHom ≤ (P : Subgroup G) := by
  obtain ⟨S, hRS⟩ := hR.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  refine ⟨g, ?_⟩
  refine (Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hRS).trans ?_
  rw [← hg]
  exact le_of_eq (by
    rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
    rfl)

/-- `HasNormalPComplement` of the normalizer of a subgroup is invariant under conjugation of the
subgroup: `N_G(H^g) = (N_G(H))^g`. -/
theorem hasNormalPComplement_normalizer_map_conj_iff {G : Type*} [Group G] [Finite G] {p : ℕ}
    (g : G) {H : Subgroup G} :
    Work.NPC.HasNormalPComplement p
        ↥(Subgroup.normalizer ((H.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G)) ↔
      Work.NPC.HasNormalPComplement p ↥(Subgroup.normalizer (H : Set G)) := by
  rw [← Subgroup.map_equiv_normalizer_eq H (MulAut.conj g)]
  have e := Subgroup.equivMapOfInjective (Subgroup.normalizer (H : Set G))
    ((MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  exact ⟨fun h => Work.NPC.Basic.hasNormalPComplement_congr e.symm h,
    fun h => Work.NPC.Basic.hasNormalPComplement_congr e h⟩

/-- A `p`-subgroup has order at most that of any Sylow `p`-subgroup. -/
theorem card_le_card_sylow_of_isPGroup {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {H : Subgroup G} (hH : IsPGroup p H) (R : Sylow p G) : Nat.card ↥H ≤ Nat.card ↥R := by
  obtain ⟨S, hHS⟩ := hH.exists_le_sylow
  have h2 : Nat.card ↥S = Nat.card ↥R :=
    (Sylow.card_eq_multiplicity S).trans (Sylow.card_eq_multiplicity R).symm
  have h1 : Nat.card ↥H ≤ Nat.card ↥S :=
    Nat.le_of_dvd Nat.card_pos (Subgroup.card_dvd_of_le hHS)
  omega

end Work.ThompsonFrobenius
