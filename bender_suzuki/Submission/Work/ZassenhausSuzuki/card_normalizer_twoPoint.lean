import Mathlib
import Submission.Work.ZassenhausTwoGroup.normalizer_twoPoint

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `|N_G(D)| = 2 |D|` for the two-point stabiliser of a Zassenhaus split rank-one set-up

In the split rank-one Zassenhaus configuration `IsSplitRankOne H Q t`, `IsZassenhaus H` with
nontrivial two-point stabiliser `D = twoPoint H t = H ⊓ Hᵗ`, the normaliser of `D` is
`D ⊔ ⟨t⟩` (`Work.ZassenhausTwoGroup.normalizer_twoPoint`), and since `t` is an involution
outside `D`, this join has order `2 |D|`:

`Nat.card N_G(D) = 2 * Nat.card D`.

The group-theoretic content is isolated in `card_sup_zpowers`, which is stated for an arbitrary
finite group, subgroup `D` and element `t` with `t * t = 1`, `t ∉ D` and `t` normalising `D`:
then `D ⊔ ⟨t⟩` is `D` together with its `t`-coset, so its index over `D` is `2`.
-/

namespace Work.ZassenhausSuzuki

open Submission.Blueprint

/-- If `t * t = 1` then the cyclic subgroup `⟨t⟩` is the two-element set `{1, t}`: every
element of `Subgroup.zpowers t` is `1` or `t`.  (The set `{1, t}` is a subgroup, so it contains
`⟨t⟩`.) -/
lemma zpowers_eq_one_or_self {G : Type*} [Group G] {t z : G} (h2 : t * t = 1)
    (hz : z ∈ Subgroup.zpowers t) : z = 1 ∨ z = t := by
  let S : Subgroup G :=
    { carrier := {x | x = 1 ∨ x = t}
      mul_mem' := by rintro x y (rfl | rfl) (rfl | rfl) <;> simp [h2]
      one_mem' := Or.inl rfl
      inv_mem' := by rintro x (rfl | rfl) <;> simp [inv_eq_of_mul_eq_one_right h2] }
  have hzS : z ∈ S := (Subgroup.zpowers_le (H := S)).mpr (Or.inr rfl) hz
  exact hzS

/-- If `t` normalises `D` and `t * t = 1`, every element of `D ⊔ ⟨t⟩` lies in `D` or in the
coset `D * t`.  Indeed `D` is normal in `D ⊔ ⟨t⟩` (it is normalised by both `D` and `t`), so an
element of the join is `y * z` with `y ∈ D`, `z ∈ ⟨t⟩`, and `z` is `1` or `t`
(`zpowers_eq_one_or_self`). -/
lemma mem_sup_zpowers {G : Type*} [Group G] (D : Subgroup G) {t : G}
    (ht : t ∈ Subgroup.normalizer (D : Set G)) (h2 : t * t = 1) :
    ∀ x ∈ D ⊔ Subgroup.zpowers t, x ∈ D ∨ x * t ∈ D := by
  have hNle : D ⊔ Subgroup.zpowers t ≤ Subgroup.normalizer (D : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr ht)
  have hnorm : (D.subgroupOf (D ⊔ Subgroup.zpowers t)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hNle
  intro x hx
  have hsup : D.subgroupOf (D ⊔ Subgroup.zpowers t) ⊔
      (Subgroup.zpowers t).subgroupOf (D ⊔ Subgroup.zpowers t) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  have hmem : (⟨x, hx⟩ : ↥(D ⊔ Subgroup.zpowers t)) ∈
      D.subgroupOf (D ⊔ Subgroup.zpowers t) ⊔
        (Subgroup.zpowers t).subgroupOf (D ⊔ Subgroup.zpowers t) := by
    rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨y, hy, z, hz, hyz⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := D.subgroupOf (D ⊔ Subgroup.zpowers t))
      (t := (Subgroup.zpowers t).subgroupOf (D ⊔ Subgroup.zpowers t)) (hs := hnorm)).mp hmem
  have hyD : (y : G) ∈ D := Subgroup.mem_subgroupOf.mp hy
  have hzZ : (z : G) ∈ Subgroup.zpowers t := Subgroup.mem_subgroupOf.mp hz
  have hval : (y : G) * (z : G) = x := congrArg Subtype.val hyz
  rcases zpowers_eq_one_or_self h2 hzZ with hz1 | hzt
  · left
    rw [← hval, hz1, mul_one]; exact hyD
  · right
    rw [← hval, hzt, mul_assoc, h2, mul_one]; exact hyD

/-- **The order of `D ⊔ ⟨t⟩`.**  If `t` is an involution normalising the subgroup `D` of a
finite group and `t ∉ D`, then `D ⊔ ⟨t⟩` has index two over `D` — every element lies in `D` or
in `D * t` (`mem_sup_zpowers`) — hence order `2 |D|`. -/
lemma card_sup_zpowers {G : Type*} [Group G] [Finite G] (D : Subgroup G) {t : G}
    (ht : t ∈ Subgroup.normalizer (D : Set G)) (h2 : t * t = 1) (htD : t ∉ D) :
    Nat.card ↥(D ⊔ Subgroup.zpowers t) = 2 * Nat.card ↥D := by
  have hkey := mem_sup_zpowers D ht h2
  -- `t` witnesses that `D` has index two in `D ⊔ ⟨t⟩`
  have hidx : (D.subgroupOf (D ⊔ Subgroup.zpowers t)).index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨t, Subgroup.mem_sup_right (Subgroup.mem_zpowers t)⟩, ?_, ?_⟩
    · intro hmem
      exact htD (Subgroup.mem_subgroupOf.mp hmem)
    · intro b
      rcases hkey (b : G) b.2 with hb | hb
      · exact Or.inr (Subgroup.mem_subgroupOf.mpr hb)
      · exact Or.inl (Subgroup.mem_subgroupOf.mpr hb)
  have hcard : Nat.card ↥(D.subgroupOf (D ⊔ Subgroup.zpowers t)) = Nat.card ↥D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  calc Nat.card ↥(D ⊔ Subgroup.zpowers t)
      = Nat.card (↥(D ⊔ Subgroup.zpowers t) ⧸ D.subgroupOf (D ⊔ Subgroup.zpowers t)) *
        Nat.card ↥(D.subgroupOf (D ⊔ Subgroup.zpowers t)) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup _
    _ = (D.subgroupOf (D ⊔ Subgroup.zpowers t)).index *
        Nat.card ↥(D.subgroupOf (D ⊔ Subgroup.zpowers t)) := by
        rw [Subgroup.index_eq_card]
    _ = 2 * Nat.card ↥(D.subgroupOf (D ⊔ Subgroup.zpowers t)) := by rw [hidx]
    _ = 2 * Nat.card ↥D := by rw [hcard]

/-- **The normaliser of the two-point stabiliser has twice its order.**  In the split rank-one
Zassenhaus set-up with `D = twoPoint H t ≠ ⊥`, the normaliser of `D` is `D ⊔ ⟨t⟩`
(`Work.ZassenhausTwoGroup.normalizer_twoPoint`), and the outside involution `t` is not in `D`,
so `|N_G(D)| = 2 |D|`. -/
theorem card_normalizer_twoPoint {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (h : Submission.Blueprint.IsSplitRankOne H Q t) (hZ : Submission.Blueprint.IsZassenhaus H)
    (hD : Submission.Blueprint.twoPoint H t ≠ ⊥) :
    Nat.card ↥(Subgroup.normalizer (Submission.Blueprint.twoPoint H t : Set G)) =
      2 * Nat.card ↥(Submission.Blueprint.twoPoint H t) := by
  have hN := Work.ZassenhausTwoGroup.normalizer_twoPoint h hZ hD
  have ht : t ∈ Subgroup.normalizer (Submission.Blueprint.twoPoint H t : Set G) := by
    rw [hN]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers t)
  have h2 : t * t = 1 := by
    rw [← pow_two, ← h.invol]; exact pow_orderOf_eq_one t
  have htD : t ∉ Submission.Blueprint.twoPoint H t := fun hm =>
    h.not_mem (Subgroup.mem_inf.mp hm).1
  rw [hN]
  exact card_sup_zpowers _ ht h2 htD

end Work.ZassenhausSuzuki
