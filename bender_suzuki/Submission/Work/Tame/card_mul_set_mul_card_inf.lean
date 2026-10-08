import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.Tame

open scoped Pointwise

/-- For subgroups `H`, `K` of a finite group `G`, the set product `H * K` satisfies
`|H * K| * |H ⊓ K| = |H| * |K|`.

Proof: quotient the group by the left cosets of `K`.  The image of `H` in `G ⧸ K`
(still meaningful for a non-normal `K`, since only the set of left cosets is used)
has cardinality `|H| / |H ⊓ K|`: it is the orbit of the coset of `1` under the left
action of `H`, and the stabilizer of that coset is exactly `H ⊓ K`, so the
orbit-stabilizer theorem applies.  Combined with the identity
`|H * K| = |K| * |image of H|` (Mathlib's `Subgroup.card_mul_eq_card_subgroup_mul_card_quotient`,
whose proof is the translation action of `K` on the cosets), the claim follows. -/
theorem card_mul_set_mul_card_inf {G : Type*} [Group G] [Fintype G] (H K : Subgroup G) :
    Nat.card ((H : Set G) * (K : Set G)) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  -- The image of `H` in `G ⧸ K` is the orbit of the coset of `1` under the left action of `H`.
  have horbit : MulAction.orbit ↥H (((1 : G) : G ⧸ K)) =
      (QuotientGroup.mk '' (H : Set G) : Set (G ⧸ K)) := by
    ext y
    rw [MulAction.mem_orbit_iff]
    constructor
    · rintro ⟨h, rfl⟩
      refine ⟨(h : G), h.2, ?_⟩
      rw [show h • (((1 : G) : G ⧸ K)) = (((h : G) : G ⧸ K)) from by
        rw [show h • (((1 : G) : G ⧸ K)) = QuotientGroup.mk ((h : G) * 1) from rfl, mul_one]]
    · rintro ⟨g, hg, rfl⟩
      refine ⟨⟨g, hg⟩, ?_⟩
      rw [show (⟨g, hg⟩ : ↥H) • (((1 : G) : G ⧸ K)) = (((g : G) : G ⧸ K)) from by
        rw [show (⟨g, hg⟩ : ↥H) • (((1 : G) : G ⧸ K)) =
            QuotientGroup.mk ((g : G) * 1) from rfl, mul_one]]
  -- The stabilizer of that coset is `H ⊓ K`.
  have hstab : MulAction.stabilizer ↥H (((1 : G) : G ⧸ K)) = (H ⊓ K).subgroupOf H := by
    ext h
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have hstep : h • (((1 : G) : G ⧸ K)) = (((h : G) : G ⧸ K)) := by
      rw [show h • (((1 : G) : G ⧸ K)) = QuotientGroup.mk ((h : G) * 1) from rfl, mul_one]
    rw [hstep]
    constructor
    · intro hh
      refine ⟨h.2, ?_⟩
      have := QuotientGroup.eq.mp hh
      simpa using this
    · rintro ⟨_, hk⟩
      rw [QuotientGroup.eq]
      simpa using hk
  -- Orbit-stabilizer.
  have hOS : Nat.card ↑(MulAction.orbit ↥H (((1 : G) : G ⧸ K))) *
      Nat.card ↥(MulAction.stabilizer ↥H (((1 : G) : G ⧸ K))) = Nat.card ↥H := by
    rw [← Nat.card_prod]
    exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup ↥H _)
  -- The stabilizer has the same cardinality as `H ⊓ K`.
  have hstabcard : Nat.card ↥(MulAction.stabilizer ↥H (((1 : G) : G ⧸ K))) = Nat.card ↥(H ⊓ K) := by
    rw [hstab, ← Subgroup.card_map_of_injective (f := H.subtype) H.subtype_injective
      (K := (H ⊓ K).subgroupOf H), Subgroup.subgroupOf_map_subtype]
    simp
  have horbitcard : Nat.card ↑(MulAction.orbit ↥H (((1 : G) : G ⧸ K))) =
      Nat.card ↑(QuotientGroup.mk '' (H : Set G) : Set (G ⧸ K)) := by
    rw [horbit]
  -- Hence `|image of H| * |H ⊓ K| = |H|`.
  have key : Nat.card ↑(QuotientGroup.mk '' (H : Set G) : Set (G ⧸ K)) * Nat.card ↥(H ⊓ K) =
      Nat.card ↥H := by
    rw [← horbitcard, ← hstabcard]
    exact hOS
  -- And `|H * K| = |K| * |image of H|`.
  rw [Subgroup.card_mul_eq_card_subgroup_mul_card_quotient K (H : Set G)]
  rw [mul_assoc, key, mul_comm]

end Work.Tame
