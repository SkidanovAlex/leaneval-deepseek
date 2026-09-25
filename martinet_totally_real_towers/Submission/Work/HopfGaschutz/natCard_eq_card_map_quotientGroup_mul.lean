import Mathlib

/-!
# `Work.HopfGaschutz.natCard_eq_card_map_quotientGroup_mul`

The order of a finite subgroup `V` of a group `G` is the order of its image in `G ⧸ C` times the
order of `C`, for a normal subgroup `C ≤ V`:

`|V| = |V ⧸ C| · |C| = |V.map (QuotientGroup.mk' C)| · |C|`.

This is Lagrange's theorem for the quotient of `V` by the normal subgroup `C`, transported along
Noether's first isomorphism theorem `V ⧸ C ≃* V.map (QuotientGroup.mk' C)`.

The finiteness hypothesis `hfin` is not needed for the identity as stated: `Nat.card` is `0` on
infinite types and Mathlib's Lagrange lemma `Subgroup.card_eq_card_quotient_mul_card_subgroup` is
unconditional, so the result holds in general (and the hypothesis is kept only to match the
requested statement).
-/

namespace Work.HopfGaschutz

-- `hfin` is part of the requested statement but the identity holds without it; silence the
-- unused-variable linter rather than weakening the statement.
set_option linter.unusedVariables false in
theorem natCard_eq_card_map_quotientGroup_mul {G : Type*} [Group G] {V C : Subgroup G} [C.Normal]
    (hC : C ≤ V) (hfin : Finite ↥V) :
    Nat.card ↥V = Nat.card ↥(V.map (QuotientGroup.mk' C)) * Nat.card ↥C := by
  -- Noether's first isomorphism theorem for the restricted projection `V → G ⧸ C`.
  let ψ : ↥V →* G ⧸ C := (QuotientGroup.mk' C).comp V.subtype
  have hker : ψ.ker = C.subgroupOf V := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show ((QuotientGroup.mk' C) (x : G) = 1) ↔ ((x : G) ∈ C)
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hrange : ψ.range = V.map (QuotientGroup.mk' C) := by
    ext y
    rw [MonoidHom.mem_range, Subgroup.mem_map]
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨(x : G), x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have hiso : Nat.card (↥V ⧸ (C.subgroupOf V)) = Nat.card ↥(V.map (QuotientGroup.mk' C)) := by
    have h := Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    rwa [hker, hrange] at h
  -- `C.subgroupOf V` and `C` have the same elements, since `C ≤ V`.
  have hcardC : Nat.card ↥(C.subgroupOf V) = Nat.card ↥C :=
    Nat.card_congr
      { toFun := fun x => ⟨((x : ↥V) : G), (Subgroup.mem_subgroupOf.mp x.2)⟩
        invFun := fun c => ⟨⟨(c : G), hC c.2⟩, (Subgroup.mem_subgroupOf.mpr c.2)⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun c => by ext; rfl }
  -- Lagrange in `V`, then transport the quotient along the isomorphism above.
  have hlag := Subgroup.card_eq_card_quotient_mul_card_subgroup (C.subgroupOf V)
  rw [hlag, hiso, hcardC]

end Work.HopfGaschutz
