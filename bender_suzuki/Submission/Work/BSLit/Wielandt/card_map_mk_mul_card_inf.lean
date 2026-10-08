import Mathlib

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The image of a subgroup in a quotient group, and the intersection with the kernel

For a group `Q`, a subgroup `C ≤ Q` and a **normal** subgroup `N ◁ Q`, the restriction to `C` of
the quotient map `Q →* Q ⧸ N` is a homomorphism `φ : C →* Q ⧸ N` whose kernel is
`N.subgroupOf C` (i.e. `C ⊓ N`) and whose range is the subgroup `C.map (QuotientGroup.mk' N)` of
`Q ⧸ N`.  Hence, by the first isomorphism theorem
(`QuotientGroup.quotientKerEquivRange`) together with
`Subgroup.card_eq_card_quotient_mul_card_subgroup` (the cardinality of a group is the index times
the cardinality of the subgroup),

  `|C| = |C.map (QuotientGroup.mk' N)| * |C ⊓ N|`,

as an identity of `Nat.card`s (the statement is valid for infinite groups as well: `Nat.card` is
`0` there, and the product degenerates accordingly).  This instance of the `C`, `N`
decomposition of `Q`, resp. of `C`, is used in Wielandt's counting argument.
-/

namespace Work.BSLit.Wielandt

theorem card_map_mk_mul_card_inf {Q : Type*} [Group Q] (C N : Subgroup Q) [N.Normal] :
    Nat.card ↥C = Nat.card ↥(C.map (QuotientGroup.mk' N)) * Nat.card ↥(C ⊓ N) := by
  -- the restriction to `C` of the quotient map
  let φ : ↥C →* Q ⧸ N := (QuotientGroup.mk' N).comp C.subtype
  -- its kernel is `C ⊓ N`
  have hker : φ.ker = N.subgroupOf C := by
    change ((QuotientGroup.mk' N).comp C.subtype).ker = N.subgroupOf C
    rw [← MonoidHom.comap_ker (QuotientGroup.mk' N) C.subtype,
      QuotientGroup.ker_mk', Subgroup.comap_subtype]
  -- its range is `C.map (QuotientGroup.mk' N)`
  have hran : φ.range = C.map (QuotientGroup.mk' N) := by
    change ((QuotientGroup.mk' N).comp C.subtype).range = C.map (QuotientGroup.mk' N)
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  -- `|ker φ| = |C ⊓ N|`
  have hcardker : Nat.card ↥φ.ker = Nat.card ↥(C ⊓ N) := by
    rw [hker, ← Subgroup.card_map_of_injective (K := N.subgroupOf C) C.subtype_injective,
      Subgroup.subgroupOf_map_subtype, inf_comm]
  calc Nat.card ↥C
      = Nat.card (↥C ⧸ φ.ker) * Nat.card ↥φ.ker :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker
    _ = Nat.card ↥φ.range * Nat.card ↥φ.ker := by
        rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv]
    _ = Nat.card ↥(C.map (QuotientGroup.mk' N)) * Nat.card ↥(C ⊓ N) := by
        rw [hran, hcardker]

end Work.BSLit.Wielandt
