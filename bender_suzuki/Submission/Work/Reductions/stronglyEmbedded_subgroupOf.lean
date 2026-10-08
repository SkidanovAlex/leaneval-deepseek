import Mathlib
import Submission.Work.Reductions.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Strong embeddedness passes to `X` for `H ⊓ X`

`Work.Reductions.stronglyEmbedded_subgroupOf`: if `H` is strongly embedded in `G` and
`X ≤ G` is a subgroup which is not contained in `H` and for which `H ⊓ X` has even order,
then `H ⊓ X`, viewed as a subgroup of `X`, is strongly embedded in `X`.

This is the conjugation-invariant core of the reduction: for `g ∈ X \ H` the subgroup
`(H ⊓ X) ⊓ (H ⊓ X)^g ≤ X` (conjugation taken inside `X`) embeds, via `X ↪ G`, into the
subgroup `H ⊓ H^g ≤ G`, whose order is odd by strong embeddedness of `H`.  Being a subgroup
of an odd-order group, its order is a divisor of an odd number, hence odd.

The hypothesis `H ⊓ X ≠ X` is exactly properness of `H ⊓ X` in `X`, and
`Even (Nat.card ↥(H ⊓ X))` is exactly evenness of the order of `H ⊓ X ≤ X`; the two orders
coincide because `(H ⊓ X).subgroupOf X` maps isomorphically onto `H ⊓ X` under the inclusion
`X ↪ G`.
-/

set_option autoImplicit false

open LeanEval.GroupTheory.Defs

namespace Work.Reductions

theorem stronglyEmbedded_subgroupOf {G : Type} [Group G] {H X : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) (hne : H ⊓ X ≠ X)
    (heven : Even (Nat.card ↥(H ⊓ X))) :
    LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((H ⊓ X).subgroupOf X) := by
  refine ⟨?_, ?_, ?_⟩
  · -- properness: `(H ⊓ X).subgroupOf X = ⊤` forces `X ≤ H ⊓ X`, i.e. `H ⊓ X = X`.
    intro htop
    exact hne (le_antisymm inf_le_right (Subgroup.subgroupOf_eq_top.mp htop))
  · -- the order of `(H ⊓ X).subgroupOf X` is the order of `H ⊓ X`: the inclusion `X ↪ G`
    -- carries one onto the other.
    have hcard : Nat.card ↥((H ⊓ X).subgroupOf X) = Nat.card ↥(H ⊓ X) := by
      rw [← Subgroup.card_map_of_injective (K := (H ⊓ X).subgroupOf X) (f := X.subtype)
            X.subtype_injective,
        Subgroup.map_subgroupOf_eq_of_le (inf_le_right : H ⊓ X ≤ X)]
    rwa [hcard]
  · -- the intersection condition: for `g ∈ X \ H`, `(H ⊓ X) ⊓ (H ⊓ X)^g` embeds in
    -- `H ⊓ H^g` through `X ↪ G`, and `|H ⊓ H^g|` is odd.
    intro g hg
    have hgH : (g : G) ∉ H := fun h => hg ⟨h, g.2⟩
    have hodd := hH.2.2 (g : G) hgH
    have hle : ((H ⊓ X).subgroupOf X ⊓ ((H ⊓ X).subgroupOf X).map
          (MulAut.conj g).toMonoidHom).map X.subtype
        ≤ H ⊓ H.map (MulAut.conj (g : G)).toMonoidHom := by
      rintro z hz
      rw [Subgroup.mem_map] at hz
      obtain ⟨y, hy, rfl⟩ := hz
      rw [Subgroup.mem_inf] at hy ⊢
      refine ⟨?_, ?_⟩
      · exact hy.1.1
      · rw [Subgroup.mem_map] at hy ⊢
        obtain ⟨m, hm, hmx⟩ := hy.2
        refine ⟨(m : G), hm.1, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hmx ⊢
        simpa using congrArg (Subtype.val) hmx
    have hdvd : Nat.card ↥((H ⊓ X).subgroupOf X ⊓ ((H ⊓ X).subgroupOf X).map
          (MulAut.conj g).toMonoidHom)
        ∣ Nat.card ↥(H ⊓ H.map (MulAut.conj (g : G)).toMonoidHom) := by
      rw [← Subgroup.card_map_of_injective (K := (H ⊓ X).subgroupOf X ⊓
            ((H ⊓ X).subgroupOf X).map (MulAut.conj g).toMonoidHom) (f := X.subtype)
            X.subtype_injective]
      exact Subgroup.card_dvd_of_le hle
    refine Nat.not_even_iff_odd.mp fun h2 => ?_
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (dvd_trans (even_iff_two_dvd.mp h2) hdvd))

end Work.Reductions
