import Mathlib
import Submission.Work.BG.indexEqCardOfNormalSup

namespace Work.BG

/-- If `B` and `K` are subgroups of a finite group `G` with `K` normalized by `B ⊔ K`
and `B ⊓ K = ⊥`, then the relative index of `B` in `B ⊔ K` equals `|K|`.

This is the statement that `B ⊔ K` is (as a set) the direct product `B * K`, so that
`[B ⊔ K : B] = |K|`. -/
theorem relIndex_sup_eq_card_of_inf_eq_bot {G : Type} [Group G] [Finite G]
    (B K : Subgroup G) (hN : B ⊔ K ≤ Subgroup.normalizer (K : Set G)) (hinf : B ⊓ K = ⊥) :
    B.relIndex (B ⊔ K) = Nat.card K := by
  -- `K` is normal in `B ⊔ K`, since `B ⊔ K` normalizes `K`.
  have hK' : (K.subgroupOf (B ⊔ K)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hN
  -- `B ⊓ K = ⊥` transfers to trivial intersection inside `B ⊔ K`.
  have hinf' : (B.subgroupOf (B ⊔ K) ⊓ K.subgroupOf (B ⊔ K) : Subgroup ↥(B ⊔ K)) = ⊥ := by
    rw [show (B.subgroupOf (B ⊔ K) : Subgroup ↥(B ⊔ K)) = B.comap (B ⊔ K).subtype from rfl,
      show (K.subgroupOf (B ⊔ K) : Subgroup ↥(B ⊔ K)) = K.comap (B ⊔ K).subtype from rfl,
      ← Subgroup.comap_inf, hinf]
    exact Subgroup.bot_subgroupOf (B ⊔ K)
  -- `B ⊔ K` is the whole group, viewed inside itself.
  have hsup' : (B.subgroupOf (B ⊔ K) ⊔ K.subgroupOf (B ⊔ K) : Subgroup ↥(B ⊔ K)) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (le_sup_left) (le_sup_right)]
    simp
  -- Noether's second isomorphism theorem content, packaged as `indexEqCardOfNormalSup`.
  have key :=
    indexEqCardOfNormalSup (B.subgroupOf (B ⊔ K)) (K.subgroupOf (B ⊔ K)) hK' hsup' hinf'
  -- `K` and its copy inside `B ⊔ K` have the same cardinality.
  have hcard' : Nat.card (K.subgroupOf (B ⊔ K)) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : K ≤ B ⊔ K)).toEquiv
  rw [← hcard']
  exact key

end Work.BG
