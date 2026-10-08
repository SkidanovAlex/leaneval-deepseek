import Mathlib
import Submission.Work.CORE2A.Defs

namespace Work.CORE2A

open Subgroup

/-!
# CORE2A: a Sylow subgroup of `K` whose `G`-normalizer lies in `K` maps to a Sylow
subgroup of `G`

Let `K ≤ G` be finite groups and `P` a Sylow `p`-subgroup of `K`.  Assume the normalizer in `G`
of the image `P₀ = P.map K.subtype` is contained in `K`.  Then `P₀` is a Sylow `p`-subgroup of
`G`, i.e. it is the underlying subgroup of some element of `Sylow p G`.

The mathematics (the classical "normalizer growth" argument):

* `P₀` is a `p`-subgroup of `G` (image of a `p`-group under a homomorphism), so it is contained
  in some Sylow `p`-subgroup `Q` of `G`; by `Sylow.exists_comap_subtype_eq` we may even take `Q`
  with `Q ∩ K = P₀`.
* `N_G(P₀) ∩ Q ≤ K ∩ Q = P₀`, while `P₀ ≤ N_G(P₀) ∩ Q`; hence `N_G(P₀) ∩ Q = P₀`.
* Suppose `P₀ ≠ Q`.  Then `P₀.subgroupOf Q ≠ ⊤` in the finite `p`-group `↥Q`; finite `p`-groups
  satisfy the normalizer condition, so `P₀.subgroupOf Q < N_{↥Q}(P₀.subgroupOf Q)`.  But
  `Subgroup.subgroupOf_normalizer_eq` turns `N_{↥Q}(P₀.subgroupOf Q)` into
  `(N_G(P₀)).subgroupOf Q = (N_G(P₀) ∩ Q).subgroupOf Q = P₀.subgroupOf Q`, a contradiction.
-/

/-- **Sylow `p`-subgroups of a subgroup with self-normalizing image.**  If `P` is a Sylow
`p`-subgroup of `K` and `N_G(P) ≤ K` (where `P` is viewed inside `G`), then the image of `P` in
`G` is a Sylow `p`-subgroup of `G`. -/
theorem map_sylow_isSylow {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    (P : Sylow p ↥K) (hN : Subgroup.normalizer ((P : Subgroup ↥K).map K.subtype : Set G) ≤ K) :
    ∃ P' : Sylow p G, (P' : Subgroup G) = (P : Subgroup ↥K).map K.subtype := by
  -- A Sylow `p`-subgroup `Q` of `G` whose intersection with `K` is the image `P₀` of `P`.
  obtain ⟨Q, hQ⟩ := Sylow.exists_comap_subtype_eq (p := p) P
  set P₀ : Subgroup G := (P : Subgroup ↥K).map K.subtype with hP₀
  refine ⟨Q, ?_⟩
  have hN' : Subgroup.normalizer (P₀ : Set G) ≤ K := hN
  have hQ' : (Q : Subgroup G).subgroupOf K = (P : Subgroup ↥K) := hQ
  -- `Q ∩ K = P₀`.
  have hQK : (Q : Subgroup G) ⊓ K = P₀ := by
    rw [← Subgroup.subgroupOf_map_subtype (Q : Subgroup G) K, hQ', hP₀]
  have hP₀leQ : P₀ ≤ (Q : Subgroup G) := hQK ▸ inf_le_left
  -- `N_G(P₀) ∩ Q = P₀` (sandwiched by `≤ K` and by `P₀ ≤` both factors).
  have hC : Subgroup.normalizer (P₀ : Set G) ⊓ (Q : Subgroup G) = P₀ := by
    refine le_antisymm ?_ ?_
    · calc Subgroup.normalizer (P₀ : Set G) ⊓ (Q : Subgroup G)
          ≤ K ⊓ (Q : Subgroup G) := inf_le_inf hN' le_rfl
        _ = P₀ := by rw [inf_comm, hQK]
    · exact le_inf Subgroup.le_normalizer hP₀leQ
  -- `P₀.subgroupOf Q` is self-normalizing in `↥Q`; the normalizer condition forces it to be `⊤`.
  have hnorm : Subgroup.normalizer (↑(P₀.subgroupOf (Q : Subgroup G))) =
      P₀.subgroupOf (Q : Subgroup G) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hP₀leQ,
        ← Subgroup.inf_subgroupOf_right (Subgroup.normalizer (P₀ : Set G)) (Q : Subgroup G), hC]
  have hnc : NormalizerCondition ↥(Q : Subgroup G) :=
    @Group.normalizerCondition_of_isNilpotent ↥(Q : Subgroup G) _ (Q.isPGroup'.isNilpotent)
  have htop : P₀.subgroupOf (Q : Subgroup G) = ⊤ :=
    (normalizerCondition_iff_only_full_group_self_normalizing.mp hnc) _ hnorm
  exact le_antisymm (Subgroup.subgroupOf_eq_top.mp htop) hP₀leQ

end Work.CORE2A
