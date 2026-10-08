import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.PGroup.lt_normalizer_inf

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# `Work.ThmF.ChV3.Prove.card_eq_pPart_of_card_normalizer`

If a `p`-subgroup `R ≤ G` has order equal to the `p`-part of the order of its own normalizer
`N_G(R)`, then `R` is a Sylow `p`-subgroup of `G`: its order is the `p`-part of `|G|`.

Proof.  Let `Q` be a Sylow `p`-subgroup of `G` containing `R` (`IsPGroup.exists_le_sylow`).  If
`R < Q`, the normalizer condition for the finite `p`-group `Q` (`Work.PGroup.lt_normalizer_inf`)
gives `R < Q ⊓ N_G(R)`, so `Q ⊓ N_G(R)` is a `p`-subgroup of `N_G(R)` strictly bigger than `R`.
But every `p`-subgroup of `N_G(R)` has order dividing `|N_G(R)|_p = |R|`, a contradiction.  Hence
`R = Q` and `|R| = |Q| = |G|_p`.
-/

set_option autoImplicit false

namespace Work.ThmF.ChV3.Prove

open Classical

/-- A `p`-subgroup `X` of a finite group, contained in the subgroup `K`, has order at most the
`p`-part of `|K|`. -/
private lemma card_le_pPart_of_le {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {X K : Subgroup G} (hXK : X ≤ K) (hX : IsPGroup p X) :
    Nat.card X ≤ Work.ThmF.ChV3.pPart p (Nat.card ↥K) := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, hk⟩ := hX.exists_card_eq
  have hcard : Nat.card ↥(X.subgroupOf K) = p ^ k := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXK).toEquiv, hk]
  have hdvd : Nat.card ↥(X.subgroupOf K) ∣ Nat.card ↥K :=
    Subgroup.card_subgroup_dvd_card (X.subgroupOf K)
  rw [hcard] at hdvd
  have hle : k ≤ (Nat.card ↥K).factorization p :=
    (hp.pow_dvd_iff_le_factorization (Nat.card_pos.ne')).mp hdvd
  calc Nat.card X = p ^ k := hk
    _ ≤ p ^ (Nat.card ↥K).factorization p := Nat.pow_le_pow_right hp.pos hle
    _ = Work.ThmF.ChV3.pPart p (Nat.card ↥K) := rfl

theorem card_eq_pPart_of_card_normalizer {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {R : Subgroup G} (hR : IsPGroup p R)
    (hcard : Nat.card R = Work.ThmF.ChV3.pPart p (Nat.card ↥(Subgroup.normalizer (R : Set G)))) :
    Nat.card R = Work.ThmF.ChV3.pPart p (Nat.card G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  -- a Sylow `p`-subgroup `Q` of `G` containing `R`
  obtain ⟨Q, hRQ⟩ := IsPGroup.exists_le_sylow hR
  -- `R` exhausts `Q`
  have hQle : (Q : Subgroup G) ≤ R := by
    by_contra hQnle
    have hne : R ≠ (Q : Subgroup G) := fun h => hQnle h.ge
    have hlt : R < (Q : Subgroup G) := lt_of_le_of_ne hRQ hne
    -- a proper subgroup of the `p`-group `Q` is strictly contained in its normalizer
    have hlt2 : R < (Q : Subgroup G) ⊓ Subgroup.normalizer (R : Set G) :=
      Work.PGroup.lt_normalizer_inf hp Q.isPGroup' hlt
    -- but `Q ⊓ N_G(R)` is a `p`-subgroup of `N_G(R)`, whose `p`-part is `|R|`
    have hXpg : IsPGroup p ↥((Q : Subgroup G) ⊓ Subgroup.normalizer (R : Set G)) :=
      Q.isPGroup'.to_inf_left
    have hcardX : Nat.card ↥((Q : Subgroup G) ⊓ Subgroup.normalizer (R : Set G)) ≤ Nat.card R := by
      have h1 := card_le_pPart_of_le hp inf_le_right hXpg
      rwa [← hcard] at h1
    have hRXle : R ≤ (Q : Subgroup G) ⊓ Subgroup.normalizer (R : Set G) :=
      le_inf hRQ Subgroup.le_normalizer
    have heqX : R = (Q : Subgroup G) ⊓ Subgroup.normalizer (R : Set G) := by
      refine SetLike.coe_injective (Set.eq_of_subset_of_ncard_le hRXle ?_)
      rw [← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
      exact hcardX
    exact (ne_of_lt hlt2) heqX
  -- hence `R` is a Sylow `p`-subgroup of `G`
  have hRQeq : R = (Q : Subgroup G) := le_antisymm hRQ hQle
  rw [hRQeq, Work.ThmF.ChV3.pPart]
  exact Sylow.card_eq_multiplicity Q

end Work.ThmF.ChV3.Prove
