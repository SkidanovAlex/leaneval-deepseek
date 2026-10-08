import Mathlib
import Submission.Work.Reductions.Defs
import Submission.Work.Reductions.stronglyEmbedded_normalizer_le
import Submission.Work.DoubleTransitivity.App2.SylowAux

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# The index of a strongly embedded subgroup is odd

`Work.Reductions.stronglyEmbedded_index_odd`: if `H` is strongly embedded in a finite group `G`
(in the sense of the challenge: `H ≠ ⊤`, `|H|` is even, and `|H ⊓ H^g|` is odd for every
`g ∉ H`), then `|G : H|` is odd.

The structural content is the classical Bender-subgroup fact exported above the main theorem as
`stronglyEmbedded_exists_sylow_le`: a strongly embedded subgroup contains a Sylow `2`-subgroup of
the whole group.  Its proof is the standard one.  Let `S` be a Sylow `2`-subgroup of `H` and
`Q ≤ G` its image.  Since `|H|` is even while `S` has odd index in `H`, `|Q| = |S|` is even, so
strong embeddedness gives `N_G(Q) ≤ H` (if `g ∈ N_G(Q) \ H` then `Q ≤ H ⊓ H^g` would force
`|H ⊓ H^g|` to be even, contradicting the strong embeddedness of `H`).  A `2`-subgroup of
`N_G(Q) ≤ H` containing `Q` must equal `Q`, because `Q ≅ S` is a maximal `2`-subgroup of `H`;
hence `Q` is a Sylow `2`-subgroup of `N_G(Q)` and `2 ∤ [N_G(Q) : Q]`.  By the general nilpotency
lemma `not_dvd_index_of_not_dvd_relIndex_normalizer` (`Work.DoubleTransitivity.App2.SylowAux`),
a `p`-subgroup which is a Sylow `p`-subgroup of its own normalizer is already a Sylow
`p`-subgroup of the whole group, so `Q` is a Sylow `2`-subgroup of `G` contained in `H`.

For the index itself: `P ≤ H` for a Sylow `2`-subgroup `P` of `G`, whose index is odd, hence so is
the index of `H`.
-/

set_option autoImplicit false
set_option linter.style.haveILetI false

namespace Work.Reductions

open LeanEval.GroupTheory.Defs

/-- A strongly embedded subgroup of a finite group contains a Sylow `2`-subgroup of the group:
concretely, `H` has even order and `N_G(X) ≤ H` for every even-order subgroup `X ≤ H`, which
forces the `2`-Sylow of `H` to already be a `2`-Sylow of `G`. -/
theorem stronglyEmbedded_exists_sylow_le {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) :
    ∃ P : Sylow 2 G, (P : Subgroup G) ≤ H := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have heven : Even (Nat.card ↥H) := hH.2.1
  -- a Sylow `2`-subgroup `S` of `H`, pushed into `G` as `Q`
  obtain ⟨S⟩ : Nonempty (Sylow 2 ↥H) := Sylow.nonempty (p := 2) (G := ↥H)
  set Q : Subgroup G := Subgroup.map H.subtype (S : Subgroup ↥H) with hQ
  have hQH : Q ≤ H := Subgroup.map_subtype_le _
  have hQpg : IsPGroup 2 Q := (S.isPGroup').map H.subtype
  -- `|Q| = |S|` is even
  have hcardQ : Nat.card Q = Nat.card ↥(S : Subgroup ↥H) :=
    Subgroup.card_map_of_injective (K := (S : Subgroup ↥H)) (f := H.subtype)
      H.subtype_injective
  have h2H : 2 ∣ Nat.card ↥H := even_iff_two_dvd.mp heven
  have h2S : 2 ∣ Nat.card ↥(S : Subgroup ↥H) := by
    have hcard := Subgroup.card_mul_index (S : Subgroup ↥H)
    have hnot : ¬ 2 ∣ (S : Subgroup ↥H).index := Sylow.not_dvd_index S
    have : 2 ∣ Nat.card ↥(S : Subgroup ↥H) * (S : Subgroup ↥H).index := hcard ▸ h2H
    rcases (Nat.Prime.dvd_mul Nat.prime_two).mp this with h | h
    · exact h
    · exact absurd h hnot
  have hQeven : Even (Nat.card Q) := even_iff_two_dvd.mpr (hcardQ ▸ h2S)
  -- strong embeddedness: the normalizer of the even-order `2`-group `Q ≤ H` lies in `H`
  have hNle : Subgroup.normalizer (Q : Set G) ≤ H :=
    stronglyEmbedded_normalizer_le hH hQH hQeven
  -- `Q` is a Sylow `2`-subgroup of `H`
  have hrelH : ¬ 2 ∣ Q.relIndex H := by
    have hEq : Q.relIndex H = (S : Subgroup ↥H).index := by
      show (Q.subgroupOf H).index = (S : Subgroup ↥H).index
      congr 1
      rw [hQ, ← Subgroup.comap_subtype, Subgroup.comap_map_eq, Subgroup.ker_subtype, sup_bot_eq]
    rw [hEq]
    exact Sylow.not_dvd_index S
  -- any `2`-subgroup of `N_G(Q) ≤ H` containing `Q` must be `Q`: so `Q` is Sylow in `N_G(Q)`
  have hrelN : ¬ 2 ∣ Q.relIndex (Subgroup.normalizer (Q : Set G)) := by
    intro hdvd
    refine hrelH ?_
    rw [← Subgroup.relIndex_mul_relIndex Q (Subgroup.normalizer (Q : Set G)) H
      Subgroup.le_normalizer hNle]
    exact dvd_mul_of_dvd_left hdvd _
  -- hence `Q` is a Sylow `2`-subgroup of `G`, and it lies in `H`
  exact ⟨hQpg.toSylow (Work.DoubleTransitivity.App2.not_dvd_index_of_not_dvd_relIndex_normalizer
    hQpg hrelN), hQH⟩

/-- A strongly embedded subgroup of a finite group has odd index. -/
theorem stronglyEmbedded_index_odd {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) : Odd H.index := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hPH⟩ := stronglyEmbedded_exists_sylow_le hH
  -- a Sylow `2`-subgroup of `G` has odd index, and `[G : P] = [G : H] * [H : P]`
  have hPind : ¬ 2 ∣ (P : Subgroup G).index := Sylow.not_dvd_index P
  exact Nat.not_even_iff_odd.mp fun hev =>
    hPind (dvd_trans (even_iff_two_dvd.mp hev) (Subgroup.index_dvd_of_le hPH))

end Work.Reductions
