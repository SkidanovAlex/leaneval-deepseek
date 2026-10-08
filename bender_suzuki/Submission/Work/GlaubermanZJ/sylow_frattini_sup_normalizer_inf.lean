import Mathlib
import Submission.Work.GlaubermanZJ.theorem3_2_defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

/-!
# Frattini's argument for a normal subgroup and a Sylow subgroup

Glauberman 1968, Lemma 3.6 (p. 1109) is the Frattini argument: for `H ⊴ G` finite and `S` a
Sylow `p`-subgroup of `H`, one has `G = H · N_G(S)`.  In the proof of Theorem 3.2 it is applied
with `H = L` (the largest normal subgroup of `G` inside `N(C)`) and the Sylow `p`-subgroup
`L ∩ S` of `L` (where `S` is a Sylow `p`-subgroup of `G`): `G = L · N_G(L ∩ S)`.

The only content beyond Mathlib's `Sylow.normalizer_sup_eq_top` is that `L ∩ S` is indeed a
Sylow `p`-subgroup of `L`, i.e. that `|L : L ∩ S|` is not divisible by `p`.  This follows from
the identity `|L : L ∩ S| = |L ⊔ S : S|` (the second isomorphism theorem for the normal
subgroup `L`): `|L : L ∩ S|` divides `|G : S|`, which is prime to `p`.
-/

set_option autoImplicit false

open scoped Classical Pointwise

namespace Work.GlaubermanZJ

variable {X : Type*} [Group X] [Finite X] {p : ℕ}

/-- Auxiliary index identity: `|S : S ⊓ L| = |L ⊔ S : S|` for a normal subgroup `L`, i.e.
`S.relIndex L = S.relIndex (L ⊔ S)`. -/
theorem relIndex_inf_eq_relIndex_sup {S : Subgroup X} (L : Subgroup X) [L.Normal] :
    S.relIndex L = S.relIndex (L ⊔ S) := by
  have hnonzero : ∀ H : Subgroup X, H.index ≠ 0 := by
    intro H h0
    have h := Subgroup.card_mul_index H
    rw [h0, mul_zero] at h
    exact (Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩) h.symm
  have hBpos : 0 < L.relIndex S := by
    have h := Subgroup.card_mul_index (L.subgroupOf S)
    rw [show (L.subgroupOf S).index = L.relIndex S from rfl] at h
    have hS : Nat.card ↥(S) ≠ 0 := Nat.card_ne_zero.mpr ⟨⟨1⟩, inferInstance⟩
    exact Nat.pos_of_ne_zero fun h0 => by rw [h0, mul_zero] at h; exact hS h.symm
  -- `S.relIndex L * L.index = (L ⊓ S).index`
  have h1 : S.relIndex L * L.index = (L ⊓ S).index := by
    rw [← Subgroup.inf_relIndex_left (H := L) (K := S)]
    exact Subgroup.relIndex_mul_index inf_le_left
  -- `L.relIndex (L ⊔ S) = L.relIndex S` and `L.relIndex (L ⊔ S) * (L ⊔ S).index = L.index`
  have h2 : L.relIndex S * (L ⊔ S).index = L.index := by
    rw [← Subgroup.relIndex_sup_left (H := S) (K := L)]
    exact Subgroup.relIndex_mul_index le_sup_left
  -- `L.relIndex S * S.index = (L ⊓ S).index`
  have h3 : L.relIndex S * S.index = (L ⊓ S).index := by
    rw [← Subgroup.inf_relIndex_right (H := L) (K := S)]
    exact Subgroup.relIndex_mul_index inf_le_right
  -- `S.relIndex (L ⊔ S) * (L ⊔ S).index = S.index`
  have h4 : S.relIndex (L ⊔ S) * (L ⊔ S).index = S.index :=
    Subgroup.relIndex_mul_index le_sup_right
  -- the two expressions for `L.relIndex S * S.index`
  have hkey : L.relIndex S * (S.relIndex (L ⊔ S) * (L ⊔ S).index)
      = S.relIndex L * (L.relIndex S * (L ⊔ S).index) := by
    rw [h4, h3, ← h1, ← h2]
  have hUpos : 0 < (L ⊔ S).index := Nat.pos_of_ne_zero (hnonzero _)
  have hcancel : L.relIndex S * S.relIndex (L ⊔ S) = L.relIndex S * S.relIndex L := by
    apply Nat.eq_of_mul_eq_mul_right hUpos
    calc (L.relIndex S * S.relIndex (L ⊔ S)) * (L ⊔ S).index
        = L.relIndex S * (S.relIndex (L ⊔ S) * (L ⊔ S).index) := by ring
      _ = L.relIndex S * S.index := by rw [h4]
      _ = (L ⊓ S).index := h3
      _ = S.relIndex L * L.index := h1.symm
      _ = S.relIndex L * (L.relIndex S * (L ⊔ S).index) := by rw [← h2]
      _ = (L.relIndex S * S.relIndex L) * (L ⊔ S).index := by ring
  exact (Nat.eq_of_mul_eq_mul_left hBpos hcancel).symm

/-- `|L : L ⊓ S|` is coprime to `p` for `L ⊴ X` and `S : Sylow p X`: it divides `|X : S|`. -/
theorem not_dvd_relIndex_inf_sylow (hp : p.Prime) {L : Subgroup X} [L.Normal] (S : Sylow p X) :
    ¬ p ∣ (L ⊓ (S : Subgroup X)).relIndex L := by
  haveI : Fact p.Prime := ⟨hp⟩
  rw [Subgroup.inf_relIndex_left (H := L) (K := (S : Subgroup X))]
  rw [relIndex_inf_eq_relIndex_sup L]
  exact fun h => S.not_dvd_index (h.trans ⟨(L ⊔ (S : Subgroup X)).index,
    (Subgroup.relIndex_mul_index (le_sup_right : (S : Subgroup X) ≤ L ⊔ (S : Subgroup X))).symm⟩)

/-- **Frattini's argument** in the form used in the proof of Glauberman's Theorem 3.2: for a
normal subgroup `L` of the finite group `X` and a Sylow `p`-subgroup `S` of `X`,
`X = L · N_X(L ∩ S)`. -/
theorem sylow_frattini_sup_normalizer_inf (hp : p.Prime) {L : Subgroup X} [L.Normal]
    (S : Sylow p X) :
    L ⊔ Subgroup.normalizer ((L ⊓ (S : Subgroup X) : Subgroup X) : Set X) = ⊤ := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hsub : (L ⊓ (S : Subgroup X)).subgroupOf L = (S : Subgroup X).subgroupOf L := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨x.2, h⟩⟩
  have hidx' : ¬ p ∣ (L ⊓ (S : Subgroup X)).relIndex L := not_dvd_relIndex_inf_sylow hp S
  have hidx : ¬ p ∣ ((S : Subgroup X).subgroupOf L).index := by
    rw [← hsub]
    exact hidx'
  have hpg : IsPGroup p ((S : Subgroup X).subgroupOf L) := by
    rw [← Subgroup.comap_subtype (S : Subgroup X) L]
    exact IsPGroup.comap_subtype S.isPGroup'
  let T : Sylow p ↥L := hpg.toSylow hidx
  have h := Sylow.normalizer_sup_eq_top T
  have hmap : ((T : Subgroup ↥L).map L.subtype) = L ⊓ (S : Subgroup X) := by
    change Subgroup.map L.subtype ((S : Subgroup X).subgroupOf L) = L ⊓ (S : Subgroup X)
    rw [Subgroup.subgroupOf_map_subtype, inf_comm]
  rw [hmap, sup_comm] at h
  exact h

end Work.GlaubermanZJ
