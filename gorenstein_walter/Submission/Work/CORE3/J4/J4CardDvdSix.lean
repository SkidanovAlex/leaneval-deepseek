import Mathlib
import Submission.Work.CORE3.Defs

/-!
# `Work.CORE3.J4.J4CardDvdSix`

If `X, W ≤ L`, `W ⊴ L` (i.e. `L ≤ N_G(W)`), `X ⊓ W = ⊥` and `[L : W] = 6`, then `|X| ∣ 6`.

Mathematically: the second isomorphism theorem gives `X ≅ XW/W`, and `XW/W` is a subgroup of
`L/W` of order `[L : W] = 6`; Lagrange's theorem gives `|X| ∣ 6`.

Formalisation: we work inside the ambient group `↥L` and use `relIndex`, which is the index of
`W.subgroupOf L` in `↥L`.  The chain of identities is

* `Nat.card ↥(X.subgroupOf L) = Nat.card X` (`Subgroup.card_subtype`, `map_subgroupOf_eq_of_le`);
* `Nat.card ↥(X.subgroupOf L) = (W.subgroupOf L).relIndex (X.subgroupOf L)`
  (`Subgroup.inf_relIndex_right`, `relIndex_bot_left`, disjointness of `X` and `W`);
* `(W.subgroupOf L).relIndex (X.subgroupOf L) ∣ (W.subgroupOf L).index = 6`
  (`Subgroup.relIndex_dvd_index_of_normal` for the normal subgroup `W.subgroupOf L`, and
  `Subgroup.relIndex_subgroupOf` + `relIndex_top_right` for the index).
-/

namespace Work.CORE3.J4

open Subgroup

theorem J4CardDvdSix {G : Type} [Group G] [Finite G] {X W L : Subgroup G}
    (hXW : X ⊓ W = ⊥) (hXL : X ≤ L) (hWL : W ≤ L)
    (hNW : L ≤ Subgroup.normalizer (W : Set G)) (hrel : W.relIndex L = 6) :
    Nat.card X ∣ 6 := by
  -- `W ⊴ L` becomes normality of `W.subgroupOf L` in the ambient group `↥L`.
  have hWnorm : (W.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWL).mpr hNW
  -- `|X.subgroupOf L| = |X|`.
  have hXcard : Nat.card ↥(X.subgroupOf L) = Nat.card X := by
    have h := Subgroup.card_subtype L (X.subgroupOf L)
    rw [Subgroup.map_subgroupOf_eq_of_le hXL] at h
    exact h.symm
  -- `X` and `W` stay disjoint inside `L`.
  have hinf : W.subgroupOf L ⊓ X.subgroupOf L = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf] at hx
    have hxW : (x : G) ∈ W := Subgroup.mem_subgroupOf.mp hx.1
    have hxX : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hx.2
    have hx0 : (x : G) ∈ X ⊓ W := ⟨hxX, hxW⟩
    rw [hXW] at hx0
    exact Subtype.ext (Subgroup.mem_bot.mp hx0)
  -- `[↥L : W.subgroupOf L] = [L : W] = 6`.
  have hidx : (W.subgroupOf L).index = 6 := by
    have h := Subgroup.relIndex_subgroupOf (H := W) (K := L) (L := L) le_rfl
    rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right, hrel] at h
    exact h
  -- Disjointness turns `|X.subgroupOf L|` into the relative index of `W` over `X`.
  have hcard : Nat.card ↥(X.subgroupOf L) = (W.subgroupOf L).relIndex (X.subgroupOf L) := by
    rw [← Subgroup.inf_relIndex_right (W.subgroupOf L) (X.subgroupOf L), hinf,
      Subgroup.relIndex_bot_left]
  have hdvd : (W.subgroupOf L).relIndex (X.subgroupOf L) ∣ 6 := by
    rw [← hidx]
    exact Subgroup.relIndex_dvd_index_of_normal (W.subgroupOf L) (X.subgroupOf L)
  rw [← hXcard, hcard]
  exact hdvd

end Work.CORE3.J4
