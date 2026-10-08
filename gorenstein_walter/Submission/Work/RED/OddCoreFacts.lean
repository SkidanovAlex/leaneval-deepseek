import Mathlib
import Submission.Work.RED.Basic
import Submission.OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315

/-!
# The `O(G)` API (`Work.RED.GW2.OddCoreFactsProp`)

`Work.RED.GW2.oddCore G = (sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}).normalCore` is
the largest normal odd-order subgroup `O(G) = O_{2'}(G)` of `G`.  This file discharges
`Work.RED.GW2.OddCoreFactsProp`, the elementary API of `O(G)` used by the RED induction:

* `oddCore_characteristic` — `O(G)` is characteristic (true for *all* groups, so proved here
  directly, by transporting the defining family of subgroups along an automorphism);
* `oddCore_odd` — `O(G)` has odd order (finite `G`), transported from the odd-order library's
  `2'`-radical `O_{2'}(G) = OddOrder.Isaacs.Ch03.oPiCore {q | q ≠ 2} G` (`oPiCore.isPiGroup`);
* `le_oddCore_of_odd_normal` — every normal odd-order subgroup lies in `O(G)` (maximality);
* `eq_top_of_odd` — `O(G) = ⊤` when `|G|` is odd;
* `oddCore_map_subtype_le` — `O(K) ≤ O(G)` for `K ⊴ G`: `O(K)` is characteristic in `K`, hence
  (as a subgroup of `G`) normal, and of odd order, so maximality applies;
* `oddCore_quotient_self` — `O(G/O(G)) = 1`;
* `card_quotient_oddCore_lt` — `|G/O(G)| < |G|` when `O(G) ≠ 1`.
-/

namespace Work.RED.GW2

open Subgroup

/-! ## `O(G) = O_{2'}(G)`: the bridge to the odd-order library -/

/-- A subgroup of a finite group has odd order iff every prime dividing its order is odd. -/
theorem odd_iff_isPiSubgroup_ne_two {G : Type*} [Group G] [Finite G] (N : Subgroup G) :
    Odd (Nat.card N) ↔ Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) N := by
  unfold Subgroup.IsPiSubgroup
  have hne : Nat.card ↥N ≠ 0 := (Nat.card_pos (α := ↥N)).ne'
  constructor
  · intro hodd q hq hq2
    rw [hq2] at hq
    exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (Nat.mem_primeFactors.mp hq).2.1)
  · intro h
    rw [← Nat.not_even_iff_odd]
    intro heven
    exact h 2 (Nat.mem_primeFactors.mpr
      ⟨by norm_num, even_iff_two_dvd.mp heven, hne⟩) rfl

/-- The supremum of the normal `π`-subgroups is the library's `O_π(G)`. -/
theorem sSup_normal_isPiSubgroup_eq_oPiCore {G : Type*} [Group G] (π : Set ℕ) :
    sSup {N : Subgroup G | N.Normal ∧ Subgroup.IsPiSubgroup π N}
      = OddOrder.Isaacs.Ch03.oPiCore π G := by
  rw [OddOrder.Isaacs.Ch03.oPiCore]
  refine le_antisymm (sSup_le ?_) (iSup_le ?_)
  · rintro N ⟨hN, hpN⟩
    exact le_iSup_of_le ⟨N, hN, hpN⟩ le_rfl
  · rintro ⟨N, hN1, hN2⟩
    exact le_sSup ⟨hN1, hN2⟩

/-- `O_π(G)` is normal, so taking `normalCore` of it changes nothing. -/
theorem normalCore_oPiCore {G : Type*} [Group G] (π : Set ℕ) :
    (OddOrder.Isaacs.Ch03.oPiCore π G).normalCore = OddOrder.Isaacs.Ch03.oPiCore π G :=
  Subgroup.normalCore_eq_self _

/-- `O(G) = O_{2'}(G)`. -/
theorem oddCore_eq_oPiCore {G : Type*} [Group G] [Finite G] :
    oddCore G = OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2}) G := by
  have hset : {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}
      = {N : Subgroup G | N.Normal ∧ Subgroup.IsPiSubgroup ({q : ℕ | q ≠ 2}) N} := by
    ext N
    exact and_congr_right fun _ => odd_iff_isPiSubgroup_ne_two N
  rw [oddCore, hset, sSup_normal_isPiSubgroup_eq_oPiCore, normalCore_oPiCore]

/-! ## `O(G)` is characteristic -/

/-- Membership of the defining family of `oddCore` is preserved by isomorphisms. -/
theorem map_mem_oddNormal {G H : Type*} [Group G] [Group H] (e : G ≃* H) {N : Subgroup G}
    (hN : N.Normal) (hodd : Odd (Nat.card N)) :
    (Subgroup.map e.toMonoidHom N).Normal ∧
      Odd (Nat.card (Subgroup.map e.toMonoidHom N)) :=
  ⟨hN.map e.toMonoidHom e.surjective,
    by rw [Subgroup.card_map_of_injective e.injective]; exact hodd⟩

/-- The family of normal odd-order subgroups is invariant under an automorphism. -/
theorem image_map_oddNormal {G : Type*} [Group G] (e : G ≃* G) :
    Subgroup.map e.toMonoidHom '' {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}
      = {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)} := by
  ext N
  constructor
  · rintro ⟨M, hM, rfl⟩
    exact map_mem_oddNormal e hM.1 hM.2
  · intro hN
    refine ⟨Subgroup.map e.symm.toMonoidHom N, map_mem_oddNormal e.symm hN.1 hN.2, ?_⟩
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id G := by
      ext x
      simp
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]

/-- `sSup` is transported by a homomorphism (only injectivity is used, through the Galois
connection `map ⊣ comap`). -/
theorem map_sSup_map {G H : Type*} [Group G] [Group H] (e : G ≃* H)
    (S : Set (Subgroup G)) :
    Subgroup.map e.toMonoidHom (sSup S) = sSup (Subgroup.map e.toMonoidHom '' S) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun N hN => ?_
    have hN' : Subgroup.map e.toMonoidHom N ∈ Subgroup.map e.toMonoidHom '' S :=
      ⟨N, hN, rfl⟩
    intro x hx
    exact le_sSup hN' ⟨x, hx, rfl⟩
  · refine sSup_le fun M hM => ?_
    rcases hM with ⟨N, hN, rfl⟩
    exact Subgroup.map_mono (f := e.toMonoidHom) (le_sSup hN)

/-- `O(G)` is characteristic, for arbitrary `G`. -/
instance oddCore_characteristic (G : Type*) [Group G] : (oddCore G).Characteristic := by
  refine Subgroup.characteristic_iff_map_le.mpr fun φ => ?_
  have hmap : Subgroup.map φ.toMonoidHom
        (sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)})
      = sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)} := by
    rw [map_sSup_map φ, image_map_oddNormal φ]
  have hmapN : (Subgroup.map φ.toMonoidHom (oddCore G)).Normal :=
    (inferInstance : (oddCore G).Normal).map φ.toMonoidHom φ.surjective
  refine Subgroup.normal_le_normalCore.mpr ?_
  exact (Subgroup.map_mono (f := φ.toMonoidHom)
      (Subgroup.normalCore_le (sSup {N : Subgroup G | N.Normal ∧ Odd (Nat.card N)}))).trans
    (le_of_eq hmap)

/-! ## The remaining `oddCore` facts -/

/-- `O(G)` has odd order. -/
theorem oddCore_odd (G : Type*) [Group G] [Finite G] : Odd (Nat.card (oddCore G)) := by
  rw [oddCore_eq_oPiCore (G := G)]
  exact (odd_iff_isPiSubgroup_ne_two
      (OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2}) G)).mpr
    (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup (G := G) ({q : ℕ | q ≠ 2}))

/-- Maximality of `O(G)`: every normal odd-order subgroup lies in it. -/
theorem le_oddCore_of_odd_normal {G : Type*} [Group G] {N : Subgroup G} (hNn : N.Normal)
    (hN : Odd (Nat.card N)) : N ≤ oddCore G := by
  have hNn' : N.Normal := hNn
  exact Subgroup.normal_le_normalCore.mpr (le_sSup ⟨hNn, hN⟩)

/-- If `|G|` is odd then `O(G) = ⊤`. -/
theorem eq_top_of_odd {G : Type*} [Group G] (h : Odd (Nat.card G)) : oddCore G = ⊤ := by
  refine top_le_iff.mp ?_
  have htop : Odd (Nat.card (⊤ : Subgroup G)) := by rwa [Subgroup.card_top]
  exact le_oddCore_of_odd_normal (N := ⊤) inferInstance htop

/-- `O(K) ≤ O(G)` for `K ⊴ G`: `O(K) = O(G) ⊓ K` is a normal odd-order subgroup of `G`. -/
theorem oddCore_map_subtype_le (G : Type*) [Group G] [Finite G] (K : Subgroup G)
    (hK : K.Normal) : Subgroup.map K.subtype (oddCore ↥K) ≤ oddCore G := by
  have hK' : K.Normal := hK
  refine le_oddCore_of_odd_normal (N := Subgroup.map K.subtype (oddCore ↥K)) inferInstance ?_
  rw [Subgroup.card_subtype]
  exact oddCore_odd ↥K

/-- `O(G/O(G)) = 1`. -/
theorem oddCore_quotient_self (G : Type*) [Group G] [Finite G] :
    oddCore (G ⧸ oddCore G) = ⊥ := by
  have h : OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2})
      (G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2}) G) = ⊥ :=
    OddOrder.Isaacs.Ch03.oPiCore_quotient_self_eq_bot (G := G) ({q : ℕ | q ≠ 2})
  have h1 : oddCore G = OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2}) G :=
    oddCore_eq_oPiCore
  have e : G ⧸ oddCore G ≃* G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2}) G :=
    QuotientGroup.quotientMulEquivOfEq h1
  have hmap : (OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2}) (G ⧸ oddCore G)).map
      (e : G ⧸ oddCore G →* G ⧸ OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2}) G) = ⊥ :=
    (OddOrder.Isaacs.Ch03.oPiCore.map_eq_of_mulEquiv ({q : ℕ | q ≠ 2}) e).trans h
  have hKbar : OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2}) (G ⧸ oddCore G) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective
      (OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2}) (G ⧸ oddCore G)) e.injective).mp hmap
  have hQ : oddCore (G ⧸ oddCore G)
      = OddOrder.Isaacs.Ch03.oPiCore ({q : ℕ | q ≠ 2}) (G ⧸ oddCore G) :=
    oddCore_eq_oPiCore
  rw [hQ]
  exact hKbar

/-- `|G/O(G)| < |G|` when `O(G) ≠ 1`. -/
theorem card_quotient_oddCore_lt (G : Type*) [Group G] [Finite G] (hne : oddCore G ≠ ⊥) :
    Nat.card (G ⧸ oddCore G) < Nat.card G := by
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (oddCore G)
  have h2 : 1 < Nat.card (oddCore G) :=
    (Subgroup.one_lt_card_iff_ne_bot (oddCore G)).mpr hne
  have hpos : 0 < Nat.card (G ⧸ oddCore G) := Nat.card_pos
  rw [hcard]
  have hlt := Nat.mul_lt_mul_of_pos_left h2 hpos
  rwa [Nat.mul_one] at hlt

end Work.RED.GW2

namespace Work.RED

theorem OddCoreFacts : Work.RED.GW2.OddCoreFactsProp := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro G _
    exact Work.RED.GW2.oddCore_characteristic G
  · intro G _ _
    exact Work.RED.GW2.oddCore_odd G
  · intro G _ N hN hodd
    exact Work.RED.GW2.le_oddCore_of_odd_normal (G := G) (N := N) hN hodd
  · intro G _ h
    exact Work.RED.GW2.eq_top_of_odd (G := G) h
  · intro G _ _ K hK
    exact Work.RED.GW2.oddCore_map_subtype_le G K hK
  · intro G _ _
    exact Work.RED.GW2.oddCore_quotient_self G
  · intro G _ _ hne
    exact Work.RED.GW2.card_quotient_oddCore_lt G hne

end Work.RED

