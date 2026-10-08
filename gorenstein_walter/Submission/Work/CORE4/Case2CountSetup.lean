/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4)

# AREA CORE4 — `Case2Count`: setup of Bender's §4 configuration

This module collects the elementary structural facts about the §4 configuration `Case2Ctx B`
(Bender 1981, §4, pp. 224–228) that the counting argument of `Work.CORE4.Case2Count` needs
before any of Bender's numbered steps (7)–(12):

* `oddCore_odd` — `O(X)` has odd order.  Proved here elementarily (the join of two normal
  odd-order subgroups is odd, and the family is directed), so that CORE4 does not have to
  import the odd-order library;
* the basic facts about `S`, `S₀`, `t`, `H = C_G(t)`, `U = O(H)` (Bender p. 219):
  `t` is central in `S`, hence `S ≤ H`; `U ⊴ H`, `U ≤ H`, `U` odd, `U ⊓ S = ⊥`;
* `S ≤ M` and `S ≅ D_n` (`n ≥ 2`) for the §4 objects, using §4 (9) (`Case2Ctx.nine`) and the
  L₂(q)-Sylow input `I.toolkit.l2syl`;
* `H = U · S` (Bender p. 219, "`H` is `SU`"), from `I.toolkit.split`, hence
  `M ⊓ H = (U ⊓ M) · S` and the two index identities
  `|H : U| = |S|`, `|M ⊓ H : U ⊓ M| = |S|` and therefore (Bender's step (10))
  `|H : H ⊓ M| = |U : U ⊓ M|`.

Everything here is proved; the counting itself is the leaf `Work.CORE4.Case2Count`.
-/
import Mathlib
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.API
import Submission.Work.CORE4.CountSetup

open scoped MatrixGroups

namespace Work.CORE4

open Subgroup

/-! ## 0. `O(X)` has odd order

The join of two normal subgroups of odd order has odd order, because
`|A ⊔ B| = |A| · |B : A ⊓ B|` and `|B : A ⊓ B|` divides `|B|`.  The odd core is the normal
core of the join of the family of all normal odd-order subgroups, which is directed, so every
element of the join lies in a member of the family and therefore has odd order. -/

/-- The join of two normal subgroups of odd order has odd order. -/
theorem oddCard_sup_of_odd {G : Type} [Group G] [Finite G] (A B : Subgroup G) (hA : A.Normal)
    (hAo : Odd (Nat.card ↥A)) (hBo : Odd (Nat.card ↥B)) : Odd (Nat.card ↥(A ⊔ B)) := by
  haveI := hA
  have h1 : A.relIndex B ∣ Nat.card ↥B := Subgroup.relIndex_dvd_card A B
  have h2 : Odd (A.relIndex B) := Odd.of_dvd_nat hBo h1
  have h3 : Nat.card ↥(A ⊔ B) = A.relIndex B * Nat.card ↥A := by
    have h := Subgroup.relIndex_mul_card A (A ⊔ B)
    rw [inf_eq_left.mpr le_sup_left, Subgroup.relIndex_sup_left (H := B) (K := A)] at h
    exact h.symm
  rw [h3]
  exact h2.mul hAo

/-- `O(X)`, the largest normal subgroup of odd order, has odd order. -/
theorem oddCore_odd (X : Type) [Group X] [Finite X] :
    Odd (Nat.card ↥(Work.GW2.oddCore X)) := by
  set KK : Set (Subgroup X) := {N | N.Normal ∧ Odd (Nat.card ↥N)} with hKK
  have hne : KK.Nonempty := ⟨⊥, Subgroup.normal_bot, by simp⟩
  have hdir : DirectedOn (· ≤ ·) KK := by
    intro N hN K hK
    refine ⟨N ⊔ K, ⟨?_, ?_⟩, le_sup_left, le_sup_right⟩
    · haveI := hN.1; haveI := hK.1; exact inferInstance
    · exact oddCard_sup_of_odd N K hN.1 hN.2 hK.2
  have hodd_elt : ∀ g : ↥(sSup KK), Odd (orderOf g) := by
    intro g
    obtain ⟨N, hN, hxN⟩ := (Subgroup.mem_sSup_of_directedOn hne hdir).mp g.2
    rw [Subgroup.orderOf_mk]
    exact Odd.of_dvd_nat hN.2 (Subgroup.orderOf_dvd_natCard N hxN)
  have hodd_T : Odd (Nat.card ↥(sSup KK)) := by
    by_contra hcon
    have h2 : 2 ∣ Nat.card ↥(sSup KK) := by
      rw [← even_iff_two_dvd, ← Nat.not_odd_iff_even]
      exact hcon
    obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := ↥(sSup KK)) 2 h2
    exact absurd (hodd_elt g) (by rw [hg]; decide)
  exact Odd.of_dvd_nat hodd_T (Subgroup.card_dvd_of_le (Subgroup.normalCore_le _))

/-! ## 0'. `relIndex` calculus for the second isomorphism theorem -/

/-- Second isomorphism theorem in `relIndex` form: if `A ⊴ C`, `B ≤ C` and `A ⊔ B = ⊤`, then
`|C : A| = |B : B ⊓ A|`. -/
theorem relIndex_top_eq_relIndex_inf {C : Type*} [Group C] (A B : Subgroup C) [A.Normal]
    (h : A ⊔ B = ⊤) : A.relIndex ⊤ = (A ⊓ B).relIndex B := by
  have h1 : A.relIndex (A ⊔ B) = A.relIndex B := Subgroup.relIndex_sup_left (H := B) (K := A)
  rw [h] at h1
  rw [h1]
  exact (Subgroup.inf_relIndex_right A B).symm

/-- If moreover `A ⊓ B = ⊥`, then `|C : A| = |B|`. -/
theorem relIndex_eq_card_of_sup_eq_top_inf_eq_bot {C : Type*} [Group C] (A B : Subgroup C)
    [A.Normal] (hsup : A ⊔ B = ⊤) (hinf : A ⊓ B = ⊥) : A.relIndex ⊤ = Nat.card ↥B := by
  rw [relIndex_top_eq_relIndex_inf A B hsup, hinf, Subgroup.relIndex_bot_left]

/-- **Second isomorphism theorem, `relIndex` form, dual orientation.**  If `A ⊴ C`,
`B ≤ C` and `A ⊔ B = C`, then `|C : B| = |A : A ⊓ B|` (as well as `|C : A| = |B : B ⊓ A|`,
which is `relIndex_top_eq_relIndex_inf`). -/
theorem relIndex_eq_relIndex_inf_of_normal_sup_eq_top {C : Type*} [Group C] [Finite C]
    (A B : Subgroup C) [A.Normal] (h : A ⊔ B = ⊤) : B.relIndex ⊤ = (A ⊓ B).relIndex A := by
  have h1 : (A ⊓ B).relIndex A * A.relIndex ⊤ = (A ⊓ B).relIndex ⊤ :=
    Subgroup.relIndex_mul_relIndex (H := A ⊓ B) (K := A) (L := ⊤) inf_le_left le_top
  have h2 : A.relIndex ⊤ = (A ⊓ B).relIndex B := relIndex_top_eq_relIndex_inf A B h
  have h3 : (A ⊓ B).relIndex B * B.relIndex ⊤ = (A ⊓ B).relIndex ⊤ :=
    Subgroup.relIndex_mul_relIndex (H := A ⊓ B) (K := B) (L := ⊤) inf_le_right le_top
  have hpos : 0 < (A ⊓ B).relIndex B := by
    refine Nat.pos_iff_ne_zero.mpr (fun h6 => ?_)
    have h4 := Subgroup.relIndex_mul_card (A ⊓ B) B
    rw [h6, zero_mul] at h4
    exact Nat.card_pos.ne' h4.symm
  have hkey : (A ⊓ B).relIndex A * (A ⊓ B).relIndex B =
      (A ⊓ B).relIndex B * B.relIndex ⊤ := by
    calc (A ⊓ B).relIndex A * (A ⊓ B).relIndex B
        = (A ⊓ B).relIndex A * A.relIndex ⊤ := by rw [h2]
      _ = (A ⊓ B).relIndex ⊤ := h1
      _ = (A ⊓ B).relIndex B * B.relIndex ⊤ := h3.symm
  rw [mul_comm ((A ⊓ B).relIndex A)] at hkey
  exact (Nat.eq_of_mul_eq_mul_left hpos hkey).symm

/-- **Second isomorphism theorem, subgroup form.**  If `A ≤ C`, `B ≤ C`, `A ⊔ B = C`,
`A ⊓ B = ⊥` and `A ⊴ C`, then `|C : A| = |B|`. -/
theorem relIndex_eq_card_of_sup_eq_inf_eq_bot {G : Type} [Group G] (A B C : Subgroup G)
    (hAC : A ≤ C) (hBC : B ≤ C) (hsup : A ⊔ B = C) (hinf : A ⊓ B = ⊥)
    (hnorm : (A.subgroupOf C).Normal) : A.relIndex C = Nat.card ↥B := by
  have hsup' : (A.subgroupOf C) ⊔ (B.subgroupOf C) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAC hBC, hsup, Subgroup.subgroupOf_self]
  have hinf' : (A.subgroupOf C) ⊓ (B.subgroupOf C) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hx
    have hxG : (x : G) ∈ A ⊓ B := Subgroup.mem_inf.mpr hx
    rw [hinf] at hxG
    exact Subtype.ext (Subgroup.mem_bot.mp hxG)
  haveI := hnorm
  have hmain := relIndex_eq_card_of_sup_eq_top_inf_eq_bot (C := ↥C) (A.subgroupOf C)
    (B.subgroupOf C) hsup' hinf'
  have hcard : Nat.card ↥(B.subgroupOf C) = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv
  rw [hcard] at hmain
  have hkey : (A.subgroupOf C).relIndex ⊤ = A.relIndex C := by
    rw [← Subgroup.subgroupOf_self C]
    exact Subgroup.relIndex_subgroupOf (H := A) (K := C) (L := C) le_rfl
  rw [hkey] at hmain
  exact hmain

/-- `(A.subgroupOf C) ⊓ (B.subgroupOf C) = (A ⊓ B).subgroupOf C`. -/
theorem inf_subgroupOf {G : Type*} [Group G] (A B C : Subgroup G) :
    A.subgroupOf C ⊓ B.subgroupOf C = (A ⊓ B).subgroupOf C := by
  ext x
  simp [Subgroup.mem_subgroupOf, Subgroup.mem_inf]

/-- **Second isomorphism theorem, subgroup form, dual orientation.**  If `A ≤ C`, `B ≤ C`,
`A ⊔ B = C` and `A ⊴ C`, then `|C : B| = |A : A ⊓ B|`. -/
theorem relIndex_eq_relIndex_inf_of_normal_sup_eq {G : Type} [Group G] [Finite G]
    (A B C : Subgroup G) (hAC : A ≤ C) (hBC : B ≤ C) (hsup : A ⊔ B = C)
    (hnorm : (A.subgroupOf C).Normal) : B.relIndex C = (A ⊓ B).relIndex A := by
  have hsup' : (A.subgroupOf C) ⊔ (B.subgroupOf C) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAC hBC, hsup, Subgroup.subgroupOf_self]
  haveI := hnorm
  have hmain := relIndex_eq_relIndex_inf_of_normal_sup_eq_top (C := ↥C) (A.subgroupOf C)
    (B.subgroupOf C) hsup'
  rw [inf_subgroupOf] at hmain
  have hkey : (B.subgroupOf C).relIndex ⊤ = B.relIndex C := by
    rw [← Subgroup.subgroupOf_self C]
    exact Subgroup.relIndex_subgroupOf (H := B) (K := C) (L := C) le_rfl
  rw [hkey] at hmain
  have hkey2 : ((A ⊓ B).subgroupOf C).relIndex (A.subgroupOf C) = (A ⊓ B).relIndex A :=
    Subgroup.relIndex_subgroupOf (H := A ⊓ B) (K := A) (L := C) hAC
  rw [hkey2] at hmain
  exact hmain

end Work.CORE4

namespace Work.GW2

open Subgroup

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Bender's setup: `S`, `S₀`, `t`, `H`, `U` (Bender p. 219) -/

/-- A cyclic group has at most one element of order two. -/
theorem eq_orderOf_eq_two_of_isCyclic {H : Type*} [Group H] [Finite H] [IsCyclic H]
    {a b : H} (ha : orderOf a = 2) (hb : orderOf b = 2) : a = b := by
  classical
  haveI := Fintype.ofFinite H
  have hd : 2 ∣ Fintype.card H := by
    rw [← Nat.card_eq_fintype_card, ← ha]
    exact orderOf_dvd_natCard a
  have hcard : Fintype.card {x : H // orderOf x = 2} = 1 := by
    rw [Fintype.card_subtype, IsCyclic.card_orderOf_eq_totient (α := H) hd, Nat.totient_two]
  exact Subtype.ext_iff.mp (Fintype.card_le_one_iff.mp (le_of_eq hcard) ⟨a, ha⟩ ⟨b, hb⟩)

namespace BenderSetup

/-- The involution `t` of the cyclic group `S₀` is central in `S` (`S/S₀` acts on the cyclic
group `S₀`, which has a unique element of order two). -/
theorem t_central (B : BenderSetup G) : ∀ x ∈ (B.S : Subgroup G), x * B.t = B.t * x := by
  intro x hxS
  by_cases hx0 : x ∈ B.S0
  · haveI : IsCyclic ↥B.S0 := B.S0_cyclic
    exact congrArg Subtype.val (mul_comm' (⟨x, hx0⟩ : ↥B.S0) ⟨B.t, B.t_mem⟩)
  · have hnorm : (B.S0.subgroupOf (B.S : Subgroup G)).Normal := by
      refine Subgroup.normal_of_index_eq_two ?_
      simpa [Subgroup.relIndex] using B.S0_index
    have hmem : x * B.t * x⁻¹ ∈ B.S0 := by
      have hcm := hnorm.conj_mem (⟨B.t, B.S0_le B.t_mem⟩ : ↥(B.S : Subgroup G))
        (by rw [Subgroup.mem_subgroupOf]; exact B.t_mem) (⟨x, hxS⟩ : ↥(B.S : Subgroup G))
      rw [Subgroup.mem_subgroupOf] at hcm
      exact hcm
    have hord : orderOf (x * B.t * x⁻¹) = 2 := by
      have hsemi : SemiconjBy x B.t (x * B.t * x⁻¹) := by simp [SemiconjBy, mul_assoc]
      exact (SemiconjBy.orderOf_eq x hsemi).symm.trans B.t_order
    have h1 : x * B.t * x⁻¹ = B.t := by
      haveI : IsCyclic ↥B.S0 := B.S0_cyclic
      have h2 : (⟨x * B.t * x⁻¹, hmem⟩ : ↥B.S0) = ⟨B.t, B.t_mem⟩ := by
        apply eq_orderOf_eq_two_of_isCyclic
        · rw [Subgroup.orderOf_mk]; exact hord
        · rw [Subgroup.orderOf_mk]; exact B.t_order
      exact congrArg Subtype.val h2
    have h2 : (x * B.t * x⁻¹) * x = B.t * x := congrArg (· * x) h1
    simpa [mul_assoc] using h2

/-- **Bender p. 219**: `S ≤ C_G(t) = H`. -/
theorem S_le_H (B : BenderSetup G) : (B.S : Subgroup G) ≤ B.H := by
  intro x hx
  rw [show B.H = centralizer ({B.t} : Set G) from rfl, Subgroup.mem_centralizer_iff]
  intro y hy
  rw [Set.mem_singleton_iff] at hy
  subst hy
  exact (B.t_central x hx).symm

theorem S_le_Hhat (B : BenderSetup G) : (B.S : Subgroup G) ≤ B.Hhat :=
  le_trans B.S_le_H B.H_le_Hhat

theorem t_mem_S (B : BenderSetup G) : B.t ∈ (B.S : Subgroup G) := B.S0_le B.t_mem

/-- `U = O(H) ≤ H`. -/
theorem U_le_H (B : BenderSetup G) : B.U ≤ B.H := Subgroup.map_subtype_le _

/-- `U = O(H)` has odd order. -/
theorem U_odd (B : BenderSetup G) : Odd (Nat.card ↥B.U) := by
  have h := Work.CORE4.oddCore_odd ↥B.H
  have hcard : Nat.card ↥B.U = Nat.card ↥(oddCore ↥B.H) :=
    Subgroup.card_map_of_injective (Subtype.val_injective)
  rw [hcard]
  exact h

/-- `U = O(H) ⊴ H`. -/
theorem U_normal (B : BenderSetup G) : (B.U.subgroupOf B.H).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (H := B.U) (K := B.H) B.U_le_H]
  intro h k hh hk
  obtain ⟨u, hu, rfl⟩ := hh
  exact ⟨⟨k, hk⟩ * u * ⟨k, hk⟩⁻¹, (oddCore_normal ↥B.H).conj_mem u hu ⟨k, hk⟩,
    by simp [map_mul]⟩

/-- `U = O(H)` and `S` intersect trivially: `U` has odd order and `S` is a 2-group. -/
theorem U_inf_S (B : BenderSetup G) : B.U ⊓ (B.S : Subgroup G) = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxU, hxS⟩ := Subgroup.mem_inf.mp hx
  have h1 : orderOf x ∣ Nat.card ↥B.U := Subgroup.orderOf_dvd_natCard B.U hxU
  have hodd : Odd (orderOf x) := Odd.of_dvd_nat B.U_odd h1
  obtain ⟨n, hn⟩ := (B.S).isPGroup' (⟨x, hxS⟩ : ↥(B.S : Subgroup G))
  have hdvd : orderOf x ∣ 2 ^ n :=
    orderOf_dvd_iff_pow_eq_one.mpr (by simpa using hn)
  obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hk0 : k = 0 := by
    rcases Nat.eq_zero_or_pos k with h | h
    · exact h
    · exfalso
      exact (Nat.not_even_iff_odd.mpr (hk' ▸ hodd))
        (even_iff_two_dvd.mpr (dvd_pow_self 2 (Nat.pos_iff_ne_zero.mp h)))
  exact orderOf_eq_one_iff.mp (by rw [hk', hk0, pow_zero])

end BenderSetup

/-! ## 2. The §4 configuration: `S` is dihedral, `H = U · S`, `M ⊓ H = (U ⊓ M) · S` -/

namespace Case2Ctx

/-- `S ≤ M` for the §4 objects, because `S ≤ E(M) ≤ M`. -/
theorem S_le_M {B : BenderSetup G} (h : Case2Ctx B) : (B.S : Subgroup G) ≤ h.D.M := by
  obtain ⟨p, k, hp, hpodd, h7, hiso, hSE⟩ := h.nine
  exact le_trans hSE (Work.CORE4.layerIn_le h.D.M)

/-- §4 (9) plus `I.toolkit.l2syl`: `S` is a Sylow 2-subgroup of `E(M) ≅ L₂(q)`, hence dihedral
(`S ≃* DihedralGroup n` with `n ≥ 2`). -/
theorem sylow_dihedral (I : C4Inputs) {B : BenderSetup G} (h : Case2Ctx B) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
  obtain ⟨p, k, hp, hpodd, h7, hiso, hSE⟩ := h.nine
  haveI := hp
  obtain ⟨φ⟩ := hiso
  let Q : Sylow 2 ↥(layerIn h.D.M) := (B.S).subtype hSE
  have hcoe : (Q : Subgroup ↥(layerIn h.D.M)) = (B.S : Subgroup G).subgroupOf (layerIn h.D.M) :=
    Sylow.coe_subtype _ _
  let Q' : Sylow 2 (PSL(2, GaloisField p k)) :=
    Sylow.mapSurjective (f := (φ : ↥(layerIn h.D.M) →* PSL(2, GaloisField p k))) φ.surjective Q
  have hQ' : (Q' : Subgroup (PSL(2, GaloisField p k))) =
      ((B.S : Subgroup G).subgroupOf (layerIn h.D.M)).map
        (φ : ↥(layerIn h.D.M) →* PSL(2, GaloisField p k)) := by
    rw [Sylow.coe_mapSurjective, hcoe]
  obtain ⟨n, hn2, ⟨e⟩⟩ := I.toolkit.l2syl p k hpodd (by omega) Q'
  refine ⟨n, hn2, ⟨?e1⟩⟩
  exact (Subgroup.subgroupOfEquivOfLe hSE).symm |>.trans
    (Subgroup.equivMapOfInjective ((B.S : Subgroup G).subgroupOf (layerIn h.D.M))
      (φ : ↥(layerIn h.D.M) →* PSL(2, GaloisField p k)) φ.injective) |>.trans
    (MulEquiv.subgroupCongr hQ') |>.trans e

/-- `H = U · S` — Bender p. 219, "`H` is `SU`" (from the input `I.toolkit.split`). -/
theorem H_eq_U_sup_S (I : C4Inputs) {B : BenderSetup G} (h : Case2Ctx B) :
    B.H = B.U ⊔ (B.S : Subgroup G) := by
  obtain ⟨n, hn2, ⟨e⟩⟩ := h.sylow_dihedral I
  exact (I.toolkit.split G B.S n hn2 ⟨e⟩ B.t B.t_mem_S B.t_order B.t_central).symm

/-- `H ⊓ M = (U ⊓ M) · S`. -/
theorem inter_H_M (I : C4Inputs) {B : BenderSetup G} (h : Case2Ctx B) :
    h.D.M ⊓ B.H = (B.U ⊓ h.D.M) ⊔ (B.S : Subgroup G) := by
  have hH := h.H_eq_U_sup_S I
  refine le_antisymm ?_ ?_
  · intro x hx
    obtain ⟨hxM, hxH⟩ := Subgroup.mem_inf.mp hx
    have htop : (B.U.subgroupOf B.H) ⊔ ((B.S : Subgroup G).subgroupOf B.H) = ⊤ := by
      rw [← Subgroup.subgroupOf_sup B.U_le_H B.S_le_H, ← hH, Subgroup.subgroupOf_self]
    have hxH' : (⟨x, hxH⟩ : ↥B.H) ∈
        (B.U.subgroupOf B.H) ⊔ ((B.S : Subgroup G).subgroupOf B.H) := by
      rw [htop]; exact Subgroup.mem_top _
    haveI : (B.U.subgroupOf B.H).Normal := B.U_normal
    obtain ⟨u, hu, s, hs, hus⟩ := Subgroup.mem_sup_of_normal_left.mp hxH'
    have huU : (u : G) ∈ B.U := Subgroup.mem_subgroupOf.mp hu
    have hsS : (s : G) ∈ (B.S : Subgroup G) := Subgroup.mem_subgroupOf.mp hs
    have hxs : (u : G) * (s : G) = x := by
      have hh := congrArg (Subtype.val) hus
      simpa using hh
    have huM : (u : G) ∈ h.D.M := by
      have h2 : (u : G) = x * (s : G)⁻¹ := by rw [← hxs]; group
      rw [h2]
      exact h.D.M.mul_mem hxM (h.D.M.inv_mem (h.S_le_M hsS))
    rw [← hxs]
    exact Subgroup.mul_mem_sup (Subgroup.mem_inf.mpr ⟨huU, huM⟩) hsS
  · refine sup_le ?_ ?_
    · exact le_inf inf_le_right (le_trans inf_le_left B.U_le_H)
    · exact le_inf h.S_le_M B.S_le_H

/-- `U ⊓ M ⊴ M ⊓ H` (because `U ⊴ H`). -/
theorem U_inf_M_normal {B : BenderSetup G} (h : Case2Ctx B) :
    ((B.U ⊓ h.D.M).subgroupOf (h.D.M ⊓ B.H)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff (le_inf inf_le_right (le_trans inf_le_left B.U_le_H))]
  intro a b ha hb
  obtain ⟨haU, haM⟩ := Subgroup.mem_inf.mp ha
  obtain ⟨hbM, hbH⟩ := Subgroup.mem_inf.mp hb
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal a b haU hbH
  · exact h.D.M.mul_mem (h.D.M.mul_mem hbM haM) (h.D.M.inv_mem hbM)

/-- `|H : U| = |S|`. -/
theorem relIndex_U_H (I : C4Inputs) {B : BenderSetup G} (h : Case2Ctx B) :
    (B.U).relIndex B.H = Nat.card ↥(B.S : Subgroup G) :=
  Work.CORE4.relIndex_eq_card_of_sup_eq_inf_eq_bot B.U B.S B.H B.U_le_H B.S_le_H
    (h.H_eq_U_sup_S I).symm B.U_inf_S B.U_normal

/-- `|M ⊓ H : U ⊓ M| = |S|`. -/
theorem relIndex_inter_MH_inter_UM (I : C4Inputs) {B : BenderSetup G} (h : Case2Ctx B) :
    (B.U ⊓ h.D.M).relIndex (h.D.M ⊓ B.H) = Nat.card ↥(B.S : Subgroup G) := by
  refine Work.CORE4.relIndex_eq_card_of_sup_eq_inf_eq_bot (B.U ⊓ h.D.M) (B.S : Subgroup G)
    (h.D.M ⊓ B.H) ?_ ?_ (h.inter_H_M I).symm ?_ h.U_inf_M_normal
  · exact le_inf inf_le_right (le_trans inf_le_left B.U_le_H)
  · exact le_inf h.S_le_M B.S_le_H
  · rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hx1, hx2⟩ := Subgroup.mem_inf.mp hx
    have hxU : x ∈ B.U ⊓ (B.S : Subgroup G) :=
      Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx1).1, hx2⟩
    rw [B.U_inf_S] at hxU
    exact Subgroup.mem_bot.mp hxU

/-- `|H : H ⊓ M| = |U : U ⊓ M|` (Bender §4, used in step (10)). -/
theorem relIndex_H_inter_M (I : C4Inputs) {B : BenderSetup G} (h : Case2Ctx B) :
    (h.D.M ⊓ B.H).relIndex B.H = (B.U ⊓ h.D.M).relIndex B.U := by
  have h1 : (B.U ⊓ h.D.M).relIndex (h.D.M ⊓ B.H) * (h.D.M ⊓ B.H).relIndex B.H =
      (B.U ⊓ h.D.M).relIndex B.H :=
    Subgroup.relIndex_mul_relIndex (H := B.U ⊓ h.D.M) (K := h.D.M ⊓ B.H) (L := B.H)
      (le_inf inf_le_right (le_trans inf_le_left B.U_le_H)) inf_le_right
  have h2 : (B.U ⊓ h.D.M).relIndex B.U * (B.U).relIndex B.H =
      (B.U ⊓ h.D.M).relIndex B.H :=
    Subgroup.relIndex_mul_relIndex (H := B.U ⊓ h.D.M) (K := B.U) (L := B.H)
      inf_le_left B.U_le_H
  rw [h.relIndex_inter_MH_inter_UM I] at h1
  rw [h.relIndex_U_H I] at h2
  have hS : 0 < Nat.card ↥(B.S : Subgroup G) := Nat.card_pos
  have hcomm : (h.D.M ⊓ B.H).relIndex B.H * Nat.card ↥(B.S : Subgroup G) =
      (B.U ⊓ h.D.M).relIndex B.U * Nat.card ↥(B.S : Subgroup G) := by
    rw [mul_comm ((h.D.M ⊓ B.H).relIndex B.H)]
    exact h1.trans h2.symm
  exact Nat.eq_of_mul_eq_mul_right hS hcomm

/-- `E(M) = layerIn M`, viewed inside `↥M`, is the layer of `M`, hence normal. -/
theorem layerIn_subgroupOf_normal {B : BenderSetup G} (h : Case2Ctx B) :
    ((layerIn h.D.M).subgroupOf h.D.M).Normal := by
  have h1 : (layerIn h.D.M).subgroupOf h.D.M = layer ↥h.D.M := by
    rw [← Subgroup.comap_subtype (layerIn h.D.M) h.D.M]
    exact Subgroup.comap_map_eq_self_of_injective (Subtype.val_injective) _
  rw [h1]
  exact Work.CORE4.layer_normal h.D.M

/-- `|M : M ⊓ H| = |E(M) : E(M) ⊓ H|`, i.e. `= |E : C_E(t)|` (Bender §4: this number is
`q k'`).  This is the second isomorphism theorem for `M = E(M) · (M ⊓ H)`. -/
theorem relIndex_M_inter_H (hbc : BenderCtx G) {B : BenderSetup G} (h : Case2Ctx B) :
    (h.D.M ⊓ B.H).relIndex h.D.M =
      (layerIn h.D.M ⊓ B.H).relIndex (layerIn h.D.M) := by
  have hkey := Work.CORE4.relIndex_eq_relIndex_inf_of_normal_sup_eq (layerIn h.D.M)
    (h.D.M ⊓ B.H) h.D.M (Work.CORE4.layerIn_le h.D.M) inf_le_left
    (Work.CORE4.M_eq_layerIn_sup hbc h).symm h.layerIn_subgroupOf_normal
  rwa [show layerIn h.D.M ⊓ (h.D.M ⊓ B.H) = layerIn h.D.M ⊓ B.H from by
    rw [← inf_assoc, inf_eq_left.mpr (Work.CORE4.layerIn_le h.D.M)]] at hkey

end Case2Ctx

end Work.GW2
