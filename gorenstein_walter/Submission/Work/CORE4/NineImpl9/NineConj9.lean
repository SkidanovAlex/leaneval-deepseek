/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4.NineImpl9`)

# `Work.CORE4.NineImpl9.NineConj9`

Bender 1981, §4, step (9), the conjugacy step N5c:

> since `8` divides `|C_G(tr)|`, `r = t^y` for some `y ∈ C_G(tr)`.

Given the input `DihFourConjProp` (the pure group-theoretic leaf: in a group with dihedral Sylow
`2`-subgroups of order `≥ 8` and one class of involutions, an involution `r ≠ t` of `S` is
`C_G(tr)`-conjugate to the central involution `t`), the present lemma shows that the hypotheses
`Hyp9` of step (9) supply exactly the inputs needed to apply it:

* `S = B.S` is not cyclic (`t` and `r` are distinct elements of order `2` in it), hence dihedral
  (`BenderCtx.sylow`), say `S ≅ DihedralGroup n` with `|S| = 2n`;
* `|S| ≥ 8`, i.e. `n ≥ 4`: the hypotheses `Case2PrePlus` make `S ⊓ M` a Sylow `2`-subgroup of `M`
  (its index in `M` is odd), so `S ⊓ E` (`E = E(M) = layerIn M`) is a Sylow `2`-subgroup of `E`;
  the shape of `E/Z(E)` (`LayerCtx6`) is `A₇` or `PSL(2,q)`, whose Sylow `2`-subgroups have order
  `≥ 4`, so `4 ∣ |E|` and hence `4 ∣ |S ⊓ E|`; and `S ⊓ E < S` because `r ∈ S ∖ E`.  Thus
  `|S| ≥ 2 · 4 = 8`;
* one class of involutions in `G` is `I.toolkit.fus` applied to `S` (`2 ≤ n`, and `G` simple
  non-abelian has no normal subgroup of index `2`).

The conclusion is then exactly `DihFourConjProp` instantiated at `(G, B.S, n, B.t, r)`.
-/
import Mathlib
import Submission.Work.CORE4.Defs10
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2CountSetup
import Submission.Work.CORE4.LayerCtx6
import Submission.Work.CORE4.DihOrCycSub

namespace Work.CORE4.NineImpl9

open Subgroup

/-! ## 0. Two elementary lemmas about `relIndex` -/

/-- Second isomorphism theorem in `relIndex` form, under normality: if `E ⊴ M` and `P ≤ M`, then
`|E : P ⊓ E| = |M : ...|` computed as `P.relIndex (P ⊔ E)`. -/
theorem relIndex_inf_eq_of_normal {G : Type} [Group G] [Finite G] (M E P : Subgroup G)
    (hEM : E ≤ M) (hPM : P ≤ M) (hnorm : (E.subgroupOf M).Normal) :
    (P ⊓ E).relIndex E = P.relIndex (P ⊔ E) := by
  have h1 : ((P ⊓ E).subgroupOf M).relIndex (E.subgroupOf M) = (P ⊓ E).relIndex E :=
    Subgroup.relIndex_subgroupOf (H := P ⊓ E) (K := E) (L := M) hEM
  have h2 : ((P ⊓ E).subgroupOf M) = (E.subgroupOf M) ⊓ (P.subgroupOf M) := by
    rw [Work.CORE4.inf_subgroupOf E P M, inf_comm E P]
  have h3 : (E.subgroupOf M) ⊔ (P.subgroupOf M) = (P ⊔ E).subgroupOf M := by
    rw [sup_comm, Subgroup.subgroupOf_sup hPM hEM]
  have h4 := Work.CORE4.relIndex_eq_relIndex_inf_of_normal_sup_eq (E.subgroupOf M)
    (P.subgroupOf M) ((E.subgroupOf M) ⊔ (P.subgroupOf M)) le_sup_left le_sup_right rfl
    (hnorm.subgroupOf _)
  have h5 : (P.subgroupOf M).relIndex ((E.subgroupOf M) ⊔ (P.subgroupOf M)) =
      P.relIndex (P ⊔ E) := by
    rw [h3]
    exact Subgroup.relIndex_subgroupOf (H := P) (K := P ⊔ E) (L := M) (sup_le hPM hEM)
  rw [← h1, h2, ← h4, h5]

/-- If `P ≤ M` has odd index in `M` and `E ⊴ M`, then `P ⊓ E` has odd index in `E`.  (This is
"`P ⊓ E` is a Sylow `2`-subgroup of `E`" for the `2`-part, in index form.) -/
theorem odd_relIndex_inf_of_normal {G : Type} [Group G] [Finite G] (M E P : Subgroup G)
    (hEM : E ≤ M) (hPM : P ≤ M) (hnorm : (E.subgroupOf M).Normal)
    (hodd : Odd (P.relIndex M)) : Odd ((P ⊓ E).relIndex E) := by
  rw [relIndex_inf_eq_of_normal M E P hEM hPM hnorm]
  exact Odd.of_dvd_nat hodd ⟨(P ⊔ E).relIndex M,
    (Subgroup.relIndex_mul_relIndex P (P ⊔ E) M le_sup_left (sup_le hPM hEM)).symm⟩

/-- If `4 ∣ |E|` and `P ⊓ E` has odd index in `E`, then `4 ∣ |P ⊓ E|`. -/
theorem four_dvd_inf_of_odd_relIndex {G : Type} [Group G] [Finite G] (E P : Subgroup G)
    (h4 : 4 ∣ Nat.card ↥E) (hodd : Odd ((P ⊓ E).relIndex E)) :
    4 ∣ Nat.card ↥(P ⊓ E) := by
  have hcard : Nat.card ↥E = (P ⊓ E).relIndex E * Nat.card ↥(P ⊓ E) := by
    have h := Subgroup.relIndex_mul_card (P ⊓ E) E
    have h2 : (P ⊓ E) ⊓ E = P ⊓ E := by rw [inf_assoc, inf_idem]
    rw [h2] at h
    exact h.symm
  rw [hcard] at h4
  have hcop : Nat.Coprime 4 ((P ⊓ E).relIndex E) := by
    rw [Nat.coprime_comm]
    exact Nat.Coprime.pow_right 2 (hodd.coprime_two_right)
  exact Nat.Coprime.dvd_of_dvd_mul_left hcop h4

/-! ## 1. `4` divides the order of the layer of `M` -/

/-- In the §4 configuration, `E = E(M) = layerIn M` has `4 ∣ |E|`: by `LayerCtx6` the quotient
`E/Z(E)` is `A₇` (`|A₇| = 2520`) or `PSL(2,q)` (`q = p^k ≥ 5`, whose Sylow `2`-subgroups are
dihedral of order `≥ 4`), and `|E/Z(E)|` divides `|E|`. -/
theorem four_dvd_layerIn_card (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (hbc : Work.GW2.BenderCtx G) (C : Work.GW2.Case2Ctx6 B) :
    4 ∣ Nat.card ↥(Work.GW2.layerIn C.D.M) := by
  have hD : Work.GW2.DihOrCycSylow ↥C.D.M := Work.CORE4.DihOrCycSub hbc.sylow C.D.M
  obtain ⟨-, -, hshape⟩ := Work.CORE4.LayerCtx6 I hbc C hD
  have h4quot : 4 ∣ Nat.card (↥(Work.GW2.layerIn C.D.M) ⧸
      center ↥(Work.GW2.layerIn C.D.M)) := by
    rcases hshape with hA | hPSL
    · obtain ⟨e⟩ := hA
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num [Nat.factorial]
    · obtain ⟨p, k, hp, hpodd, h5, hiso⟩ := hPSL
      haveI : Fact p.Prime := hp
      obtain ⟨e⟩ := hiso
      obtain ⟨S⟩ := Sylow.nonempty (p := 2)
        (G := Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))
      obtain ⟨n, hn2, ⟨eS⟩⟩ := I.toolkit.l2syl p k hpodd h5 S
      have hcard : Nat.card ↥(S : Subgroup
          (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) = 2 * n := by
        rw [Nat.card_congr eS.toEquiv, DihedralGroup.nat_card]
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have h4S : 4 ∣ Nat.card ↥(S : Subgroup
          (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) := by
        obtain ⟨a, ha0⟩ := S.isPGroup'.exists_card_eq
        have ha : 2 * n = 2 ^ a := hcard.symm.trans ha0
        have ha2 : 2 ≤ a := by
          by_contra h
          have h1 : a = 0 ∨ a = 1 := by omega
          rcases h1 with h1 | h1
          · rw [h1, pow_zero] at ha
            omega
          · rw [h1, pow_one] at ha
            omega
        calc (4 : ℕ) = 2 ^ 2 := by norm_num
          _ ∣ 2 ^ a := Nat.pow_dvd_pow 2 ha2
          _ = Nat.card ↥(S : Subgroup
                (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k))) := ha0.symm
      have hdvd := Subgroup.card_subgroup_dvd_card (S : Subgroup
        (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p k)))
      rw [← Nat.card_congr e.toEquiv] at hdvd
      exact dvd_trans h4S hdvd
  exact dvd_trans h4quot
    (Subgroup.card_quotient_dvd_card (center ↥(Work.GW2.layerIn C.D.M)))

/-! ## 2. The main lemma -/

/-- **LEAF C10.N5c `NineConj`**: with `DihFourConjProp` as input, the hypotheses of step (9) give
`r = t^y` for some `y ∈ C_G(tr)`. -/
theorem NineConj9 (I : Work.GW2.C4Inputs) (h : Work.GW2.DihFourConjProp) :
    Work.GW2.NineConjProp I := by
  intro G _instG _instF B C hH hSE r hr hr2 hrE
  obtain ⟨hbc, _hc2, hpp, _hseven, _height⟩ := hH
  -- basic membership facts
  have hrS : r ∈ (B.S : Subgroup G) := (Subgroup.mem_inf.mp hr).1
  have hEM : Work.GW2.layerIn C.D.M ≤ C.D.M := Work.CORE4.layerIn_le C.D.M
  have htr : B.t ≠ r := fun hh => hrE (hh ▸ C.D.t_mem)
  -- `E = layerIn M` is normal in `M`
  have hnormE : ((Work.GW2.layerIn C.D.M).subgroupOf C.D.M).Normal := by
    have hEq : (Work.GW2.layerIn C.D.M).subgroupOf C.D.M = Work.GW2.layer ↥C.D.M := by
      rw [Work.GW2.layerIn]
      exact Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective C.D.M)
        (Work.GW2.layer ↥C.D.M)
    rw [hEq]
    exact Work.CORE4.layer_normal C.D.M
  -- `S` is not cyclic: it contains `t` and `r`, distinct involutions
  have hnotcyc : ¬ IsCyclic ↥(B.S : Subgroup G) := by
    intro hcyc
    haveI := hcyc
    have h1 : (⟨B.t, Work.GW2.BenderSetup.t_mem_S B⟩ : ↥(B.S : Subgroup G)) = ⟨r, hrS⟩ :=
      Work.GW2.eq_orderOf_eq_two_of_isCyclic
        (a := (⟨B.t, Work.GW2.BenderSetup.t_mem_S B⟩ : ↥(B.S : Subgroup G)))
        (b := ⟨r, hrS⟩)
        (by rw [Subgroup.orderOf_mk]; exact B.t_order)
        (by rw [Subgroup.orderOf_mk]; exact hr2)
    exact htr (congrArg Subtype.val h1)
  -- hence `S` is dihedral
  obtain ⟨n, hdih⟩ : ∃ n : ℕ, Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
    rcases hbc.sylow B.S with hcyc | ⟨n, hn⟩
    · exact absurd hcyc hnotcyc
    · exact ⟨n, hn⟩
  -- `S ⊓ M` has odd index in `M` (this is `Case2PrePlus`), so `S ⊓ E` has odd index in `E`
  have hoddP : Odd (((B.S : Subgroup G) ⊓ C.D.M).relIndex C.D.M) :=
    Nat.not_even_iff_odd.mp (fun he => hpp.1 (even_iff_two_dvd.mp he))
  have hoddE : Odd ((((B.S : Subgroup G) ⊓ C.D.M) ⊓ Work.GW2.layerIn C.D.M).relIndex
      (Work.GW2.layerIn C.D.M)) :=
    odd_relIndex_inf_of_normal C.D.M (Work.GW2.layerIn C.D.M) ((B.S : Subgroup G) ⊓ C.D.M)
      hEM inf_le_right hnormE hoddP
  -- `4 ∣ |S ⊓ E|`
  have h4E : 4 ∣ Nat.card ↥(Work.GW2.layerIn C.D.M) := four_dvd_layerIn_card I hbc C
  have h4SE : 4 ∣ Nat.card ↥((B.S : Subgroup G) ⊓ C.D.M ⊓ Work.GW2.layerIn C.D.M) :=
    four_dvd_inf_of_odd_relIndex (Work.GW2.layerIn C.D.M) ((B.S : Subgroup G) ⊓ C.D.M) h4E hoddE
  have hSEeq : ((B.S : Subgroup G) ⊓ C.D.M) ⊓ Work.GW2.layerIn C.D.M =
      (B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M := by
    rw [inf_assoc, inf_eq_right.mpr hEM]
  rw [hSEeq] at h4SE
  have hSE4 : 4 ≤ Nat.card ↥((B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M) :=
    Nat.le_of_dvd Nat.card_pos h4SE
  -- `|S| ≥ 8`
  have hS8 : 8 ≤ Nat.card ↥(B.S : Subgroup G) := by
    have hidx1 : ((B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M).relIndex (B.S : Subgroup G) ≠ 1 := by
      intro h1
      exact hrE (Subgroup.mem_inf.mp ((Subgroup.relIndex_eq_one.mp h1) hrS)).2
    have hidx0 : ((B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M).relIndex
        (B.S : Subgroup G) ≠ 0 := by
      show (((B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M).subgroupOf (B.S : Subgroup G)).index ≠ 0
      exact Subgroup.index_ne_zero_of_finite
    have hidx2 : 2 ≤ ((B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M).relIndex
        (B.S : Subgroup G) := by omega
    have hcard : ((B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M).relIndex (B.S : Subgroup G) *
        Nat.card ↥((B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M) =
        Nat.card ↥(B.S : Subgroup G) := by
      have h := Subgroup.relIndex_mul_card
        ((B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M) (B.S : Subgroup G)
      have h2 : ((B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M) ⊓ (B.S : Subgroup G) =
          (B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M := inf_eq_left.mpr inf_le_left
      rw [h2] at h
      exact h
    calc (8 : ℕ) = 2 * 4 := by norm_num
      _ ≤ ((B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M).relIndex (B.S : Subgroup G) *
            Nat.card ↥((B.S : Subgroup G) ⊓ Work.GW2.layerIn C.D.M) := Nat.mul_le_mul hidx2 hSE4
      _ = Nat.card ↥(B.S : Subgroup G) := hcard
  have hn4 : 4 ≤ n := by
    obtain ⟨e⟩ := hdih
    have hc : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    omega
  have hn2 : 2 ≤ n := by omega
  -- `G` has no normal subgroup of index `2`
  have hNidx : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
    intro N hN hNidx2
    haveI := hN
    haveI : IsSimpleGroup G := hbc.simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
    · rw [hbot] at hNidx2
      have h1 : (⊥ : Subgroup G).index = Nat.card G := by
        rw [Subgroup.index_eq_card]
        exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
      have hcard : Nat.card G = 2 := by rw [← h1]; exact hNidx2
      have hcardT : Nat.card ↥(Subgroup.zpowers B.t) = 2 := by
        rw [Nat.card_zpowers]; exact B.t_order
      have hT : Subgroup.zpowers B.t = ⊤ :=
        Subgroup.eq_top_of_card_eq _ (by rw [hcardT, hcard])
      have hcomm : IsMulCommutative G := by
        refine IsMulCommutative.of_comm fun a b => ?_
        have ha : a ∈ Subgroup.zpowers B.t := by rw [hT]; exact Subgroup.mem_top a
        have hb : b ∈ Subgroup.zpowers B.t := by rw [hT]; exact Subgroup.mem_top b
        obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
        obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
        rw [← zpow_add, add_comm, zpow_add]
      obtain ⟨a, b, hab⟩ := hbc.nonab
      exact hab (hcomm.is_comm.comm a b)
    · rw [htop] at hNidx2
      exact absurd hNidx2 (by rw [Subgroup.index_top]; norm_num)
  -- one class of involutions in `G`
  have hfus : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y :=
    (I.toolkit.fus G B.S n hn2 hdih hNidx).1
  exact h G B.S n hn4 hdih hfus B.t (Work.GW2.BenderSetup.t_mem_S B) B.t_order
    (Work.GW2.BenderSetup.t_central B) r hrS hr2 (fun hh => htr hh.symm)

end Work.CORE4.NineImpl9
