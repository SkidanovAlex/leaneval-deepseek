/-
Copyright (c) 2026 gorenstein_walter team. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: CORE2A area (fundmath3-gorenstein_walter)
-/
import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.lemma24
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.CORE2A.odd_subgroup_le_oddCoreIn
import Submission.Work.CORE2A.le_oddCoreIn_of_normal_of_odd
import Submission.Work.CORE2A.oddCoreIn_le_oddCoreIn_of_normal
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.RED.le_center_of_card_eq_two

/-!
# CORE2A: Bender 1981, Theorem 2.6, first paragraph — `U = O(Ĥ)`

Bender 1981, p. 220: *"Suppose `1 ≠ O₂(Ĥ)`. Then `U` centralizes `O₂(Ĥ)` and hence equals
`O(Ĥ)`."*  This file proves that step: with `V = O₂(Ĥ)`, if `V ≠ ⊥` then
`oddCoreIn B.Hhat = B.U`, i.e. `O(Ĥ) = U = O(H)`.

The argument, with `V = O₂(Ĥ) ≤ S`, `V` a `2`-group and `V ◁ Ĥ`:

* **Case `t ∈ V`.**  Put `M = C_Ĥ(V)`.  Since `t ∈ V`, `M ≤ C(t) = H`.  Since `V ◁ Ĥ` and
  `V ≤ S ≤ H`, the two normal subgroups `U = O(H)` and `Õ = O(Ĥ)` of a common group meet `V`
  trivially, so each commutes with `V`: `U ⊆ M` and `Õ ⊆ M`.  Then
  - `Õ ≤ U`: `Õ ≤ M ≤ H` with `Õ ◁ H` odd, and every odd-order subgroup of `H` lies in
    `O(H) = U` because `H = U ⊔ S` with `S` a `2`-group (`odd_subgroup_le_oddCoreIn`);
  - `U ≤ Õ`: `U ≤ O(M)` (maximality of the odd core) and `O(M) ≤ O(Ĥ)`, because conjugation by
    `Ĥ` restricts to an automorphism of `M`, hence preserves `O(M)`; so `O(M)` is a normal odd
    subgroup of `Ĥ`.
* **Case `t ∉ V`.**  Then `V ∩ S₀ = ⊥` (`V` is a nontrivial `2`-group, and any involution of
  the cyclic `S₀` is `t`), which bounds `|V|` by the index `[S : S₀] = 2`, so `|V| = 2`.
  Hence `V ≤ Z(Ĥ)`, say `V = ⟨x⟩` with `x` an involution outside `S₀`.  Maximality of the
  coatom `Ĥ` gives `C(x) = Ĥ` (`C(x) ⊋ Ĥ` would force `x ∈ Z(G)`, impossible in a non-abelian
  simple group), and `x` is conjugate to `t` (`T.fus`), so `Ĥ = C(x) = C(t)^g = H^g`, whence
  `H = Ĥ` and `O(Ĥ) = O(H) = U`.
-/

open scoped MatrixGroups

namespace Work.CORE2A

open Subgroup

set_option linter.unusedVariables false

/-- `O₂(Ĥ)` is a `2`-group. -/
theorem pCoreIn_isPGroup_two {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    IsPGroup 2 ↥(Work.GW2.pCoreIn 2 B.Hhat) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsup : IsPGroup 2 ↥(sSup {N : Subgroup ↥B.Hhat | N.Normal ∧ IsPGroup 2 N}) :=
    Sylow.sSup_of_normal {N : Subgroup ↥B.Hhat | N.Normal ∧ IsPGroup 2 N}
      (fun N hN => hN.2) (fun N hN => hN.1)
  have hp : IsPGroup 2 ↥(Work.GW2.pCore 2 ↥B.Hhat) :=
    hsup.to_le (Subgroup.normalCore_le _)
  exact hp.map B.Hhat.subtype

/-- `O₂(Ĥ)` is normal in `Ĥ`. -/
theorem pCoreIn_subgroupOf_normal {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    ((Work.GW2.pCoreIn 2 B.Hhat).subgroupOf B.Hhat).Normal := by
  have h : (Work.GW2.pCoreIn 2 B.Hhat).subgroupOf B.Hhat = Work.GW2.pCore 2 ↥B.Hhat := by
    rw [Work.GW2.pCoreIn]
    exact Subgroup.comap_map_eq_self_of_injective B.Hhat.subtype_injective _
  rw [h]
  exact Work.GW2.pCore_normal 2 ↥B.Hhat

/-- `O_{2'}(K)` is normal in `K`. -/
theorem oddCoreIn_normal_inSelf {G : Type} [Group G] [Finite G] (K : Subgroup G) :
    ((Work.GW2.oddCoreIn K).subgroupOf K).Normal := by
  have h : (Work.GW2.oddCoreIn K).subgroupOf K = Work.GW2.oddCore ↥K := by
    rw [Work.GW2.oddCoreIn]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  rw [h]
  exact Work.GW2.oddCore_normal ↥K

/-- `O₂(Ĥ) ≤ S`: a normal `2`-subgroup lies in every Sylow `2`-subgroup. -/
theorem pCoreIn_le_sylow {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G) :
    Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) := by
  have hle := bSetup_S_le_Hhat B
  have hpg : IsPGroup 2 ↥((Work.GW2.pCoreIn 2 B.Hhat).subgroupOf B.Hhat) :=
    (pCoreIn_isPGroup_two B).of_equiv (Subgroup.subgroupOfEquivOfLe (Subgroup.map_subtype_le _)).symm
  have h1 : (Work.GW2.pCoreIn 2 B.Hhat).subgroupOf B.Hhat
      ≤ ((B.S).subtype hle : Subgroup ↥B.Hhat) := by
    haveI := pCoreIn_subgroupOf_normal B
    exact IsPGroup.le_sylow_of_normal hpg ((B.S).subtype hle)
  rw [Sylow.coe_subtype B.S hle] at h1
  intro x hx
  have hx' : (⟨x, Subgroup.map_subtype_le (Work.GW2.pCore 2 ↥B.Hhat) hx⟩ : ↥B.Hhat)
      ∈ (Work.GW2.pCoreIn 2 B.Hhat).subgroupOf B.Hhat := by
    rw [Subgroup.mem_subgroupOf]
    exact hx
  exact Subgroup.mem_subgroupOf.mp (h1 hx')

/-- Two normal subgroups of `K` with trivial intersection commute. -/
theorem le_centralizer_of_normal_of_inf_eq_bot {G : Type} [Group G] {A B K : Subgroup G}
    (hAK : A ≤ K) (hBK : B ≤ K) (hAn : (A.subgroupOf K).Normal) (hBn : (B.subgroupOf K).Normal)
    (hbot : A ⊓ B = ⊥) : A ≤ Subgroup.centralizer (B : Set G) := by
  have hbot' : A.subgroupOf K ⊓ B.subgroupOf K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨hzA, hzB⟩ := Subgroup.mem_inf.mp hz
    have h1 : (z : G) ∈ A ⊓ B :=
      Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hzA, Subgroup.mem_subgroupOf.mp hzB⟩
    rw [hbot] at h1
    exact Subtype.ext (Subgroup.mem_bot.mp h1)
  have hcomm : A.subgroupOf K ≤ Subgroup.centralizer ((B.subgroupOf K) : Set ↥K) := by
    have hle : ⁅A.subgroupOf K, B.subgroupOf K⁆ ≤ A.subgroupOf K ⊓ B.subgroupOf K :=
      le_inf (Subgroup.commutator_le_left _ _) (Subgroup.commutator_le_right _ _)
    rw [hbot'] at hle
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp hle)
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have h2 : (⟨b, hBK hb⟩ : ↥K) * ⟨a, hAK ha⟩ = ⟨a, hAK ha⟩ * ⟨b, hBK hb⟩ :=
    Subgroup.mem_centralizer_iff.mp (hcomm ha) ⟨b, hBK hb⟩ (Subgroup.mem_subgroupOf.mpr hb)
  exact congrArg Subtype.val h2

/-- The centralizer of a single element moves with conjugation. -/
theorem conjSub_centralizer_singleton {G : Type} [Group G] (g t : G) :
    Work.GW2.conjSub g (Subgroup.centralizer ({t} : Set G)) =
      Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
  ext x
  rw [Work.CORE2A.mem_conjSub_iff, Subgroup.mem_centralizer_iff, Subgroup.mem_centralizer_iff]
  simp only [Set.mem_singleton_iff, forall_eq]
  constructor
  · intro h
    calc (g * t * g⁻¹) * x = g * (t * (g⁻¹ * x * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * x * g) * t) * g⁻¹ := by rw [h]
      _ = x * (g * t * g⁻¹) := by group
  · intro h
    calc t * (g⁻¹ * x * g) = g⁻¹ * ((g * t * g⁻¹) * x) * g := by group
      _ = g⁻¹ * (x * (g * t * g⁻¹)) * g := by rw [h]
      _ = (g⁻¹ * x * g) * t := by group

/-- **Dichotomy for `V = O₂(Ĥ)`.**  If `V ≠ ⊥` then `V ≤ S`, and either `t ∈ V` or
`|V| = 2` with `V` not contained in `S₀`. -/
theorem pCoreIn_dichotomy {G : Type} [Group G] [Finite G] (B : Work.GW2.BenderSetup G)
    (hV : Work.GW2.pCoreIn 2 B.Hhat ≠ ⊥) :
    Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) ∧
      (B.t ∈ Work.GW2.pCoreIn 2 B.Hhat ∨
        (Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat) = 2 ∧
          ¬ Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨pCoreIn_le_sylow B, ?_⟩
  by_cases ht : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat
  · exact Or.inl ht
  -- `V ∩ S₀ = ⊥`: any nonidentity element of it generates an involution of `S₀`, i.e. `t`
  have hVS0 : Work.GW2.pCoreIn 2 B.Hhat ⊓ B.S0 = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    by_contra hz1
    have hpg : IsPGroup 2 ↥(Work.GW2.pCoreIn 2 B.Hhat ⊓ B.S0) :=
      (pCoreIn_isPGroup_two B).to_le inf_le_left
    have hne : Work.GW2.pCoreIn 2 B.Hhat ⊓ B.S0 ≠ ⊥ := fun h => by
      rw [h] at hz
      exact hz1 (Subgroup.mem_bot.mp hz)
    have hdvd : 2 ∣ Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat ⊓ B.S0) := by
      rcases hpg.card_eq_or_dvd (p := 2) with h1 | h2
      · exact absurd (Subgroup.card_eq_one.mp h1) hne
      · exact h2
    obtain ⟨w, hw2⟩ :=
      exists_prime_orderOf_dvd_card' (G := ↥(Work.GW2.pCoreIn 2 B.Hhat ⊓ B.S0)) 2 hdvd
    have hwV : ((w : ↥(Work.GW2.pCoreIn 2 B.Hhat ⊓ B.S0)) : G)
        ∈ Work.GW2.pCoreIn 2 B.Hhat := (Subgroup.mem_inf.mp w.2).1
    have hwS0 : ((w : ↥(Work.GW2.pCoreIn 2 B.Hhat ⊓ B.S0)) : G) ∈ B.S0 :=
      (Subgroup.mem_inf.mp w.2).2
    have hw2' : orderOf (((w : ↥(Work.GW2.pCoreIn 2 B.Hhat ⊓ B.S0)) : G)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact hw2
    haveI : IsCyclic ↥B.S0 := B.S0_cyclic
    have heq : (⟨((w : ↥(Work.GW2.pCoreIn 2 B.Hhat ⊓ B.S0)) : G), hwS0⟩ : ↥B.S0)
        = ⟨B.t, B.t_mem⟩ :=
      eq_of_orderOf_eq_two_of_isCyclic (b := (⟨B.t, B.t_mem⟩ : ↥B.S0))
        (by rw [Subgroup.orderOf_mk]; exact hw2') (by rw [Subgroup.orderOf_mk]; exact B.t_order)
    have hwt : ((w : ↥(Work.GW2.pCoreIn 2 B.Hhat ⊓ B.S0)) : G) = B.t :=
      congrArg Subtype.val heq
    exact ht (hwt ▸ hwV)
  refine Or.inr ⟨?_, ?_⟩
  · -- `|V| ≤ 2`, then `|V| ≥ 2`
    have hle := pCoreIn_le_sylow B
    have hrel : (Work.GW2.pCoreIn 2 B.Hhat).relIndex (B.S : Subgroup G)
        * Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat) = Nat.card ↥(B.S : Subgroup G) := by
      have h := Subgroup.relIndex_mul_card (Work.GW2.pCoreIn 2 B.Hhat) (B.S : Subgroup G)
      rwa [inf_eq_left.mpr hle] at h
    have hineq : Nat.card ↥(B.S : Subgroup G)
        ≤ (Work.GW2.pCoreIn 2 B.Hhat).relIndex (B.S : Subgroup G) * 2 := by
      have h := Subgroup.relIndex_inf_le (H := Work.GW2.pCoreIn 2 B.Hhat) (K := B.S0)
        (L := (B.S : Subgroup G))
      rw [hVS0, Subgroup.relIndex_bot_left, B.S0_index] at h
      exact h
    have hle2 : Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat) ≤ 2 := by
      have hpos : 0 < (Work.GW2.pCoreIn 2 B.Hhat).relIndex (B.S : Subgroup G) := by
        rcases Nat.eq_zero_or_pos ((Work.GW2.pCoreIn 2 B.Hhat).relIndex (B.S : Subgroup G))
          with h0 | h0
        · rw [h0, zero_mul] at hrel
          exact (Nat.card_pos.ne' hrel.symm).elim
        · exact h0
      rw [← hrel] at hineq
      exact Nat.le_of_mul_le_mul_left hineq hpos
    have hge2 : 2 ≤ Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat) := by
      have hdvd : 2 ∣ Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat) := by
        rcases (pCoreIn_isPGroup_two B).card_eq_or_dvd (p := 2) with h1 | h2
        · exact absurd (Subgroup.card_eq_one.mp h1) hV
        · exact h2
      exact Nat.le_of_dvd Nat.card_pos hdvd
    omega
  · -- `V ≰ S₀`
    intro hle
    have h1 : Work.GW2.pCoreIn 2 B.Hhat = ⊥ := by
      rw [← inf_eq_left.mpr hle, hVS0]
    exact hV h1

theorem thm26a_U_eq_Ohat (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop) (h22 : Work.GW2.Lemma22Prop) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Work.GW2.pCoreIn 2 B.Hhat ≠ ⊥ → Work.GW2.oddCoreIn B.Hhat = B.U := by
  intro G _ _ hFT hctx B hV
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup G := hctx.simple
  obtain ⟨n, hn2, hdih⟩ := Work.CORE3.SylowDihedral G hctx B
  obtain ⟨hVS, hdich⟩ := pCoreIn_dichotomy B hV
  have hH : B.U ⊔ (B.S : Subgroup G) = B.H := Work.CORE3.H_eq_U_sup_S G T hctx B
  have hUodd : Odd (Nat.card ↥B.U) := bSetup_U_odd B
  have hVpg : IsPGroup 2 ↥(Work.GW2.pCoreIn 2 B.Hhat) := pCoreIn_isPGroup_two B
  have hVH : Work.GW2.pCoreIn 2 B.Hhat ≤ B.H := hVS.trans (bSetup_S_le_H B)
  have hVHhat : Work.GW2.pCoreIn 2 B.Hhat ≤ B.Hhat := Subgroup.map_subtype_le _
  have hVnorm : ((Work.GW2.pCoreIn 2 B.Hhat).subgroupOf B.Hhat).Normal :=
    pCoreIn_subgroupOf_normal B
  have hVnormH : ((Work.GW2.pCoreIn 2 B.Hhat).subgroupOf B.H).Normal :=
    (Subgroup.normal_subgroupOf_iff hVH).mpr fun h k hh hk =>
      (Subgroup.normal_subgroupOf_iff hVHhat).mp hVnorm h k hh (B.H_le_Hhat hk)
  have hOodd : Odd (Nat.card ↥(Work.GW2.oddCoreIn B.Hhat)) := by
    rw [Work.GW2.oddCoreIn, Subgroup.card_map_of_injective B.Hhat.subtype_injective]
    exact Work.ASM.oddCore_odd ↥B.Hhat
  rcases hdich with ht | ⟨hVcard, -⟩
  · -- ## Case `t ∈ V`
    set M : Subgroup G := Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat) : Set G) ⊓ B.Hhat
      with hMdef
    have hMleHhat : M ≤ B.Hhat := by rw [hMdef]; exact inf_le_right
    have hMleH : M ≤ B.H := by
      rw [hMdef]
      intro z hz
      obtain ⟨hzC, -⟩ := Subgroup.mem_inf.mp hz
      rw [show B.H = Subgroup.centralizer ({B.t} : Set G) from rfl,
        Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff] at hy
      subst hy
      exact Subgroup.mem_centralizer_iff.mp hzC B.t ht
    have hUnormH : (B.U.subgroupOf B.H).Normal := oddCoreIn_normal_inSelf B.H
    have hMnorm : (M.subgroupOf B.Hhat).Normal := by
      rw [hMdef, Subgroup.normal_subgroupOf_iff inf_le_right]
      intro h k hh hk
      obtain ⟨hhC, hhH⟩ := Subgroup.mem_inf.mp hh
      refine Subgroup.mem_inf.mpr
        ⟨?_, B.Hhat.mul_mem (B.Hhat.mul_mem hk hhH) (B.Hhat.inv_mem hk)⟩
      rw [Subgroup.mem_centralizer_iff] at hhC ⊢
      intro v hv
      have hv' : k⁻¹ * v * k ∈ Work.GW2.pCoreIn 2 B.Hhat := by
        have h := (Subgroup.normal_subgroupOf_iff hVHhat).mp hVnorm v k⁻¹ hv (B.Hhat.inv_mem hk)
        simpa using h
      have h2 : (k⁻¹ * v * k) * h = h * (k⁻¹ * v * k) := hhC (k⁻¹ * v * k) hv'
      calc v * (k * h * k⁻¹) = k * ((k⁻¹ * v * k) * h) * k⁻¹ := by group
        _ = k * (h * (k⁻¹ * v * k)) * k⁻¹ := by rw [h2]
        _ = (k * h * k⁻¹) * v := by group
    have hUleC : B.U ≤ Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat) : Set G) :=
      le_centralizer_of_normal_of_inf_eq_bot (bSetup_U_le_H B) hVH hUnormH hVnormH
        (inf_eq_bot_of_odd_of_isPGroup_two hUodd hVpg)
    have hUleM : B.U ≤ M := by
      rw [hMdef]
      exact le_inf hUleC (bSetup_U_le_Hhat B)
    have hOleC : Work.GW2.oddCoreIn B.Hhat
        ≤ Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat) : Set G) :=
      le_centralizer_of_normal_of_inf_eq_bot
        (Subgroup.map_subtype_le (Work.GW2.oddCore ↥B.Hhat)) hVHhat
        (oddCoreIn_normal_inSelf B.Hhat) hVnorm
        (inf_eq_bot_of_odd_of_isPGroup_two hOodd hVpg)
    have hOleM : Work.GW2.oddCoreIn B.Hhat ≤ M := by
      rw [hMdef]
      exact le_inf hOleC (Subgroup.map_subtype_le (Work.GW2.oddCore ↥B.Hhat))
    have hOleH : Work.GW2.oddCoreIn B.Hhat ≤ B.H := hOleM.trans hMleH
    have hUnormM : (B.U.subgroupOf M).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hUleM]
      intro a b ha hb
      exact (Subgroup.normal_subgroupOf_iff (bSetup_U_le_H B)).mp hUnormH a b ha (hMleH hb)
    have hUleO : B.U ≤ Work.GW2.oddCoreIn B.Hhat :=
      (le_oddCoreIn_of_normal_of_odd hUleM hUnormM hUodd).trans
        (oddCoreIn_le_oddCoreIn_of_normal hMleHhat hMnorm)
    have hOleU : Work.GW2.oddCoreIn B.Hhat ≤ B.U :=
      odd_subgroup_le_oddCoreIn B.H B.U B.S (bSetup_U_eq B) hH B.S.isPGroup'
        (Work.GW2.oddCoreIn B.Hhat) hOleH hOodd
    exact le_antisymm hOleU hUleO
  · -- ## Case `t ∉ V`
    obtain ⟨x, hx1⟩ : ∃ x : ↥(Work.GW2.pCoreIn 2 B.Hhat), x ≠ 1 := by
      haveI : Nontrivial ↥(Work.GW2.pCoreIn 2 B.Hhat) :=
        (Subgroup.nontrivial_iff_ne_bot _).mpr hV
      exact exists_ne 1
    have hxne : (x : G) ≠ 1 := fun h => hx1 (Subtype.ext h)
    have hxorder : orderOf (x : G) = 2 := by
      have hdvd : orderOf (x : G) ∣ Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat) :=
        Subgroup.orderOf_dvd_natCard _ x.2
      rw [hVcard] at hdvd
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
      · exact absurd (orderOf_eq_one_iff.mp h1) hxne
      · exact h2
    -- `x` is central in `Ĥ`, because it generates the normal subgroup `V` of order two
    have hxcent : ∀ h ∈ B.Hhat, h * (x : G) * h⁻¹ = (x : G) := by
      have hcard' : Nat.card ↥((Work.GW2.pCoreIn 2 B.Hhat).subgroupOf B.Hhat) = 2 := by
        rw [Nat.card_congr
          (Subgroup.subgroupOfEquivOfLe (H := Work.GW2.pCoreIn 2 B.Hhat)
            (K := B.Hhat) hVHhat).toEquiv]
        exact hVcard
      have hcenter := Work.RED.le_center_of_card_eq_two
        ((Work.GW2.pCoreIn 2 B.Hhat).subgroupOf B.Hhat) hVnorm hcard'
      intro h hh
      have hxmem : (⟨(x : G), hVHhat x.2⟩ : ↥B.Hhat)
          ∈ (Work.GW2.pCoreIn 2 B.Hhat).subgroupOf B.Hhat := by
        rw [Subgroup.mem_subgroupOf]
        exact x.2
      have h1 : (⟨(x : G), hVHhat x.2⟩ : ↥B.Hhat) ∈ Subgroup.center ↥B.Hhat := hcenter hxmem
      have h2 := (Subgroup.mem_center_iff.mp h1) (⟨h, hh⟩ : ↥B.Hhat)
      have h3 : h * (x : G) = (x : G) * h := by
        have h4 := congrArg Subtype.val h2
        simpa using h4
      calc h * (x : G) * h⁻¹ = ((x : G) * h) * h⁻¹ := by rw [h3]
        _ = (x : G) := by group
    -- `C(x) = Ĥ` by maximality of the coatom `Ĥ`
    have hCx : Subgroup.centralizer ({(x : G)} : Set G) = B.Hhat := by
      have hle : B.Hhat ≤ Subgroup.centralizer ({(x : G)} : Set G) := by
        intro h hh
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        have h3 : h * (x : G) * h⁻¹ * h = (x : G) * h := by rw [hxcent h hh]
        have h4 : h * (x : G) = (x : G) * h := by simpa using h3
        exact h4.symm
      refine le_antisymm ?_ hle
      by_contra hcon
      have hne : B.Hhat ≠ Subgroup.centralizer ({(x : G)} : Set G) :=
        fun heq => hcon (le_of_eq heq.symm)
      have htop : Subgroup.centralizer ({(x : G)} : Set G) = ⊤ :=
        (B.Hhat_coatom.lt_iff).mp (lt_of_le_of_ne hle hne)
      have hxZ : (x : G) ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact (Subgroup.mem_centralizer_iff.mp (htop ▸ Subgroup.mem_top g) (x : G)
          (by simp)).symm
      haveI : (Subgroup.zpowers (x : G)).Normal :=
        Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hxZ)
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.zpowers (x : G)) with hb | htop2
      · rw [Subgroup.zpowers_eq_bot] at hb
        exact hxne hb
      · obtain ⟨a, b, hab⟩ := hctx.nonab
        have hcomm : IsMulCommutative G := by
          refine IsMulCommutative.of_comm fun a b => ?_
          have ha : a ∈ Subgroup.zpowers (x : G) := by rw [htop2]; exact Subgroup.mem_top a
          have hb' : b ∈ Subgroup.zpowers (x : G) := by rw [htop2]; exact Subgroup.mem_top b
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb'
          rw [← zpow_add, add_comm, zpow_add]
        exact hab (hcomm.is_comm.comm a b)
    -- `x` is conjugate to `t`, hence `Ĥ` is conjugate to `H`
    have hnoN : ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := fun N hN h2 => by
      haveI : N.Normal := hN
      have hne_top : N ≠ ⊤ := by intro h; rw [h] at h2; simp at h2
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop3
      · have h1 : (⊥ : Subgroup G).index = Nat.card G := by
          rw [Subgroup.index_eq_card]
          exact Nat.card_congr QuotientGroup.quotientBot.toEquiv
        have hcard : Nat.card G = 2 := h1.symm.trans (hbot ▸ h2)
        have hcardT : Nat.card ↥(Subgroup.zpowers B.t) = 2 := by
          rw [Nat.card_zpowers]
          exact B.t_order
        have hT : Subgroup.zpowers B.t = ⊤ :=
          Subgroup.eq_top_of_card_eq _ (by rw [hcardT, hcard])
        have hcomm : IsMulCommutative G := by
          refine IsMulCommutative.of_comm fun a b => ?_
          have ha : a ∈ Subgroup.zpowers B.t := by rw [hT]; exact Subgroup.mem_top a
          have hb : b ∈ Subgroup.zpowers B.t := by rw [hT]; exact Subgroup.mem_top b
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
          rw [← zpow_add, add_comm, zpow_add]
        obtain ⟨a, b, hab⟩ := hctx.nonab
        exact hab (hcomm.is_comm.comm a b)
      · exact hne_top htop3
    have hconj : IsConj (x : G) B.t :=
      (T.fus G B.S n hn2 hdih hnoN).1 (x : G) B.t hxorder B.t_order
    obtain ⟨c, hc⟩ := hconj
    have hx0 : (c : G)⁻¹ * B.t * ((c : G)⁻¹)⁻¹ = (x : G) := by
      have h1 : (c : G) * (x : G) = B.t * (c : G) := hc
      calc (c : G)⁻¹ * B.t * ((c : G)⁻¹)⁻¹ = (c : G)⁻¹ * (B.t * (c : G)) := by group
        _ = (c : G)⁻¹ * ((c : G) * (x : G)) := by rw [← h1]
        _ = (x : G) := by group
    have h1 : Work.GW2.conjSub (c : G)⁻¹ (Subgroup.centralizer ({B.t} : Set G))
        = Subgroup.centralizer ({(x : G)} : Set G) := by
      rw [conjSub_centralizer_singleton, hx0]
    have h2 : Work.GW2.conjSub (c : G)⁻¹ B.H = B.Hhat := by
      rw [show B.H = Subgroup.centralizer ({B.t} : Set G) from rfl, h1, hCx]
    have h3 : B.H = Work.GW2.conjSub (c : G) B.Hhat := by
      have h4 := congrArg (Work.GW2.conjSub (c : G)) h2
      rwa [Work.CORE2A.conjSub_conjSub_inv] at h4
    have h5 : Nat.card ↥B.H = Nat.card ↥B.Hhat := by
      rw [h3, Work.CORE2A.card_conjSub]
    have h6 : B.H = B.Hhat := Subgroup.eq_of_le_of_card_ge B.H_le_Hhat (by rw [h5])
    rw [← h6]

end Work.CORE2A
