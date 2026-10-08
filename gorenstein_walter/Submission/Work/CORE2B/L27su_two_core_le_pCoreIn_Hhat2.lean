import Mathlib
import Submission.Work.CORE2B.Basic
import Submission.Work.CORE2B.API
import Submission.Work.CORE2B.isPGroup_pCoreIn_two
import Submission.Work.CORE2B.t_central_in_S
import Submission.Work.CORE2B.oddCore_odd
import Submission.Work.CORE2B.L27su_utils

/-!
# CORE2B — `P ≤ O₂(Ĥ)` for a `2`-subgroup `P ≤ C_G(t)` centralizing `U = O(H)`

Bender 1981, Lemma 2.7, needs the inclusion `O₂(M) ≤ O₂(Ĥ)`.  This file proves the input for it.
Since `H = C_G(t) = U ⊔ S` (Bender p. 219; this is `Work.GW2.CentralizerSplitProp`, the toolbox
field `T.split`), any `2`-subgroup `P ≤ H = C_G(t)` that centralizes `U = O(H)` is contained in
`S`; Theorem 2.6 (`h26`) identifies `S ⊓ C_G(U)` with `O₂(Ĥ)`, so

  `P ≤ S ⊓ C_G(U) = O₂(Ĥ)`.

The group-theoretic core is isolated in
`L27su_centralizer_two_le_right_of_sup_eq_top2`: if `U ◁ H` has odd order and `U ⊔ S = ⊤` with
`S` a `2`-group, then every `2`-subgroup `P ≤ C_H(U)` lies in `S`.  Indeed, write `x = u · s`
(`u ∈ U`, `s ∈ S`) for `x ∈ C_H(U)`; centrality of `x` says that conjugation by `s` on `U`
equals conjugation by `u⁻¹`, and evaluating at `u ∈ U` gives `s u s⁻¹ = u⁻¹ u u = u`, i.e. `s`
and `u` commute.  If moreover `x` has `2`-power order `2^k`, then `(u s)^(2^k) = u^(2^k) s^(2^k)`
and this is `1`; as `U ⊓ S = ⊥` (`U` odd, `S` a `2`-group) we get `u^(2^k) = 1`, so `orderOf u`
divides both the `2`-power `2^k` and the odd number `|U|`, whence `u = 1` and `x = s ∈ S`.

Everything is stated in the `Work.GW2` vocabulary of `Submission.Work.CORE2B.Defs` (the copy the
CORE2B area uses), so the module is importable next to `Submission.Work.CORE2B.Basic`.
-/

namespace Work.CORE2B

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

/-- `U = O(H)`, viewed inside `↥B.H`, is exactly `O(↥B.H)`. -/
theorem L27su_U_subgroupOf_eq_oddCore2 {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) : B.U.subgroupOf B.H = Work.GW2.oddCore ↥B.H := by
  show (Work.GW2.oddCoreIn B.H).subgroupOf B.H = _
  rw [Work.GW2.oddCoreIn, Subgroup.subgroupOf]
  exact Subgroup.comap_map_eq_self_of_injective B.H.subtype_injective _

theorem L27su_U_subgroupOf_normal2 {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) : (B.U.subgroupOf B.H).Normal :=
  (L27su_U_subgroupOf_eq_oddCore2 B) ▸ Work.GW2.oddCore_normal ↥B.H

/-- `U = O(H) = O_{2'}(H)` has odd order, viewed inside `↥B.H`. -/
theorem L27su_U_subgroupOf_odd2 {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) : Odd (Nat.card (B.U.subgroupOf B.H)) := by
  rw [L27su_U_subgroupOf_eq_oddCore2 B]
  exact oddCore_odd

/-- A centrality hypothesis `P ≤ C_G(U)` together with `P ≤ H` translates to centrality of
`P.subgroupOf H` in the group `↥H`. -/
theorem L27su_centralizer_subgroupOf2 {G : Type} [Group G] [Finite G]
    (B : Work.GW2.BenderSetup G) (P : Subgroup G) (hPH : P ≤ B.H)
    (hPC : P ≤ Subgroup.centralizer (B.U : Set G)) :
    P.subgroupOf B.H ≤ Subgroup.centralizer (B.U.subgroupOf B.H : Set ↥B.H) := by
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
  have hyU : (y : G) ∈ B.U := Subgroup.mem_subgroupOf.mp hy
  have h := Subgroup.mem_centralizer_iff.mp (hPC hxP) (y : G) hyU
  exact Subtype.ext h

/-- **A `2`-subgroup of `C_H(U)` lies in `S`, for `U ◁ H` of odd order and `H = U ⊔ S` with `S`
a `2`-group.**  (`U ⊓ S` is trivial: it divides both the odd number `|U|` and `|S| = 2ⁿ`.) -/
theorem L27su_centralizer_two_le_right_of_sup_eq_top2 {H : Type} [Group H] [Finite H]
    (U S P : Subgroup H) [U.Normal] (hUS : U ⊔ S = ⊤) (hS : IsPGroup 2 S)
    (hUodd : Odd (Nat.card U)) (hP : IsPGroup 2 P)
    (hPC : P ≤ Subgroup.centralizer (U : Set H)) : P ≤ S := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot2 : ¬ 2 ∣ Nat.card U := by
    rw [← even_iff_two_dvd]
    exact Nat.not_even_iff_odd.mpr hUodd
  -- `U ⊓ S = ⊥`
  have hdisj : U ⊓ S = ⊥ := by
    refine (Subgroup.disjoint_of_coprime_natCard (H := U) (K := S) ?_).eq_bot
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hS
    rw [hn]
    exact Nat.prime_two.coprime_pow_of_not_dvd hnot2
  intro x hxP
  have hxc : x ∈ Subgroup.centralizer (U : Set H) := hPC hxP
  -- `x` has `2`-power order
  obtain ⟨k, hk⟩ := isPGroup_iff_orderOf_dvd_pow.mp hP ⟨x, hxP⟩
  rw [Subgroup.orderOf_mk] at hk
  have hpow : x ^ (2 ^ k) = 1 := orderOf_dvd_iff_pow_eq_one.mp hk
  -- decompose `x = u * s`
  have hxsup : x ∈ U ⊔ S := by rw [hUS]; exact Subgroup.mem_top x
  obtain ⟨u, hu, s, hs, hus⟩ := (Subgroup.mem_sup_of_normal_left (s := U) (t := S)).mp hxsup
  -- conjugation by `s` on `U` equals conjugation by `u⁻¹`
  have hconj : ∀ y ∈ U, s * y * s⁻¹ = u⁻¹ * y * u := by
    intro y hy
    have hyx : x * y * x⁻¹ = y := by
      have h := Subgroup.mem_centralizer_iff.mp hxc y hy
      rw [← h]; group
    have h2 : u * (s * y * s⁻¹) * u⁻¹ = x * y * x⁻¹ := by rw [← hus]; group
    rw [hyx] at h2
    calc s * y * s⁻¹ = u⁻¹ * (u * (s * y * s⁻¹) * u⁻¹) * u := by group
      _ = u⁻¹ * y * u := by rw [h2]
  -- hence `s` commutes with `u`
  have hcomm : s * u = u * s := by
    have h := hconj u hu
    have h' : s * u * s⁻¹ = u := by simpa using h
    calc s * u = (s * u * s⁻¹) * s := by group
      _ = u * s := by rw [h']
  have hmul : (u * s) ^ (2 ^ k) = u ^ (2 ^ k) * s ^ (2 ^ k) :=
    Commute.mul_pow (show Commute u s from hcomm.symm) (2 ^ k)
  have h1 : u ^ (2 ^ k) * s ^ (2 ^ k) = 1 := by
    rw [← hmul, hus]
    exact hpow
  -- `u ^ (2^k) = 1`, since it lies in `U ⊓ S = ⊥`
  have hum : u ^ (2 ^ k) = 1 := by
    have h2 : u ^ (2 ^ k) = (s ^ (2 ^ k))⁻¹ := mul_eq_one_iff_eq_inv.mp h1
    have hmem : u ^ (2 ^ k) ∈ U ⊓ S :=
      ⟨U.pow_mem hu _, by rw [h2]; exact S.inv_mem (S.pow_mem hs _)⟩
    have hbot : u ^ (2 ^ k) ∈ (⊥ : Subgroup H) := hdisj ▸ hmem
    rwa [Subgroup.mem_bot] at hbot
  -- `orderOf u` divides both the `2`-power `2^k` and the odd number `|U|`
  have hord2 : orderOf u ∣ 2 ^ k := orderOf_dvd_iff_pow_eq_one.mpr hum
  have hordU : orderOf u ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hu
  have hcop : Nat.Coprime (2 ^ k) (Nat.card U) :=
    (Nat.prime_two.coprime_pow_of_not_dvd hnot2).symm
  have hu1 : u = 1 := orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop hord2 hordU)
  rw [hu1, one_mul] at hus
  rw [← hus]
  exact hs

theorem L27su_two_core_le_pCoreIn_Hhat2 :
    ∀ (T : Work.GW2.LocalToolkit) (h26 : Work.GW2.Thm26Prop) (G : Type) [Group G] [Finite G],
      Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (P : Subgroup G), IsPGroup 2 P →
        P ≤ Subgroup.centralizer (B.U : Set G) → P ≤ B.H →
        P ≤ Work.GW2.pCoreIn 2 B.Hhat := by
  intro T h26 G _ _ hFT hCtx B P hP hPC hPH
  -- Theorem 2.6 (ii): `O₂(Ĥ) = S ⊓ C_G(U)`.
  obtain ⟨-, hO2, -⟩ := h26 G hFT hCtx B
  -- Bender p. 219 (via `T.split`): `H = U ⊔ S`.
  obtain ⟨n, hn2, hdih⟩ := L27su_S_dihedral hCtx B
  have hsplit : B.U ⊔ (B.S : Subgroup G) = B.H :=
    T.split G B.S n hn2 hdih B.t (B.S0_le B.t_mem) B.t_order (t_central_in_S B)
  -- Work inside `↥B.H`: a `2`-subgroup of `C_H(U)` lies in `S`.
  have hUleH : B.U ≤ B.H := Subgroup.map_subtype_le _
  have hSleH : (B.S : Subgroup G) ≤ B.H := L27su_S_le_H B
  have hUS' : B.U.subgroupOf B.H ⊔ (B.S : Subgroup G).subgroupOf B.H = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUleH hSleH, hsplit, Subgroup.subgroupOf_self]
  have hS' : IsPGroup 2 ((B.S : Subgroup G).subgroupOf B.H) := B.S.isPGroup'.comap_subtype
  have hP' : IsPGroup 2 (P.subgroupOf B.H) := hP.comap_subtype (K := B.H)
  haveI : (B.U.subgroupOf B.H).Normal := L27su_U_subgroupOf_normal2 B
  have hPS' : P.subgroupOf B.H ≤ (B.S : Subgroup G).subgroupOf B.H :=
    L27su_centralizer_two_le_right_of_sup_eq_top2 (B.U.subgroupOf B.H)
      ((B.S : Subgroup G).subgroupOf B.H) (P.subgroupOf B.H)
      hUS' hS' (L27su_U_subgroupOf_odd2 B) hP'
      (L27su_centralizer_subgroupOf2 B P hPH hPC)
  -- Translate back to `G`.
  have hPS : P ≤ (B.S : Subgroup G) := by
    intro x hx
    have hx' : (⟨x, hPH hx⟩ : ↥B.H) ∈ P.subgroupOf B.H := by
      rw [Subgroup.mem_subgroupOf]; exact hx
    have h := hPS' hx'
    rw [Subgroup.mem_subgroupOf] at h
    exact h
  rw [← hO2]
  exact le_inf hPS hPC

end Work.CORE2B
