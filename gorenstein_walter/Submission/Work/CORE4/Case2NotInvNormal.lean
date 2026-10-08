/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Gorenstein–Walter formalisation team (area CORE4, `Work.CORE4`)

# AREA CORE4 — `Work.CORE4.Case2NotInvNormal`: the exceptional clause of Bender §4 (8)

Bender 1981, §4 (8), p. 225–226, contains the trichotomy for `Q := Ω₁(Z₂(O_p(U)))`; its third
case concludes `I_U(s) ⊲ Ĥ`.  Bender immediately discards this case (p. 227) with the remark
"then `S₀ = O₂(H ∩ E) = O₂(H) = C_S(U)`", which enters the hypothesis list of the leaves below as
`S₀ ≤ C_G(U)`.

Formally: from `S₀ ≤ C_G(U)` the exceptional clause `Case2InvNormal B D` (the existence of a
subgroup `I` with `(I : Set G) = invSet B.U D.s`, `I ≤ Ĥ` and `I ⊴ Ĥ`) is impossible.

Route (design pass 9 §1).  Bender's Lemma 2.8 (`Work.GW2.Lemma28Prop`, the field `I.lem28` of
`Work.GW2.C4Inputs`) states, contrapositively, that if *every* inversion subgroup
`I_U(s') = invSet B.U s'` (`s' ∈ S ∖ S₀`) were the underlying set of a subgroup normal in `U`,
then `[S₀, U] ≠ 1`.  Since `S₀ ≤ C_G(U)` forces `[S₀, U] = 1`
(`Subgroup.commutator_eq_bot_iff_le_centralizer`), some `s' ∈ S ∖ S₀` has `I_U(s')` not normal in
`U`.  Now `S₀` has index two in `S` (`BenderSetup.S0_index`), so any two elements of `S` outside
`S₀` are congruent modulo `S₀` (`Subgroup.mul_mem_iff_of_index_two`); in particular
`s' = y · D.s` with `y = s' · D.s⁻¹ ∈ S₀`.  Because `S₀ ≤ C_G(U)`, the element `y` centralizes
`U`, and centralizing `U` does not change inversion: `invSet B.U (y * s) = invSet B.U s` for
every `s` (`invSet_mul_centralizer`).  So `invSet B.U s' = invSet B.U D.s`, and a witness `I` of
`Case2InvNormal` — whose carrier is `invSet B.U D.s ⊆ U ≤ Ĥ` — is a subgroup of `U` normal in
`Ĥ`, hence normal in `U` (`Subgroup.normal_subgroupOf_iff`), a contradiction.

The hypothesis `S₀ ≤ C_G(U)` is *not* used in the auxiliary fact `s ∉ S₀` (`s_notMem_S0` below,
which only uses `U ≤ H = C_G(t)`: `t` centralizes `U`, and `S₀` is cyclic, so the only element of
order two of `S₀` is `t`); it enters exactly once, in the centralizer step above.
-/
import Mathlib
import Submission.OddOrder.FeitThompson
import Submission.Work.CORE4.Defs
import Submission.Work.CORE4.InvSet.invSet_mul_centralizer
import Submission.Work.CORE4.API
import Submission.Work.CORE4.Case2K1_ne_bot
import Submission.Work.CORE4.Case2CountSetup

namespace Work.CORE4

open Subgroup

/-! ## 1. Feit–Thompson in the vocabulary of the development -/

/-- The odd order theorem (`Work.GW2.FeitThompsonProp`), discharged from the ported odd-order
library.  Bender's Lemma 2.8 (`I.lem28`) consumes it. -/
theorem feitThompsonProp_gw : Work.GW2.FeitThompsonProp :=
  fun _ _ _ h => OddOrder.feitThompson h

/-! ## 2. `s ∉ S₀`

The second ingredient, `invSet K (y * s) = invSet K s` for `y ∈ C_G(K)` (inversion subgroups only
depend on the coset modulo the centralizer), is the general library lemma
`Work.CORE4.InvSet.invSet_mul_centralizer`
(`Submission/Work/CORE4/InvSet/invSet_mul_centralizer.lean`, imported above). -/

/-- **The involution `s` of the §4 configuration is not in the cyclic index-two subgroup `S₀`**
(Bender p. 227: `S₀ = C_S(U)`, so `s ∉ S₀`).

If `s ∈ S₀`, then `s = B.t`: both have order `2` and lie in the cyclic group `S₀`, which has a
unique element of order two.  But `U ≤ H = C_G(t)`, so `t` centralizes `U ⊇ U ⊓ M`, whence every
element of `K = I_{U⊓M}(s) = I_{U⊓M}(t)` satisfies `x = x⁻¹`; as `U` has odd order this forces
`x = 1`, i.e. `K = ⊥`, contradicting `K ≠ ⊥` (`Work.CORE4.Case2K1_ne_bot`).

The same fact is available publicly as `Work.CORE4.Case2Data.s_notMem_S0`
(`Submission/Work/CORE4/Case2Numeric.lean`, proved); it is reproduced here so that this module —
which is a leaf of §4 (8) and is consumed by the design-9 chain — depends on the §4 (1)–(6) data
and `Case2K1_ne_bot` alone, and not on the whole §4 (7)–(9) file `Case2Numeric`. -/
private theorem s_notMem_S0 (I : Work.GW2.C4Inputs) {G : Type} [Group G] [Finite G]
    {B : Work.GW2.BenderSetup G} (hbc : Work.GW2.BenderCtx G) (h : Work.GW2.Case2Ctx B) :
    h.D.s ∉ B.S0 := by
  intro hs
  haveI : IsCyclic ↥B.S0 := B.S0_cyclic
  have hle_s : Subgroup.zpowers h.D.s ≤ B.S0 := Subgroup.zpowers_le.mpr hs
  have hle_t : Subgroup.zpowers B.t ≤ B.S0 := Subgroup.zpowers_le.mpr B.t_mem
  have hcard_s : Nat.card ↥(Subgroup.zpowers h.D.s) = 2 := by
    rw [Nat.card_zpowers]; exact h.D.s_order
  have hcard_t : Nat.card ↥(Subgroup.zpowers B.t) = 2 := by
    rw [Nat.card_zpowers]; exact B.t_order
  have heq : (Subgroup.zpowers h.D.s).subgroupOf B.S0 =
      (Subgroup.zpowers B.t).subgroupOf B.S0 := by
    refine IsCyclic.subgroup_eq_iff_card_eq.mpr ?_
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle_s).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle_t).toEquiv, hcard_s, hcard_t]
  have heq' : Subgroup.zpowers h.D.s = Subgroup.zpowers B.t := by
    have hmap := congrArg (Subgroup.map (B.S0).subtype) heq
    rwa [Subgroup.map_subgroupOf_eq_of_le hle_s, Subgroup.map_subgroupOf_eq_of_le hle_t] at hmap
  -- `t` centralizes `U` (as `U ≤ H = C_G(t)`), hence so does every element of `⟨t⟩ ∋ s`
  have htC : B.t ∈ Subgroup.centralizer ((B.U : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact ((Subgroup.mem_centralizer_iff.mp (B.U_le_H hu)) B.t (Set.mem_singleton B.t)).symm
  have hsC : h.D.s ∈ Subgroup.centralizer ((B.U : Subgroup G) : Set G) := by
    refine Subgroup.zpowers_le.mpr htC ?_
    rw [← heq']; exact Subgroup.mem_zpowers _
  have hKbot : h.D.K = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    have hxinv : x ∈ Work.GW2.invSet (B.U ⊓ h.D.M) h.D.s := by
      rw [← h.D.K_def]; exact hx
    obtain ⟨-, hinv⟩ := hxinv
    have hxU : x ∈ B.U := (Subgroup.mem_inf.mp ((h.D.K_le B) hx)).1
    have hfix : h.D.s * x * h.D.s⁻¹ = x := by
      have hc := (Subgroup.mem_centralizer_iff.mp hsC) x hxU
      rw [hc.symm, mul_assoc, mul_inv_cancel, mul_one]
    rw [hfix] at hinv
    have hx2 : x * x = 1 := by
      nth_rewrite 2 [hinv]
      exact mul_inv_cancel x
    have hx1 : orderOf x ∣ 2 := by
      rw [orderOf_dvd_iff_pow_eq_one, pow_two]; exact hx2
    have hodd : Odd (orderOf x) :=
      Odd.of_dvd_nat B.U_odd (Subgroup.orderOf_dvd_natCard B.U hxU)
    rcases (Nat.dvd_prime Nat.prime_two).mp hx1 with h1 | h1
    · exact orderOf_eq_one_iff.mp h1
    · rw [h1] at hodd; exact absurd hodd (by decide)
  have hne := Work.CORE4.Case2K1_ne_bot I hbc h
  rw [hKbot] at hne
  simpa using hne

/-! ## 3. The exceptional clause of §4 (8) does not occur -/

/-- Bender 1981, §4 (8), the exceptional clause: `I_U(s) ⊲ Ĥ` cannot occur, given
`S₀ ≤ C_G(U)` (Bender p. 227: `S₀ = C_S(U)`).

Here `Case2InvNormal B D` is the design-pass-9 reading of Bender's exception
`I_U(s) ⊲ Ĥ`, i.e. `∃ I, (I : Set G) = invSet B.U D.s ∧ I ≤ B.Hhat ∧
(I.subgroupOf B.Hhat).Normal`.

Route (design pass 9 §1, as recorded in `Defs.lean`): by Bender's Lemma 2.8
(`I.lem28 : Lemma28Prop`), if every inversion subgroup `I_U(s')` (`s' ∈ S ∖ S₀`) were normal in
`U`, then `[S₀, U] ≠ ⊥`.  So `S₀ ≤ C_G(U)` (the hypothesis) gives some `s' ∈ S ∖ S₀` such that
*every* subgroup `I` with `(I : Set G) = invSet B.U s'` fails to be normal in `U`.  Since
`S = S₀ ⊔ ⟨D.s⟩` (`D.s ∉ S₀`, because `s ∈ S₀` would force `s = B.t`, the unique involution of the
cyclic `S₀`, and then `K = I_{U⊓M}(t) = ⊥` as `U ⊓ M ≤ C_G(t)`, contradicting `K ≠ ⊥` from
`Submission.Work.CORE4.Case2K1_ne_bot`) and `S₀ ≤ C_G(U)`, one may take `s' = y·D.s` with
`y ∈ S₀`, so that `invSet B.U s' = invSet B.U D.s`.  Hence a witness `I` of `Case2InvNormal`
(`I ≤ Ĥ`, `I ⊴ Ĥ`) would be normal in `U` (as `I ≤ B.U ≤ Ĥ`), a contradiction. -/
theorem Case2NotInvNormal :
    ∀ (G : Type) [Group G] [Finite G] (I : Work.GW2.C4Inputs), Work.GW2.BenderCtx G →
      ∀ (B : Work.GW2.BenderSetup G) (h : Work.GW2.Case2Ctx B),
        B.S0 ≤ Subgroup.centralizer ((B.U : Subgroup G) : Set G) →
        ¬ Work.GW2.Case2InvNormal B h.D := by
  intro G _ _ I hbc B h hS0
  rintro ⟨J, hJinv, hJHhat, hJnorm⟩
  have hFT : Work.GW2.FeitThompsonProp := feitThompsonProp_gw
  have hsS : h.D.s ∈ (B.S : Subgroup G) := (Subgroup.mem_inf.mp h.D.s_mem).1
  have hidx : (B.S0.subgroupOf (B.S : Subgroup G)).index = 2 := by
    simpa [Subgroup.relIndex] using B.S0_index
  have hnotin : h.D.s ∉ B.S0 := s_notMem_S0 I hbc h
  -- the commutator hypothesis of Bender's Lemma 2.8 is satisfied
  have hcomm : ⁅B.S0, B.U⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hS0
  -- the witness `J` is a subgroup of `U` normal in `Ĥ`, hence normal in `U`
  have hJleU : J ≤ B.U := by
    intro x hx
    have hx' : x ∈ Work.GW2.invSet B.U h.D.s := by rw [← hJinv]; exact hx
    exact hx'.1
  have hJleHhat : J ≤ B.Hhat := le_trans hJleU (le_trans B.U_le_H B.H_le_Hhat)
  have hJnormU : (J.subgroupOf B.U).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hJleU]
    intro a b ha hb
    exact (Subgroup.normal_subgroupOf_iff hJleHhat).mp hJnorm a b ha
      (le_trans B.U_le_H B.H_le_Hhat hb)
  -- every inversion subgroup `invSet B.U s'`, `s' ∈ S ∖ S₀`, is normal in `U`
  have hpre : ∀ s ∈ (B.S : Subgroup G), s ∉ B.S0 →
      ∃ J' : Subgroup G, (J' : Set G) = Work.GW2.invSet B.U s ∧ (J'.subgroupOf B.U).Normal := by
    intro s hsS' hs0'
    -- `y := s * D.s⁻¹ ∈ S₀`, because `S₀` has index two in `S` and both `s`, `D.s` lie outside
    have hnotin' : h.D.s⁻¹ ∉ B.S0 := fun hc => hnotin (by simpa using B.S0.inv_mem hc)
    have hy_mem : (⟨s, hsS'⟩ : ↥(B.S : Subgroup G)) * (⟨h.D.s, hsS⟩ : ↥(B.S : Subgroup G))⁻¹ ∈
        B.S0.subgroupOf (B.S : Subgroup G) := by
      rw [Subgroup.mul_mem_iff_of_index_two (H := B.S0.subgroupOf (B.S : Subgroup G)) hidx]
      exact iff_of_false (by simpa [Subgroup.mem_subgroupOf] using hs0')
        (by simpa [Subgroup.mem_subgroupOf] using hnotin')
    have hy : s * h.D.s⁻¹ ∈ B.S0 := by
      have := Subgroup.mem_subgroupOf.mp hy_mem
      simpa using this
    -- `y` centralizes `U`, so `invSet B.U s = invSet B.U (y * D.s) = invSet B.U D.s`
    have hyC : s * h.D.s⁻¹ ∈ Subgroup.centralizer ((B.U : Subgroup G) : Set G) := hS0 hy
    have hs_eq : s = (s * h.D.s⁻¹) * h.D.s := by group
    refine ⟨J, ?_, hJnormU⟩
    rw [hJinv, hs_eq]
    exact (InvSet.invSet_mul_centralizer hyC).symm
  -- Bender's Lemma 2.8 contradicts `[S₀, U] = 1`
  exact (I.lem28 G hFT hbc B hpre).1 hcomm

end Work.CORE4
