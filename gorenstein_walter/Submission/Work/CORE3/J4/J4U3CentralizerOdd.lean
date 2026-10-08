import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.FourGroupOrderThreeFixed
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.CORE3.J4.EqOneOfCommuteOrderThreeCardSix
import Submission.Work.CORE3.J4.MemLeftOfSupOfSqEqOne

/-!
# `Work.CORE3.J4.J4U3CentralizerOdd`

Bender 1981, §3 (the `(2,2)` subcase of Case (1) of Theorem 2.10).  With `V = O₂(Ĥ)`,
`U = O(Ĥ)`, `VU = V ⊔ U`, `Ĥ/VU` has order `6` and is *not* a `C₆`
(`Work.GW2.Thm26Concl`), hence is nonabelian.

For `x ∈ Ĥ` of order `3` with `x ∉ VU`, the centralizer `C_Ĥ(x)` has odd order:  an involution
`g ∈ C_Ĥ(x)` has image in `Ĥ/VU` of order dividing both `2` and the odd order `3` of the
centralizer of (the order-`3` element) `xVU`, so `g ∈ VU`; the `2`-part of `VU` is `V`, and
`V ⊓ C_Ĥ(x) = ⊥` because `x ∉ VU = C_Ĥ(V)` acts fixed-point-freely on the four-group `V`.

The two group-theoretic inputs are proved in the sibling modules
`Work.CORE3.J4.EqOneOfCommuteOrderThreeCardSix` (no involution of a nonabelian group of order
`6` commutes with an element of order `3`) and
`Work.CORE3.J4.MemLeftOfSupOfSqEqOne` (the `2`-part of a split product `A ⊔ B` with `|B|` odd
lies in `A`).
-/

namespace Work.CORE3.J4

open Subgroup

set_option linter.unusedVariables false
set_option linter.style.haveILetI false

theorem J4U3CentralizerOdd {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {x : G} (hxH : x ∈ B.Hhat) (hx3 : orderOf x = 3)
    (hxVU : x ∉ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U)) :
    Odd (Nat.card ↥(Subgroup.centralizer ({x} : Set G) ⊓ B.Hhat)) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  -- ### Bender's Theorem 2.6, and `C_Ĥ(V) = VU`
  have h26 : Work.GW2.Thm26Concl B := I.h26 G I.T.ft hBc B
  have hcent : Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) ⊓ B.Hhat
      = Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U :=
    Work.CORE3.CentralizerPcoreEqVU G I hBc B h1 D
  have hrel : (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 :=
    Work.CORE3.relIndex_VU_Hhat G I hBc B h1 D
  have hV4 : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat) := D.four
  -- ### `Ĥ` normalizes `V` and `U`
  have hVnorm : B.Hhat ≤
      Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
    simpa [Work.GW2.pCoreIn] using
      Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.pCore 2 ↥B.Hhat)
  have hUnorm : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
    have h : B.Hhat ≤ Subgroup.normalizer ((Work.GW2.oddCoreIn B.Hhat : Subgroup G) : Set G) :=
      Work.CORE3.le_normalizer_map_subtype B.Hhat (Work.GW2.oddCore ↥B.Hhat)
    rwa [Work.CORE2A.thm26Concl_oddCore_eq h26] at h
  -- ### `x` normalizes, but does not centralize, `V`
  have hxN : x ∈ Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) :=
    hVnorm hxH
  have hxnc : x ∉ Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
    intro hxc
    apply hxVU
    have hmem : x ∈ Subgroup.centralizer
        ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) ⊓ B.Hhat :=
      Subgroup.mem_inf.mpr ⟨hxc, hxH⟩
    rwa [hcent] at hmem
  have hVfix : Work.GW2.pCoreIn 2 B.Hhat ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ :=
    Work.CORE3.FourGroupOrderThreeFixed hV4 hxN hx3 hxnc
  -- ### the quotient `Ĥ/VU`
  let N : Subgroup ↥B.Hhat := (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U).subgroupOf B.Hhat
  haveI hNnorm : N.Normal := Work.CORE3.normal_VU_subgroupOf G I hBc B h1 D
  let π : ↥B.Hhat →* (↥B.Hhat ⧸ N) := QuotientGroup.mk' N
  have hQcard : Nat.card (↥B.Hhat ⧸ N) = 6 := by
    rw [← Subgroup.index_eq_card N]
    exact hrel
  -- ### `Ĥ/VU` is nonabelian (Theorem 2.6, third clause)
  have hnonab : ∃ p q : ↥B.Hhat ⧸ N, p * q ≠ q * p := by
    have hwit : ∃ a ∈ B.Hhat, ∃ b ∈ B.Hhat,
        a * b * a⁻¹ * b⁻¹ ∉ (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) := by
      rcases h26.2.2 with ⟨hle, -⟩ | ⟨-, -, hw⟩
      · exact absurd (Work.CORE3.isCyclic_of_le_of_isCyclic' hle B.S0_cyclic)
          (Work.CORE3.not_isCyclic_of_isFourGroup' hV4)
      · exact hw
    obtain ⟨a0, ha0, b0, hb0, hw⟩ := hwit
    refine ⟨π ⟨a0, ha0⟩, π ⟨b0, hb0⟩, fun heq => hw ?_⟩
    have hker_eq : MonoidHom.ker π = N := QuotientGroup.ker_mk' (N := N)
    have hmem : (⟨a0, ha0⟩ * ⟨b0, hb0⟩) * (⟨b0, hb0⟩ * ⟨a0, ha0⟩)⁻¹ ∈ N := by
      rw [← hker_eq, MonoidHom.mem_ker]
      have hker : π (⟨a0, ha0⟩ * ⟨b0, hb0⟩) = π (⟨b0, hb0⟩ * ⟨a0, ha0⟩) := by
        rw [map_mul, map_mul, heq]
      rw [map_mul, map_inv, hker, mul_inv_cancel]
    have hG : (((⟨a0, ha0⟩ * ⟨b0, hb0⟩) * (⟨b0, hb0⟩ * ⟨a0, ha0⟩)⁻¹ : ↥B.Hhat) : G) ∈
        (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) := Subgroup.mem_subgroupOf.mp hmem
    have hcoe : (((⟨a0, ha0⟩ * ⟨b0, hb0⟩) * (⟨b0, hb0⟩ * ⟨a0, ha0⟩)⁻¹ : ↥B.Hhat) : G)
        = a0 * b0 * a0⁻¹ * b0⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_rev]
      group
    rw [hcoe] at hG
    exact hG
  -- ### `x` has order `3` in the quotient
  have hq3 : orderOf (π ⟨x, hxH⟩) = 3 := by
    have hx3' : x ^ 3 = 1 := by rw [← hx3, pow_orderOf_eq_one]
    have hdvd : orderOf (π ⟨x, hxH⟩) ∣ 3 := by
      rw [orderOf_dvd_iff_pow_eq_one]
      have h : (⟨x, hxH⟩ : ↥B.Hhat) ^ 3 = 1 := by
        apply Subtype.ext
        simpa using hx3'
      rw [← map_pow, h, map_one]
    have hne : π ⟨x, hxH⟩ ≠ 1 := by
      intro h1
      have hker_eq : MonoidHom.ker π = N := QuotientGroup.ker_mk' (N := N)
      have hmem : (⟨x, hxH⟩ : ↥B.Hhat) ∈ N := by
        rw [← hker_eq, MonoidHom.mem_ker]
        exact h1
      exact hxVU (Subgroup.mem_subgroupOf.mp hmem)
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (orderOf (π ⟨x, hxH⟩)) hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  -- ### no involution in `C_Ĥ(x)`
  rw [← Nat.not_even_iff_odd]
  intro heven
  obtain ⟨g, hgord⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.centralizer ({x} : Set G) ⊓ B.Hhat))
      2 heven.two_dvd
  have hgC : (g : G) ∈ Subgroup.centralizer ({x} : Set G) := (Subgroup.mem_inf.mp g.2).1
  have hgK : (g : G) ∈ B.Hhat := (Subgroup.mem_inf.mp g.2).2
  have hgordG : orderOf (g : G) = 2 := (Subgroup.orderOf_coe g).trans hgord
  have hgx : (g : G) * x = x * (g : G) := Subgroup.mem_centralizer_singleton_iff.mp hgC
  have hg2 : (g : G) * (g : G) = 1 := by
    have h := pow_orderOf_eq_one (g : G)
    rw [hgordG] at h
    simpa [pow_two] using h
  let gK : ↥B.Hhat := ⟨(g : G), hgK⟩
  have hcomm : π gK * π ⟨x, hxH⟩ = π ⟨x, hxH⟩ * π gK := by
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simpa using hgx
  have hsq : π gK * π gK = 1 := by
    rw [← map_mul]
    have hgKsq : gK * gK = 1 := by
      apply Subtype.ext
      simpa using hg2
    rw [hgKsq, map_one]
  have hpg1 : π gK = 1 :=
    EqOneOfCommuteOrderThreeCardSix hQcard hnonab hq3 hsq hcomm.symm
  have hgW : (g : G) ∈ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U := by
    have hker_eq : MonoidHom.ker π = N := QuotientGroup.ker_mk' (N := N)
    have hmem : gK ∈ N := by
      rw [← hker_eq, MonoidHom.mem_ker]
      exact hpg1
    exact Subgroup.mem_subgroupOf.mp hmem
  -- ### `(g : G)` lies in `V`, hence in `V ⊓ C_Ĥ(x) = ⊥`
  have hUVbot : Work.GW2.pCoreIn 2 B.Hhat ⊓ B.U = ⊥ := by
    apply le_bot_iff.mp
    calc Work.GW2.pCoreIn 2 B.Hhat ⊓ B.U ≤ (B.S : Subgroup G) ⊓ B.U :=
          inf_le_inf (Work.CORE2A.thm26Concl_O2_le_S h26) le_rfl
      _ = ⊥ := by rw [inf_comm]; exact Work.CORE2A.inf_U_S_eq_bot B
  have hVnU : Work.GW2.pCoreIn 2 B.Hhat ≤ Subgroup.normalizer (B.U : Set G) :=
    le_trans (Work.CORE2A.thm26Concl_O2_le_Hhat h26) hUnorm
  have hUnV : B.U ≤ Subgroup.normalizer ((Work.GW2.pCoreIn 2 B.Hhat : Subgroup G) : Set G) :=
    le_trans (Work.CORE2A.thm26Concl_U_le_Hhat h26) hVnorm
  have hgV : (g : G) ∈ Work.GW2.pCoreIn 2 B.Hhat :=
    MemLeftOfSupOfSqEqOne hUVbot hVnU hUnV (Work.CORE2A.bSetup_U_odd B) hgW hg2
  have hg1 : (g : G) = 1 := by
    have hmem : (g : G) ∈ (⊥ : Subgroup G) := by
      rw [← hVfix]
      exact ⟨hgV, hgC⟩
    exact Subgroup.mem_bot.mp hmem
  have hgone : g = 1 := Subtype.ext (by simpa using hg1)
  rw [hgone, orderOf_one] at hgord
  exact absurd hgord (by norm_num)

end Work.CORE3.J4
