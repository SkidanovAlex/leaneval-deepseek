import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1bDStructure
import Submission.Work.CORE3.J4.VUInvSetTrivial
import Submission.Work.CORE3.FourGroupOrderThreeFixed
import Submission.Work.CORE3.OrderThreeLeCentralizer
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.CentralizerPcoreEqVU
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.Case1bFalse
import Submission.Work.CORE3.CosetInvCountBasic
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.InvSetVUSingleton
import Submission.Work.CORE3.card_le_eight_of_isPGroup_two_le_Hhat
import Submission.Work.CORE3.DihedralFourNotCommutative
import Submission.Work.CORE2A.Basic
import Submission.Work.BSW.Cases.K4.CardSup

/-!
# `J4DTriv`: the stabilizer of a `J₄`-coset in `VU` is trivial

Bender 1981, §3, step (7) for a `J₄`-coset: if `y ∉ Ĥ` is an involution whose coset carries
exactly four involutions and which inverts an odd-order subgroup `X ≤ Ĥ`, and if `|U| = 3`
(`U = O(Ĥ)`), then `VU ⊓ (Ĥ ⊓ Ĥ^y) = ⊥`, where `VU = O₂(Ĥ) ⊔ O(Ĥ)`.
-/

namespace Work.CORE3.J4

open Subgroup

set_option linter.unusedVariables false

namespace J4DTrivAux

variable {G : Type} [Group G] [Finite G]

/-- An element of order two is its own inverse. -/
theorem inv_eq_self_of_orderOf_two {y : G} (h : orderOf y = 2) : y⁻¹ = y :=
  inv_eq_of_mul_eq_one_left ((orderOf_eq_two_iff_mul_self y).mp h).1

/-- Every non-trivial element of a subgroup of order `3` has order `3`. -/
theorem orderOf_eq_three_of_mem_card_three {A : Subgroup G} (hA : Nat.card A = 3)
    {x : G} (hx : x ∈ A) (hx1 : x ≠ 1) : orderOf x = 3 := by
  have hdvd : orderOf x ∣ 3 := by
    rw [← hA]; exact Subgroup.orderOf_dvd_natCard A hx
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hx1
  · exact h

/-- A non-trivial subgroup of a group of order `3` is the whole group. -/
theorem eq_of_le_of_card_eq_three {A U : Subgroup G} (hAU : A ≤ U) (hU : Nat.card U = 3)
    (hA : A ≠ ⊥) : A = U := by
  have hdvd : Nat.card A ∣ 3 := by rw [← hU]; exact Subgroup.card_dvd_of_le hAU
  have hne1 : Nat.card A ≠ 1 := by
    intro h
    exact hA (Work.BSW.Cases.K4.eq_bot_of_card_eq_one h)
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd h hne1
  · exact Subgroup.eq_of_le_of_card_ge hAU (le_of_eq (by rw [h, hU]))

/-- **Product formula for the join.**  If `A ⊴ G` then
`|A ⊔ B| * |A ⊓ B| = |A| * |B|`. -/
theorem card_sup_mul_card_inf_of_normal {A B : Subgroup G} (hA : A.Normal) :
    Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card ↥A * Nat.card ↥B := by
  have hnorm : (A.subgroupOf (⊤ : Subgroup G)).Normal := hA.subgroupOf ⊤
  have h1 : A.relIndex (B ⊔ A) = (A ⊓ B).relIndex B :=
    Work.CORE3.relIndex_sup_eq_inf_relIndex ⊤ A B le_top le_top hnorm
  rw [sup_comm] at h1
  have h2 := Subgroup.relIndex_mul_card A (B ⊔ A)
  rw [inf_eq_left.mpr le_sup_right] at h2
  rw [sup_comm] at h2
  have h3 := Subgroup.relIndex_mul_card (A ⊓ B) B
  rw [inf_eq_left.mpr inf_le_right] at h3
  rw [h1] at h2
  calc Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B)
      = ((A ⊓ B).relIndex B * Nat.card ↥A) * Nat.card ↥(A ⊓ B) := by rw [h2]
    _ = ((A ⊓ B).relIndex B * Nat.card ↥(A ⊓ B)) * Nat.card ↥A := by ring
    _ = Nat.card ↥B * Nat.card ↥A := by rw [h3]
    _ = Nat.card ↥A * Nat.card ↥B := by ring

/-- In a group of order `18`, two subgroups of order `9` are equal (they are the unique
Sylow `3`-subgroup). -/
theorem card_eq_nine_eq_of_card_eighteen {Q : Type} [Group Q] [Finite Q]
    (hQ : Nat.card Q = 18) {A B : Subgroup Q} (hA : Nat.card A = 9) (hB : Nat.card B = 9) :
    A = B := by
  have hidx : A.index = 2 := by
    rw [Subgroup.index_eq_card_div, hA, hQ]
  have hAn : A.Normal := Subgroup.normal_of_index_eq_two hidx
  have hmain : Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = 81 := by
    rw [card_sup_mul_card_inf_of_normal (A := A) (B := B) hAn, hA, hB]
  have hle : Nat.card ↥(A ⊔ B) ≤ 18 := by
    have h := Subgroup.card_dvd_of_le (H := A ⊔ B) (K := (⊤ : Subgroup Q)) le_top
    rw [Subgroup.card_top, hQ] at h
    exact Nat.le_of_dvd (by norm_num) h
  have hdiv : Nat.card ↥(A ⊓ B) ∣ 9 := by
    rw [← hA]; exact Subgroup.card_dvd_of_le inf_le_left
  have hge : 5 ≤ Nat.card ↥(A ⊓ B) := by
    rcases Nat.lt_or_ge (Nat.card ↥(A ⊓ B)) 5 with h | h
    · exfalso
      have h2 : Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) ≤ 18 * 4 :=
        Nat.mul_le_mul hle (Nat.lt_succ_iff.mp h)
      rw [hmain] at h2
      exact absurd h2 (by norm_num)
    · exact h
  obtain ⟨k, hk⟩ := hdiv
  have hcard : Nat.card ↥(A ⊓ B) = 9 := by
    have hk0 : k ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hk; exact absurd hk (by norm_num)
    have hle1 : k ≤ 1 := by
      by_contra h
      have h2 : 2 ≤ k := Nat.succ_le_of_lt (not_le.mp h)
      nlinarith [hge, hk]
    have hk1 : k = 1 := by omega
    have hb : Nat.card ↥(A ⊓ B) * k = 9 := hk.symm
    rw [hk1, mul_one] at hb
    exact hb
  have hAeq : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hcard, hA])
  have hAB : A ≤ B := by rw [← hAeq]; exact inf_le_right
  exact Subgroup.eq_of_le_of_card_ge hAB (by rw [hA, hB])

/-- The same, for two subgroups of `G` lying in a subgroup of order `18`. -/
theorem card_eq_nine_eq_of_le_card_eighteen {Q A B : Subgroup G} (hQ : Nat.card Q = 18)
    (hA : A ≤ Q) (hB : B ≤ Q) (hAc : Nat.card A = 9) (hBc : Nat.card B = 9) : A = B := by
  have hcardQ : Nat.card ↥Q = 18 := hQ
  have hA' : Nat.card ↥(A.subgroupOf Q) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA).toEquiv, hAc]
  have hB' : Nat.card ↥(B.subgroupOf Q) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB).toEquiv, hBc]
  have hEq : A.subgroupOf Q = B.subgroupOf Q :=
    card_eq_nine_eq_of_card_eighteen hcardQ hA' hB'
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have hmem : (⟨x, hA hx⟩ : ↥Q) ∈ A.subgroupOf Q := Subgroup.mem_subgroupOf.mpr hx
    rw [hEq] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  · have hmem : (⟨x, hB hx⟩ : ↥Q) ∈ B.subgroupOf Q := Subgroup.mem_subgroupOf.mpr hx
    rw [← hEq] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem

end J4DTrivAux

theorem J4DTriv {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (hy4 : Work.GW2.cosetInvCount B.Hhat y = 4)
    {X : Subgroup G} (hXH : X ≤ B.Hhat) (hX1 : X ≠ ⊥) (hXodd : Odd (Nat.card X))
    (hinv : Work.GW2.Inverts y X)
    (hC : Even (Nat.card (Subgroup.centralizer (X : Set G))))
    (hN : Even (Nat.card (Subgroup.normalizer (X : Set G))))
    (hU3 : Nat.card B.U = 3) :
    (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) ⊓ (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat) = ⊥ := by
  classical
  have hy1 : y * y = 1 := ((orderOf_eq_two_iff_mul_self y).mp hy2).1
  have hyinv : y⁻¹ = y := J4DTrivAux.inv_eq_self_of_orderOf_two hy2
  -- ### The subgroups `V = O₂(Ĥ)`, `U = O(Ĥ)`, `VU`, `D = Ĥ ⊓ Ĥ^y`
  set V : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat with hV
  set Uu : Subgroup G := B.U with hU
  set VU : Subgroup G := V ⊔ Uu with hVU
  set DD : Subgroup G := B.Hhat ⊓ Work.GW2.conjSub y B.Hhat with hDD
  have h26 : Work.GW2.Thm26Concl B := I.h26 G I.T.ft hBc B
  have hVpS : Work.GW2.pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) :=
    Work.CORE2A.thm26Concl_O2_le_S h26
  have hVleHhat : V ≤ B.Hhat := by
    rw [hV]; exact Work.CORE2A.thm26Concl_O2_le_Hhat h26
  have hUleHhat : Uu ≤ B.Hhat := by
    rw [hU]; exact Work.CORE2A.thm26Concl_U_le_Hhat h26
  have hVUleHhat : VU ≤ B.Hhat := by
    rw [hVU]; exact sup_le hVleHhat hUleHhat
  have hVS : V ≤ (B.S : Subgroup G) := by rw [hV]; exact hVpS
  have hV4 : Work.GW2.IsFourGroup V := by rw [hV]; exact D.four
  have hVcard : Nat.card V = 4 := hV4.1
  have hVsq : ∀ v ∈ V, v ^ 2 = 1 := hV4.2
  have hUcard : Nat.card Uu = 3 := by rw [hU]; exact hU3
  have hVUdisj : V ⊓ Uu = ⊥ := by
    refine le_bot_iff.mp ?_
    rw [hV, hU]
    calc Work.GW2.pCoreIn 2 B.Hhat ⊓ B.U ≤ (B.S : Subgroup G) ⊓ B.U :=
          inf_le_inf hVpS le_rfl
      _ = ⊥ := by rw [inf_comm]; exact Work.CORE2A.inf_U_S_eq_bot B
  have hVnorm : B.Hhat ≤ Subgroup.normalizer (V : Set G) := by
    rw [hV]
    exact le_of_eq (Work.CORE3.NormalizerPcoreEqHhat G hBc B D.four).symm
  have hUnorm : B.Hhat ≤ Subgroup.normalizer (Uu : Set G) := by
    rw [hU]
    have h := Work.CORE3.le_normalizer_map_subtype_of_normal'
      (K := B.Hhat) (N := Work.GW2.oddCore ↥B.Hhat) inferInstance
    have heq : (Work.GW2.oddCore ↥B.Hhat).map B.Hhat.subtype = B.U := by
      simpa [Work.GW2.oddCoreIn] using Work.CORE2A.thm26Concl_oddCore_eq h26
    rwa [heq] at h
  have hVUnorm : B.Hhat ≤ Subgroup.normalizer (VU : Set G) := by
    rw [hVU]
    exact le_trans (le_inf hVnorm hUnorm)
      (Subgroup.inf_normalizer_le_normalizer_sup V Uu)
  have hVUcard : Nat.card VU = 12 := by
    have h := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot (H := V) (K := Uu)
      (le_trans hUleHhat hVnorm) hVUdisj
    rw [h]
    rw [hVcard, hUcard]
  have hHhatcard : Nat.card B.Hhat = 72 := by
    have h := Subgroup.relIndex_mul_card (H := VU) (K := B.Hhat)
    rw [inf_eq_left.mpr hVUleHhat] at h
    have hrel : VU.relIndex B.Hhat = 6 := by
      rw [hVU]; exact Work.CORE3.relIndex_VU_Hhat G I hBc B h1 D
    rw [hrel, hVUcard] at h
    norm_num at h
    exact h.symm
  -- `V` and `U` commute (elementwise): `VU` is abelian
  have hcommVU : ∀ v ∈ V, ∀ u ∈ Uu, v * u = u * v := by
    intro v hv u hu
    have h1 : v * u * v⁻¹ * u⁻¹ ∈ Uu :=
      Uu.mul_mem ((Subgroup.mem_normalizer_iff.mp (hUnorm (hVleHhat hv)) u).mp hu)
        (Uu.inv_mem hu)
    have h2 : v * u * v⁻¹ * u⁻¹ ∈ V := by
      have h3 : u * v⁻¹ * u⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.mp (hVnorm (hUleHhat hu)) v⁻¹).mp (V.inv_mem hv)
      have h4 : v * (u * v⁻¹ * u⁻¹) ∈ V := V.mul_mem hv h3
      simpa [mul_assoc] using h4
    have h5 : v * u * v⁻¹ * u⁻¹ = 1 := by
      have hmem : v * u * v⁻¹ * u⁻¹ ∈ V ⊓ Uu := ⟨h2, h1⟩
      rw [hVUdisj] at hmem
      exact Subgroup.mem_bot.mp hmem
    have h6 : (v * u) * (u * v)⁻¹ = 1 := by
      rw [mul_inv_rev]
      simpa [mul_assoc] using h5
    exact mul_inv_eq_one.mp h6
  -- ### the structure of `D`
  obtain ⟨hDsup', hDrel', hDinv'⟩ :=
    Work.CORE3.Case1bDStructure G I hBc B h1 D y hy2 hyH (le_of_eq hy4.symm)
  have hDsup : DD ⊔ VU = B.Hhat := by
    rw [hDD, hVU]; exact hDsup'
  have hDrel : (VU ⊓ DD).relIndex DD = 6 := by
    rw [hDD, hVU]; exact hDrel'
  have hIleD : Work.CORE3.invSetIn B.Hhat y ⊆ DD := by
    rw [hDD]; exact hDinv'
  have hIcard : (Work.CORE3.invSetIn B.Hhat y).ncard = 4 := by
    rw [Work.CORE3.ncard_invSetIn_eq_cosetInvCount B.Hhat y hy1 hyH, hy4]
  -- `y` normalizes `D`
  have hyDD : Work.GW2.conjSub y DD = DD := by
    show (B.Hhat ⊓ Work.GW2.conjSub y B.Hhat).map (MulAut.conj y).toMonoidHom =
      B.Hhat ⊓ Work.GW2.conjSub y B.Hhat
    rw [Subgroup.map_inf B.Hhat (Work.GW2.conjSub y B.Hhat) (MulAut.conj y).toMonoidHom
      (MulAut.conj y).injective]
    have h2 : (Work.GW2.conjSub y B.Hhat).map (MulAut.conj y).toMonoidHom = B.Hhat := by
      show (B.Hhat.map (MulAut.conj y).toMonoidHom).map (MulAut.conj y).toMonoidHom = B.Hhat
      rw [Subgroup.map_map]
      have hcomp : (MulAut.conj y).toMonoidHom.comp (MulAut.conj y).toMonoidHom =
          MonoidHom.id G := by
        ext x
        show y * (y * x * y⁻¹) * y⁻¹ = x
        rw [show y * (y * x * y⁻¹) * y⁻¹ = (y * y) * x * (y⁻¹ * y⁻¹) by group, hy1,
          show y⁻¹ * y⁻¹ = 1 by rw [← mul_inv_rev, hy1, inv_one], mul_one, one_mul]
      rw [hcomp]
      exact Subgroup.map_id B.Hhat
    rw [h2]
    exact inf_comm _ _
  -- ### `X ≤ D` and its basic properties
  have hXleD : X ≤ DD := by
    intro x hx
    refine ⟨hXH hx, ?_⟩
    show x ∈ Work.GW2.conjSub y B.Hhat
    rw [Work.CORE2A.mem_conjSub_iff]
    have h : y⁻¹ * x * y = x⁻¹ := by simpa [hyinv] using hinv x hx
    rw [h]
    exact B.Hhat.inv_mem (hXH hx)
  have hXVUdisj : X ⊓ VU = ⊥ := by
    refine le_bot_iff.mp ?_
    intro x hx
    rw [Subgroup.mem_inf] at hx
    obtain ⟨hxX, hxVU⟩ := hx
    have h5 : Work.GW2.invSet VU y = {1} := by
      rw [hVU]; exact Work.CORE3.J4.VUInvSetTrivial I hBc B h1 D y hy2 hyH
    have hmem : x ∈ Work.GW2.invSet VU y := by
      refine ⟨hxVU, ?_⟩
      simpa [hyinv] using hinv x hxX
    rw [h5] at hmem
    rw [Subgroup.mem_bot]
    exact hmem
  have hXcard : Nat.card X = 3 := by
    have h := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot (H := VU) (K := X)
      (le_trans hXH hVUnorm) (by rw [inf_comm]; exact hXVUdisj)
    have hle : VU ⊔ X ≤ B.Hhat := sup_le hVUleHhat hXH
    have hdvd : 12 * Nat.card X ∣ 72 := by
      have h2 : Nat.card ↥(VU ⊔ X) ∣ Nat.card B.Hhat := Subgroup.card_dvd_of_le hle
      rw [hHhatcard] at h2
      rwa [h, hVUcard] at h2
    have hdvd6 : Nat.card X ∣ 6 := by
      have h3 : 12 * Nat.card X ∣ 12 * 6 := by
        rw [show (12 * 6 : ℕ) = 72 by norm_num]; exact hdvd
      exact (Nat.mul_dvd_mul_iff_left (by norm_num : 0 < 12)).mp h3
    have hcop : Nat.Coprime (Nat.card X) 2 := Nat.coprime_two_right.mpr hXodd
    have h3 : Nat.card X ∣ 3 := by
      have h4 : Nat.card X ∣ 2 * 3 := by norm_num at hdvd6 ⊢; exact hdvd6
      exact Nat.Coprime.dvd_of_dvd_mul_left hcop h4
    have hne1 : Nat.card X ≠ 1 := by
      intro h1
      exact hX1 (Work.BSW.Cases.K4.eq_bot_of_card_eq_one h1)
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h1
    · exact absurd h1 hne1
    · exact h1
  have hXord : ∀ x ∈ X, x ≠ 1 → orderOf x = 3 := fun x hx hx1 =>
    J4DTrivAux.orderOf_eq_three_of_mem_card_three hXcard hx hx1
  have hXnormV : X ≤ Subgroup.normalizer (V : Set G) := by
    rw [hV, Work.CORE3.NormalizerPcoreEqHhat G hBc B D.four]
    exact hXH
  have hFixFree : ∀ x ∈ X, x ≠ 1 → V ⊓ Subgroup.centralizer ({x} : Set G) = ⊥ := by
    intro x hx hx1
    have hx3 := hXord x hx hx1
    have hxN : x ∈ Subgroup.normalizer (V : Set G) := hXnormV hx
    have hxnc : x ∉ Subgroup.centralizer (V : Set G) := by
      intro hxc
      have hxVU : x ∈ VU := by
        rw [hVU, hV, hU, ← Work.CORE3.CentralizerPcoreEqVU G I hBc B h1 D]
        exact ⟨hxc, hXH hx⟩
      have h2 : x ∈ X ⊓ VU := ⟨hx, hxVU⟩
      rw [hXVUdisj] at h2
      exact hx1 (Subgroup.mem_bot.mp h2)
    exact Work.CORE3.FourGroupOrderThreeFixed hV4 hxN hx3 hxnc
  -- ### `X` acts transitively on `V^♯`
  have htransV : ∀ v ∈ V, v ≠ 1 → ∀ w ∈ V, w ≠ 1 → ∃ x ∈ X, x * v * x⁻¹ = w := by
    intro v hv hv1 w hw hw1
    have hact : ∀ x ∈ X, ∀ u ∈ V, x * u * x⁻¹ ∈ V := fun x hx u hu =>
      (Subgroup.mem_normalizer_iff.mp (hXnormV hx) u).mp hu
    have hXVc : X ⊓ Subgroup.centralizer ({v} : Set G) = ⊥ := by
      refine le_bot_iff.mp ?_
      intro y hy
      rw [Subgroup.mem_inf] at hy
      obtain ⟨hyX, hyc⟩ := hy
      by_contra hy1
      have hvmem : v ∈ V ⊓ Subgroup.centralizer ({y} : Set G) := by
        refine ⟨hv, ?_⟩
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact ((Subgroup.mem_centralizer_iff.mp hyc) v (by simp)).symm
      rw [hFixFree y hyX hy1] at hvmem
      exact hv1 (Subgroup.mem_bot.mp hvmem)
    have hinj : ∀ x ∈ X, ∀ x' ∈ X, x * v * x⁻¹ = x' * v * x'⁻¹ → x = x' := by
      intro x hx x' hx' heq
      have hmem : x'⁻¹ * x ∈ X ⊓ Subgroup.centralizer ({v} : Set G) := by
        refine ⟨X.mul_mem (X.inv_mem hx') hx, ?_⟩
        refine Subgroup.mem_centralizer_iff.mpr ?_
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        rw [hz]
        exact (calc (x'⁻¹ * x) * v = x'⁻¹ * (x * v) := by group
          _ = x'⁻¹ * (x * v * x⁻¹) * x := by group
          _ = x'⁻¹ * (x' * v * x'⁻¹) * x := by rw [heq]
          _ = v * (x'⁻¹ * x) := by group).symm
      rw [hXVc] at hmem
      have h1 : x'⁻¹ * x = 1 := Subgroup.mem_bot.mp hmem
      have h2 : x' = x := inv_mul_eq_one.mp h1
      exact h2.symm
    have hImSub : (X : Set G).image (fun x => x * v * x⁻¹) ⊆ (V : Set G) \ {1} := by
      rintro _ ⟨x, hxX, rfl⟩
      refine ⟨hact x hxX v hv, ?_⟩
      simp only [Set.mem_singleton_iff]
      intro hcon
      exact hv1 (by
        have h' := congrArg (fun z => x⁻¹ * z * x) hcon
        simpa [mul_assoc] using h')
    have hImcard : ((X : Set G).image (fun x => x * v * x⁻¹)).ncard = 3 := by
      have hinjOn : Set.InjOn (fun x => x * v * x⁻¹) (X : Set G) :=
        fun x hx x' hx' heq => hinj x hx x' hx' heq
      have hc : (X : Set G).ncard = Nat.card X := (Nat.card_coe_set_eq (X : Set G)).symm
      rw [hinjOn.ncard_image, hc, hXcard]
    have hVsharp : ((V : Set G) \ {1}).ncard = 3 := by
      have hc : (V : Set G).ncard = Nat.card V := (Nat.card_coe_set_eq (V : Set G)).symm
      rw [Set.ncard_sdiff_singleton_of_mem (V.one_mem), hc, hVcard]
    have hEq : (X : Set G).image (fun x => x * v * x⁻¹) = (V : Set G) \ {1} :=
      Set.eq_of_subset_of_ncard_le hImSub (by rw [hImcard, hVsharp]) (Set.toFinite _)
    have hwmem : w ∈ (X : Set G).image (fun x => x * v * x⁻¹) := by
      rw [hEq]; exact ⟨hw, hw1⟩
    obtain ⟨x, hxX, hxw⟩ := hwmem
    exact ⟨x, hxX, hxw⟩
  -- ### Case 1: `V ⊓ D ≠ ⊥` is impossible
  have hVnorm'' : ∀ s ∈ B.Hhat, ∀ v ∈ V, s * v * s⁻¹ ∈ V :=
    fun s hs v hv => (Subgroup.mem_normalizer_iff.mp (hVnorm hs) v).mp hv
  have hUnorm'' : ∀ s ∈ B.Hhat, ∀ u ∈ Uu, s * u * s⁻¹ ∈ Uu :=
    fun s hs u hu => (Subgroup.mem_normalizer_iff.mp (hUnorm hs) u).mp hu
  have case1 : V ⊓ DD ≠ ⊥ → False := by
    intro hne
    obtain ⟨z, hzmem, hz1⟩ : ∃ z ∈ V ⊓ DD, z ≠ 1 := by
      by_contra hcon
      push_neg at hcon
      refine hne ((Subgroup.eq_bot_iff_forall (V ⊓ DD)).mpr ?_)
      intro z hz
      exact hcon z hz
    have hzv : z ∈ V := hzmem.1
    have hzD : z ∈ DD := hzmem.2
    have hVleD : V ≤ DD := by
      intro w hw
      by_cases hw1 : w = 1
      · rw [hw1]; exact DD.one_mem
      · obtain ⟨x, hxX, hxw⟩ := htransV z hzv hz1 w hw hw1
        rw [← hxw]
        exact DD.mul_mem (DD.mul_mem (hXleD hxX) hzD) (DD.inv_mem (hXleD hxX))
    have hVyD : Work.GW2.conjSub y V ≤ DD := by
      have hm : Work.GW2.conjSub y V ≤ Work.GW2.conjSub y DD := Subgroup.map_mono hVleD
      rwa [hyDD] at hm
    have hVyc : Nat.card ↥(Work.GW2.conjSub y V) = 4 := by
      show Nat.card ↥(V.map (MulAut.conj y).toMonoidHom) = 4
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hVcard]
    have hVne : V ≠ Work.GW2.conjSub y V := by
      intro heq
      have hN : y ∈ Subgroup.normalizer (V : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro a
        constructor
        · intro ha
          have h1 : y * a * y⁻¹ ∈ Work.GW2.conjSub y V := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
          rwa [← heq] at h1
        · intro ha
          have h1 : a ∈ Work.GW2.conjSub y V :=
            Subgroup.mem_map.mpr ⟨y * a * y⁻¹, ha, ?_⟩
          · rwa [← heq] at h1
          · show y * (y * a * y⁻¹) * y⁻¹ = a
            rw [show y * (y * a * y⁻¹) * y⁻¹ = (y * y) * a * (y⁻¹ * y⁻¹) by group, hy1,
              show y⁻¹ * y⁻¹ = 1 by rw [← mul_inv_rev, hy1, inv_one], mul_one, one_mul]
      rw [Work.CORE3.NormalizerPcoreEqHhat G hBc B D.four] at hN
      exact hyH hN
    -- cardinality bookkeeping for `D`
    have hDleHhat : DD ≤ B.Hhat := by rw [hDD]; exact inf_le_left
    have hDcard : Nat.card DD = 6 * Nat.card ↥(DD ⊓ VU) := by
      have h := Subgroup.relIndex_mul_card (H := VU ⊓ DD) (K := DD)
      rw [inf_eq_left.mpr inf_le_right, hDrel] at h
      simpa [inf_comm] using h.symm
    have hN12 : Nat.card ↥(DD ⊓ VU) ∣ 12 := by
      have h := Subgroup.card_dvd_of_le (H := DD ⊓ VU) (K := VU) inf_le_right
      rwa [hVUcard] at h
    by_cases hdisj : V ⊓ Work.GW2.conjSub y V = ⊥
    · -- `V ⊓ V^y = ⊥` would force `16 ∣ |D| = 6 |D ⊓ VU|`, impossible
      have hcard16 : Nat.card ↥(V ⊔ Work.GW2.conjSub y V) = 16 := by
        have h := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot (H := V)
          (K := Work.GW2.conjSub y V) (le_trans hVyD (le_trans hDleHhat hVnorm)) hdisj
        rw [h, hVcard, hVyc]
      have hle : V ⊔ Work.GW2.conjSub y V ≤ DD := sup_le hVleD hVyD
      have h16 : 16 ∣ Nat.card DD := by
        have h2 := Subgroup.card_dvd_of_le hle
        rwa [hcard16] at h2
      have h16' : 16 ∣ 6 * Nat.card ↥(DD ⊓ VU) := by rwa [hDcard] at h16
      obtain ⟨k, hk⟩ := h16'
      have hk2 : 2 * (3 * Nat.card ↥(DD ⊓ VU)) = 2 * (8 * k) := by nlinarith [hk]
      have h3 : 3 * Nat.card ↥(DD ⊓ VU) = 8 * k :=
        Nat.mul_left_cancel (by norm_num : 0 < 2) hk2
      have h8 : 8 ∣ Nat.card ↥(DD ⊓ VU) :=
        Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) ⟨k, h3⟩
      exact absurd (dvd_trans h8 hN12) (by norm_num)
    · -- `|V ⊓ V^y| = 2`, giving an involution fixed by `y`
      have hVinter : Nat.card ↥(V ⊓ Work.GW2.conjSub y V) = 2 := by
        have hdvd : Nat.card ↥(V ⊓ Work.GW2.conjSub y V) ∣ 4 := by
          rw [← hVcard]; exact Subgroup.card_dvd_of_le inf_le_left
        have hpos : 0 < Nat.card ↥(V ⊓ Work.GW2.conjSub y V) := Nat.card_pos
        have hle4 : Nat.card ↥(V ⊓ Work.GW2.conjSub y V) ≤ 4 :=
          Nat.le_of_dvd (by norm_num) hdvd
        have hne1 : Nat.card ↥(V ⊓ Work.GW2.conjSub y V) ≠ 1 := by
          intro h1
          exact hdisj (Work.BSW.Cases.K4.eq_bot_of_card_eq_one h1)
        have hne4 : Nat.card ↥(V ⊓ Work.GW2.conjSub y V) ≠ 4 := by
          intro h4
          have hle : V ≤ Work.GW2.conjSub y V := by
            have heq : V ⊓ Work.GW2.conjSub y V = V :=
              Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h4, hVcard])
            intro x hx
            have hxmem : x ∈ V ⊓ Work.GW2.conjSub y V := by rw [heq]; exact hx
            exact hxmem.2
          exact hVne (Subgroup.eq_of_le_of_card_ge hle (by rw [hVyc, hVcard]))
        have hne3 : Nat.card ↥(V ⊓ Work.GW2.conjSub y V) ≠ 3 := by
          intro h3
          have hd := hdvd
          rw [h3] at hd
          exact absurd hd (by norm_num)
        omega
      obtain ⟨z', hz'mem, hz'1⟩ : ∃ z' ∈ V ⊓ Work.GW2.conjSub y V, z' ≠ 1 := by
        have hnebot : V ⊓ Work.GW2.conjSub y V ≠ ⊥ := hdisj
        obtain ⟨z', hz'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hnebot
        exact ⟨(z' : G), z'.2, fun h => hz'1 (Subtype.ext h)⟩
      have hyz' : y * z' * y = z' := by
        have h1 : y * z' * y ∈ V ⊓ Work.GW2.conjSub y V := by
          constructor
          · obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hz'mem.2
            have hba' : y * b * y⁻¹ = z' := hba
            have hz : y * z' * y = b := by
              rw [← hba']
              rw [show y * (y * b * y⁻¹) * y = (y * y) * b * (y⁻¹ * y) by group, hy1,
                inv_mul_cancel, mul_one, one_mul]
            rw [hz]; exact hb
          · have h2 : y * z' * y⁻¹ ∈ Work.GW2.conjSub y V :=
              Subgroup.mem_map.mpr ⟨z', hz'mem.1, rfl⟩
            rwa [show y * z' * y⁻¹ = y * z' * y by rw [hyinv]] at h2
        by_contra hcon
        have h3 : ({(1 : G), z', y * z' * y} : Set G).ncard = 3 := by
          refine Set.ncard_eq_three.mpr ⟨1, z', y * z' * y, hz'1.symm, ?_, ?_, rfl⟩
          · intro h
            have h2 : y * z' * y = 1 := h.symm
            have h3' : z' = y * (y * z' * y) * y := by
              rw [show y * (y * z' * y) * y = (y * y) * z' * (y * y) by group, hy1, one_mul,
                mul_one]
            rw [h2, mul_one, hy1] at h3'
            exact hz'1 h3'
          · intro h
            exact hcon h.symm
        have hle : 3 ≤ Nat.card ↥(V ⊓ Work.GW2.conjSub y V) := by
          have hsub : ({(1 : G), z', y * z' * y} : Set G) ⊆
              ((V ⊓ Work.GW2.conjSub y V : Subgroup G) : Set G) := by
            intro a ha
            simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ha
            rcases ha with rfl | rfl | rfl
            · exact (V ⊓ Work.GW2.conjSub y V).one_mem
            · exact hz'mem
            · exact h1
          have h2 := Set.ncard_le_ncard hsub (Set.toFinite _)
          rw [h3] at h2
          rw [← Nat.card_coe_set_eq ((V ⊓ Work.GW2.conjSub y V : Subgroup G) : Set G)] at h2
          exact h2
        omega
      have hz'V : z' ∈ V := hz'mem.1
      exact hyH (Work.CORE3.claimA G hBc B I.T.fus h26 D.four hz'V hz'1
        (by
          refine Subgroup.mem_centralizer_iff.mpr ?_
          intro a ha
          rw [Set.mem_singleton_iff] at ha
          rw [ha]
          have h' := congrArg (fun t => t * y) hyz'
          rw [show (y * z' * y) * y = y * z' by rw [mul_assoc, hy1, mul_one]] at h'
          exact h'.symm))
  have case2 : V ⊓ DD = ⊥ → Uu ⊓ DD ≠ ⊥ → False := by
    haveI : IsSimpleGroup G := hBc.simple
    intro hVDbot hne
    have hVnorm' := hVnorm''
    have hUnorm' := hUnorm''
    have hVcomm : ∀ v ∈ V, ∀ w ∈ V, v * w = w * v := by
      intro v hv w hw
      have hvw : v * v = 1 := by simpa [pow_two] using hVsq v hv
      have hww : w * w = 1 := by simpa [pow_two] using hVsq w hw
      have h1 : (v * w) * (v * w) = 1 := by
        simpa [pow_two] using hVsq (v * w) (V.mul_mem hv hw)
      have h3 : v * w * v * w = 1 := by
        rw [show v * w * v * w = (v * w) * (v * w) by group]; exact h1
      have h4 := congrArg (fun t => t * w) h3
      have h2 : v * w * v = w := by
        rw [show (v * w * v * w) * w = v * w * v * (w * w) by group, hww, mul_one,
          one_mul] at h4
        exact h4
      have h5 := congrArg (fun t => t * v) h2
      rw [show (v * w * v) * v = v * w * (v * v) by group, hvw, mul_one] at h5
      exact h5
    have hXcomm : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := by
      intro a ha b hb
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      haveI : IsCyclic ↥X := isCyclic_of_prime_card hXcard
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥X)
      have hg3 : orderOf (g : G) = 3 := by rw [Subgroup.orderOf_coe, hg, hXcard]
      have hgen : Subgroup.zpowers (g : G) = X :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr g.2)
          (by rw [Nat.card_zpowers, hg3, hXcard])
      have h1 : a ∈ Subgroup.zpowers (g : G) := by rw [hgen]; exact ha
      have h2 : b ∈ Subgroup.zpowers (g : G) := by rw [hgen]; exact hb
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h1
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h2
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    have hUcomm : ∀ a ∈ Uu, ∀ b ∈ Uu, a * b = b * a := by
      intro a ha b hb
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      haveI : IsCyclic ↥Uu := isCyclic_of_prime_card hUcard
      obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := ↥Uu)
      have hg3 : orderOf (g : G) = 3 := by rw [Subgroup.orderOf_coe, hg, hUcard]
      have hgen : Subgroup.zpowers (g : G) = Uu :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr g.2)
          (by rw [Nat.card_zpowers, hg3, hUcard])
      have h1 : a ∈ Subgroup.zpowers (g : G) := by rw [hgen]; exact ha
      have h2 : b ∈ Subgroup.zpowers (g : G) := by rw [hgen]; exact hb
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h1
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h2
      rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    have hVUcomm : ∀ a ∈ VU, ∀ b ∈ VU, a * b = b * a := by
      intro a ha b hb
      obtain ⟨v₁, hv₁, u₁, hu₁, haeq⟩ := Work.CORE3.exists_mul_of_mem_sup_of_normal
        (S := B.Hhat) hVleHhat hUleHhat hVnorm' hUnorm' a ha
      obtain ⟨v₂, hv₂, u₂, hu₂, hbeq⟩ := Work.CORE3.exists_mul_of_mem_sup_of_normal
        (S := B.Hhat) hVleHhat hUleHhat hVnorm' hUnorm' b hb
      rw [haeq, hbeq]
      calc (v₁ * u₁) * (v₂ * u₂) = v₁ * (u₁ * v₂) * u₂ := by group
        _ = v₁ * (v₂ * u₁) * u₂ := by rw [hcommVU v₂ hv₂ u₁ hu₁]
        _ = (v₁ * v₂) * (u₁ * u₂) := by group
        _ = (v₂ * v₁) * (u₂ * u₁) := by rw [hVcomm v₁ hv₁ v₂ hv₂, hUcomm u₁ hu₁ u₂ hu₂]
        _ = v₂ * (v₁ * u₂) * u₁ := by group
        _ = v₂ * (u₂ * v₁) * u₁ := by rw [hcommVU v₁ hv₁ u₂ hu₂]
        _ = (v₂ * u₂) * (v₁ * u₁) := by group
    have hUleD : Uu ≤ DD := by
      have h := J4DTrivAux.eq_of_le_of_card_eq_three inf_le_left hUcard hne
      intro x hx
      have hx' : x ∈ Uu ⊓ DD := by rw [h]; exact hx
      exact hx'.2
    have hUBot : B.U ≠ ⊥ := by
      intro hb
      have h1 : Nat.card ↥(⊥ : Subgroup G) = 3 := by rw [← hb]; exact hU3
      rw [Subgroup.card_bot] at h1
      norm_num at h1
    have hNUeq : Subgroup.normalizer (Uu : Set G) = B.Hhat := by
      rw [hU]
      exact Work.CORE3.normalizer_eq_of_isCoatom B.Hhat B.Hhat_coatom B.U hUleHhat hUnorm hUBot
    have hDleHhat : DD ≤ B.Hhat := by rw [hDD]; exact inf_le_left
    -- ### `D ⊓ VU = U` and `|D| = 18`
    have hNdisj : V ⊓ (DD ⊓ VU) = ⊥ := by
      refine le_bot_iff.mp ?_
      calc V ⊓ (DD ⊓ VU) ≤ V ⊓ DD := inf_le_inf_left V inf_le_left
        _ = ⊥ := hVDbot
    have hNmem : ∀ b ∈ DD ⊓ VU, b ∈ VU := fun b hb => hb.2
    have hVmem : ∀ a ∈ V, a ∈ VU := fun a ha => Subgroup.mem_sup_left ha
    have hUmem : ∀ a ∈ Uu, a ∈ VU := fun a ha => Subgroup.mem_sup_right ha
    have hUleDVU : Uu ≤ DD ⊓ VU := fun x hx => ⟨hUleD hx, hUmem x hx⟩
    have hVnormN : DD ⊓ VU ≤ Subgroup.normalizer (V : Set G) := by
      intro n hn
      rw [Subgroup.mem_normalizer_iff]
      intro w
      constructor
      · intro hw'
        have h2 : n * w * n⁻¹ = w := by
          rw [hVUcomm n hn.2 w (hVmem w hw')]
          group
        rw [h2]
        exact hw'
      · intro hw'
        have h3 : n⁻¹ * (n * w * n⁻¹) * n = n * w * n⁻¹ := by
          rw [hVUcomm n⁻¹ (VU.inv_mem hn.2) (n * w * n⁻¹) (hVmem (n * w * n⁻¹) hw')]
          group
        have h1 : w = n⁻¹ * (n * w * n⁻¹) * n := by group
        rw [h1, h3]
        exact hw'
    have hNcard : Nat.card ↥(DD ⊓ VU) = 3 := by
      have h := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot (H := V) (K := DD ⊓ VU)
        hVnormN hNdisj
      have hle : V ⊔ (DD ⊓ VU) ≤ VU := sup_le le_sup_left inf_le_right
      have hdvd : Nat.card ↥(DD ⊓ VU) * 4 ∣ 12 := by
        have h2 := Subgroup.card_dvd_of_le hle
        rw [h, hVcard, hVUcard] at h2
        simpa [mul_comm] using h2
      have hN3 : Nat.card ↥(DD ⊓ VU) ∣ 3 := by
        have h4 : Nat.card ↥(DD ⊓ VU) * 4 ∣ 3 * 4 := by
          rw [show (3 * 4 : ℕ) = 12 by norm_num]; exact hdvd
        exact (Nat.mul_dvd_mul_iff_right (by norm_num : 0 < 4)).mp h4
      have h3dvd : 3 ∣ Nat.card ↥(DD ⊓ VU) := by
        have h2 := Subgroup.card_dvd_of_le (H := Uu) (K := DD ⊓ VU) hUleDVU
        rwa [hUcard] at h2
      have hge : 3 ≤ Nat.card ↥(DD ⊓ VU) := Nat.le_of_dvd Nat.card_pos h3dvd
      have hle3 : Nat.card ↥(DD ⊓ VU) ≤ 3 := Nat.le_of_dvd (by norm_num) hN3
      omega
    have hNU : DD ⊓ VU = Uu :=
      (Subgroup.eq_of_le_of_card_ge hUleDVU (by rw [hNcard, hUcard])).symm
    have hDrel18 : (DD ⊓ VU).relIndex DD = 6 := by simpa [inf_comm] using hDrel
    have hDcard18 : Nat.card DD = 18 := by
      have h := Subgroup.relIndex_mul_card (H := DD ⊓ VU) (K := DD)
      rw [inf_eq_left.mpr inf_le_left, hDrel18, hNcard] at h
      norm_num at h
      exact h.symm
    -- ### `E = X ⊔ U` and its structure
    have hXUdisj : X ⊓ Uu = ⊥ := by
      refine le_bot_iff.mp ?_
      intro x hx
      rw [Subgroup.mem_inf] at hx
      have h2 : x ∈ X ⊓ VU := ⟨hx.1, show x ∈ V ⊔ Uu from Subgroup.mem_sup_right hx.2⟩
      rw [hXVUdisj] at h2
      exact Subgroup.mem_bot.mp h2
    have hEcard : Nat.card ↥(X ⊔ Uu) = 9 := by
      have h := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot (H := Uu) (K := X)
        (le_trans hXH hUnorm) (by rw [inf_comm]; exact hXUdisj)
      rw [show Nat.card ↥(X ⊔ Uu) = Nat.card ↥(Uu ⊔ X) by rw [sup_comm], h, hUcard, hXcard]
    have hEdvd : (X ⊔ Uu).relIndex DD = 2 := by
      have h := Subgroup.relIndex_mul_card (H := X ⊔ Uu) (K := DD)
      rw [inf_eq_left.mpr (sup_le hXleD hUleD), hEcard, hDcard18] at h
      omega
    have hEsq : ∀ z ∈ DD, z * z ∈ X ⊔ Uu := by
      intro z hz
      have h := Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd (H := X ⊔ Uu) (K := DD)
        (by rw [hEdvd]; norm_num) hz (n := 2) (fun m _ hm2 => by
          rw [hEdvd] at hm2; interval_cases m <;> norm_num)
      rw [inf_eq_left.mpr (sup_le hXleD hUleD)] at h
      rwa [pow_two] at h
    have hEab : ∀ a ∈ X ⊔ Uu, ∀ b ∈ X ⊔ Uu, a * b = b * a := by
      haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
      have hc : IsMulCommutative ↥(X ⊔ Uu) :=
        IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (G := ↥(X ⊔ Uu))
          (by rw [hEcard]; norm_num)
      intro a ha b hb
      exact congrArg Subtype.val (hc.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hEswap : ∀ a ∈ X ⊔ Uu, ∀ b ∈ X ⊔ Uu, ∀ c ∈ X ⊔ Uu, ∀ d ∈ X ⊔ Uu,
        (a * b) * (c * d) = (a * c) * (b * d) := by
      intro a ha b hb c hc d hd
      rw [show (a * b) * (c * d) = a * (b * c) * d by group, hEab b hb c hc]
      group
    have hEdecomp : ∀ w ∈ X ⊔ Uu, ∃ x ∈ X, ∃ u ∈ Uu, w = x * u := by
      intro w hw
      have hXnormE : ∀ s ∈ X ⊔ Uu, ∀ x ∈ X, s * x * s⁻¹ ∈ X := by
        intro s hs x hx
        have hx' : x ∈ X ⊔ Uu := Subgroup.mem_sup_left hx
        have h1 : s * x * s⁻¹ = x := by rw [hEab s hs x hx']; group
        rw [h1]; exact hx
      have hUnormE : ∀ s ∈ X ⊔ Uu, ∀ u ∈ Uu, s * u * s⁻¹ ∈ Uu := by
        intro s hs u hu
        have hu' : u ∈ X ⊔ Uu := Subgroup.mem_sup_right hu
        have h1 : s * u * s⁻¹ = u := by rw [hEab s hs u hu']; group
        rw [h1]; exact hu
      exact Work.CORE3.exists_mul_of_mem_sup_of_normal (V := X) (U := Uu) (S := X ⊔ Uu)
        le_sup_left le_sup_right hXnormE hUnormE w hw
    have hEpow : ∀ w ∈ X ⊔ Uu, w ^ 3 = 1 := by
      intro w hw
      obtain ⟨x, hx, u, hu, hwu⟩ := hEdecomp w hw
      rw [hwu]
      have hx3 : x ^ 3 = 1 := by
        have hd : orderOf x ∣ 3 := by
          rw [← hXcard]; exact Subgroup.orderOf_dvd_natCard X hx
        exact orderOf_dvd_iff_pow_eq_one.mp hd
      have hu3 : u ^ 3 = 1 := by
        have hd : orderOf u ∣ 3 := by
          rw [← hUcard]; exact Subgroup.orderOf_dvd_natCard Uu hu
        exact orderOf_dvd_iff_pow_eq_one.mp hd
      rw [(show Commute x u from
            hEab x (Subgroup.mem_sup_left hx) u (Subgroup.mem_sup_right hu)).mul_pow, hx3, hu3,
        mul_one]
    have hEcomm : ∀ a ∈ X ⊔ Uu, ∀ b ∈ X ⊔ Uu, a * b = b * a := hEab
    have hEsub : X ⊔ Uu ≤ DD := sup_le hXleD hUleD
    have hUyD : Work.GW2.conjSub y Uu ≤ DD := by
      have hm : Work.GW2.conjSub y Uu ≤ Work.GW2.conjSub y DD := Subgroup.map_mono hUleD
      rwa [hyDD] at hm
    have hUyc : Nat.card ↥(Work.GW2.conjSub y Uu) = 3 := by
      show Nat.card ↥(Uu.map (MulAut.conj y).toMonoidHom) = 3
      rw [Subgroup.card_map_of_injective (MulAut.conj y).injective, hUcard]
    have hUyne : Uu ≠ Work.GW2.conjSub y Uu := by
      intro heq
      have hN : y ∈ Subgroup.normalizer (Uu : Set G) := by
        rw [Subgroup.mem_normalizer_iff]
        intro a
        constructor
        · intro ha
          have h1 : y * a * y⁻¹ ∈ Work.GW2.conjSub y Uu := Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
          rwa [← heq] at h1
        · intro ha
          have h1 : a ∈ Work.GW2.conjSub y Uu := Subgroup.mem_map.mpr ⟨y * a * y⁻¹, ha, ?_⟩
          · rwa [← heq] at h1
          · show y * (y * a * y⁻¹) * y⁻¹ = a
            rw [show y * (y * a * y⁻¹) * y⁻¹ = (y * y) * a * (y⁻¹ * y⁻¹) by group, hy1,
              show y⁻¹ * y⁻¹ = 1 by rw [← mul_inv_rev, hy1, inv_one], mul_one, one_mul]
      rw [hNUeq] at hN
      exact hyH hN
    have hWdisj : Uu ⊓ Work.GW2.conjSub y Uu = ⊥ := by
      have hdvd : Nat.card ↥(Uu ⊓ Work.GW2.conjSub y Uu) ∣ 3 := by
        rw [← hUcard]; exact Subgroup.card_dvd_of_le inf_le_left
      have hne3 : Nat.card ↥(Uu ⊓ Work.GW2.conjSub y Uu) ≠ 3 := by
        intro h3
        have hle : Uu ≤ Work.GW2.conjSub y Uu := by
          have heq : Uu ⊓ Work.GW2.conjSub y Uu = Uu :=
            Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hUcard])
          intro x hx
          have hx' : x ∈ Uu ⊓ Work.GW2.conjSub y Uu := by rw [heq]; exact hx
          exact hx'.2
        exact hUyne (Subgroup.eq_of_le_of_card_ge hle (by rw [hUyc, hUcard]))
      have h1 : Nat.card ↥(Uu ⊓ Work.GW2.conjSub y Uu) = 1 := by
        rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
        · exact h
        · exact absurd h hne3
      exact Work.BSW.Cases.K4.eq_bot_of_card_eq_one h1
    have hUyE : Work.GW2.conjSub y Uu ≤ X ⊔ Uu := by
      have hweq : X ⊔ Uu = Uu ⊔ Work.GW2.conjSub y Uu :=
        J4DTrivAux.card_eq_nine_eq_of_le_card_eighteen hDcard18 hEsub (sup_le hUleD hUyD)
          hEcard (by
            have h := Work.BSW.Cases.K4.card_sup_of_le_normalizer_of_inf_eq_bot (H := Uu)
              (K := Work.GW2.conjSub y Uu) (le_trans hUyD (le_trans hDleHhat hUnorm)) hWdisj
            rw [h, hUcard, hUyc])
      rw [hweq]; exact le_sup_right
    have hInvX : ∀ x ∈ X, y * x * y = x⁻¹ := fun x hx => by simpa [hyinv] using hinv x hx
    have hconj2 : ∀ a b : G, y * (a * b) * y = (y * a * y) * (y * b * y) := by
      intro a b
      rw [show y * (a * b) * y = y * (a * b) * y⁻¹ by rw [hyinv],
        show y * (a * b) * y⁻¹ = (y * a * y⁻¹) * (y * b * y⁻¹) by group, hyinv]
    have hyEy : ∀ e ∈ X ⊔ Uu, y * e * y ∈ X ⊔ Uu := by
      intro e he
      obtain ⟨x, hx, u, hu, heq⟩ := hEdecomp e he
      rw [heq]
      have h1 : y * x * y = x⁻¹ := hInvX x hx
      have h2 : y * u * y ∈ Work.GW2.conjSub y Uu := by
        have h3 : y * u * y = y * u * y⁻¹ := by rw [hyinv]
        rw [h3]; exact Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
      rw [hconj2 x u, h1]
      exact (X ⊔ Uu).mul_mem ((X ⊔ Uu).inv_mem (Subgroup.mem_sup_left hx)) (hUyE h2)
    have hEnormal : ∀ e ∈ X ⊔ Uu, ∀ z ∈ DD, z * e * z⁻¹ ∈ X ⊔ Uu := by
      have hidx : ((X ⊔ Uu).subgroupOf DD).index = 2 := by
        rw [Subgroup.index_eq_card_div,
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEsub).toEquiv, hEcard, hDcard18]
      haveI hNidx : ((X ⊔ Uu).subgroupOf DD).Normal := Subgroup.normal_of_index_eq_two hidx
      intro e he z hz
      exact (Subgroup.normal_subgroupOf_iff hEsub).mp hNidx e z he hz
    have hconjE : ∀ z ∈ DD, ∀ e ∈ X ⊔ Uu, z * e * z⁻¹ ∈ X ⊔ Uu :=
      fun z hz e he => hEnormal e he z hz
    -- ### an involution `m ∈ D − E`
    have hneE : X ⊔ Uu ≠ DD := by
      intro h
      have hc := congrArg (fun s : Subgroup G => Nat.card ↥s) h
      rw [hEcard, hDcard18] at hc
      norm_num at hc
    obtain ⟨m, hmD, hmE, hm2⟩ : ∃ m ∈ DD, m ∉ X ⊔ Uu ∧ m * m = 1 := by
      obtain ⟨z, hzD, hzE⟩ : ∃ z ∈ DD, z ∉ X ⊔ Uu := by
        by_contra hcon
        push_neg at hcon
        exact hneE (le_antisymm (sup_le hXleD hUleD) (fun x hx => hcon x hx))
      by_cases hzsq : z * z = 1
      · exact ⟨z, hzD, hzE, hzsq⟩
      · have hz3E : z ^ 3 ∉ X ⊔ Uu := by
          intro hcon
          have h2E : z * z ∈ X ⊔ Uu := hEsq z hzD
          have h2inv : (z * z)⁻¹ ∈ X ⊔ Uu := (X ⊔ Uu).inv_mem h2E
          have hzz : z = z ^ 3 * (z * z)⁻¹ := by group
          refine hzE ?_
          rw [hzz]
          exact (X ⊔ Uu).mul_mem hcon h2inv
        have hz3sq : z ^ 3 * z ^ 3 = 1 := by
          have h3 : z ^ 3 * z ^ 3 = (z * z) ^ 3 := by
            rw [← (Commute.refl z).mul_pow 3]
          rw [h3, hEpow (z * z) (hEsq z hzD)]
        exact ⟨z ^ 3, DD.pow_mem hzD 3, hz3E, hz3sq⟩
    have hmHhat : m ∈ B.Hhat := hDleHhat hmD
    have hminv : m⁻¹ = m := inv_eq_of_mul_eq_one_left hm2
    have hmconj2 : ∀ a b : G, m * (a * b) * m = (m * a * m) * (m * b * m) := by
      intro a b
      rw [show m * (a * b) * m = m * (a * b) * m⁻¹ by rw [hminv],
        show m * (a * b) * m⁻¹ = (m * a * m⁻¹) * (m * b * m⁻¹) by group, hminv]
    have hconjEm : ∀ e ∈ X ⊔ Uu, m * e * m ∈ X ⊔ Uu := by
      intro e he
      have h := hconjE m hmD e he
      rwa [hminv] at h
    have hEidx2 : ((X ⊔ Uu).subgroupOf DD).index = 2 := by
      rw [Subgroup.index_eq_card_div,
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEsub).toEquiv, hEcard, hDcard18]
    have hsplit : ∀ z ∈ DD, z ∈ X ⊔ Uu ∨ ∃ e ∈ X ⊔ Uu, z = m * e := by
      intro z hz
      by_cases hzE : z ∈ X ⊔ Uu
      · exact Or.inl hzE
      · refine Or.inr ⟨m * z, ?_, by rw [← mul_assoc, hm2, one_mul]⟩
        have hkey : ((⟨m, hmD⟩ : ↥DD) * ⟨z, hz⟩) ∈ ((X ⊔ Uu).subgroupOf DD) := by
          rw [Subgroup.mul_mem_iff_of_index_two hEidx2, Subgroup.mem_subgroupOf,
            Subgroup.mem_subgroupOf]
          exact ⟨fun h => absurd h hmE, fun h => absurd h hzE⟩
        simpa using (Subgroup.mem_subgroupOf).mp hkey
    -- ### `I ∩ E = X`
    have hIX : Work.CORE3.invSetIn B.Hhat y ∩ ((X ⊔ Uu : Subgroup G) : Set G) = (X : Set G) := by
      refine le_antisymm ?_ ?_
      · intro a ha
        rw [Set.mem_inter_iff] at ha
        obtain ⟨haI, haE⟩ := ha
        obtain ⟨x, hx, u, hu, haeq⟩ := hEdecomp a haE
        rw [haeq] at haI ⊢
        have h1 : y * (x * u) * y = (y * x * y) * (y * u * y) := hconj2 x u
        have h1' : y * x * y = x⁻¹ := hInvX x hx
        have h2 : (x * u)⁻¹ = x⁻¹ * u⁻¹ := by
          rw [mul_inv_rev,
            (show Commute u x from
              hEab u (Subgroup.mem_sup_right hu) x (Subgroup.mem_sup_left hx)).inv_inv]
        have hu' : y * u * y = u⁻¹ := by
          have h3 := haI.2
          rw [h1, h1', h2] at h3
          exact mul_left_cancel h3
        have h5 : y * u * y⁻¹ ∈ Uu ⊓ Work.GW2.conjSub y Uu := by
          refine ⟨?_, Subgroup.mem_map.mpr ⟨u, hu, rfl⟩⟩
          rw [hyinv, hu']
          exact Uu.inv_mem hu
        rw [hWdisj] at h5
        have h6 : y * u * y⁻¹ = 1 := Subgroup.mem_bot.mp h5
        have hu1 : u = 1 := by
          have h7 : u = y⁻¹ * (y * u * y⁻¹) * y := by group
          rw [h6, mul_one, inv_mul_cancel] at h7
          exact h7
        rw [hu1, mul_one]
        exact hx
      · intro a ha
        exact ⟨⟨hXH ha, hInvX a ha⟩, Subgroup.mem_sup_left ha⟩
    -- ### `e₀` and the criterion for `m * e ∈ I`
    have hyphim : y * m * y ∉ X ⊔ Uu := by
      intro hcon
      refine hmE ?_
      have h1 : m = y * (y * m * y) * y := by
        rw [show y * (y * m * y) * y = (y * y) * m * (y * y) by group, hy1, one_mul, mul_one]
      rw [h1]
      exact hyEy (y * m * y) hcon
    have hyphimD : y * m * y ∈ DD := by
      have h1 : y * m * y = y * m * y⁻¹ := by rw [hyinv]
      rw [h1]
      have h2 : y * m * y⁻¹ ∈ Work.GW2.conjSub y DD := Subgroup.mem_map.mpr ⟨m, hmD, rfl⟩
      rwa [hyDD] at h2
    obtain ⟨e₀, he₀E, he₀⟩ : ∃ e₀ ∈ X ⊔ Uu, y * m * y = m * e₀ := by
      rcases hsplit (y * m * y) hyphimD with h | h
      · exact absurd h hyphim
      · exact h
    have hσ2 : ∀ e ∈ X ⊔ Uu, m * (m * e * m) * m = e := by
      intro e _
      rw [show m * (m * e * m) * m = (m * m) * e * (m * m) by group, hm2, one_mul, mul_one]
    have hM2 : ∀ e ∈ X ⊔ Uu, y * (y * e * y) * y = e := by
      intro e _
      rw [show y * (y * e * y) * y = (y * y) * e * (y * y) by group, hy1, one_mul, mul_one]
    have hmy : (y * m * y)⁻¹ = y * m * y := by
      rw [show (y * m * y)⁻¹ = y⁻¹ * m⁻¹ * y⁻¹ by group, hyinv, hminv]
    have hMσ : ∀ e ∈ X ⊔ Uu, y * (m * e * m) * y = m * (y * e * y) * m := by
      intro e he
      have hA : y * e * y ∈ X ⊔ Uu := hyEy e he
      have h1 : y * (m * e * m) * y = (m * e₀) * (y * e * y) * (m * e₀)⁻¹ := by
        rw [show y * (m * e * m) * y = (y * m * y) * (y * e * y) * (y * m * y)⁻¹ by
              rw [show y * (m * e * m) * y = y * (m * e * m) * y⁻¹ by rw [hyinv],
                show y * (m * e * m) * y⁻¹ = (y * m * y⁻¹) * (y * e * y⁻¹) * (y * m * y⁻¹) by
                  group,
                hyinv, hmy],
            he₀]
      rw [h1]
      have h3 : (m * e₀)⁻¹ = e₀⁻¹ * m := by simp only [mul_inv_rev, hminv]
      rw [h3]
      rw [show (m * e₀) * (y * e * y) * (e₀⁻¹ * m) =
          m * (e₀ * (y * e * y) * e₀⁻¹) * m by group]
      rw [show e₀ * (y * e * y) * e₀⁻¹ = y * e * y by
        rw [hEab e₀ he₀E (y * e * y) hA]
        group]
    have hcriterion : ∀ e ∈ X ⊔ Uu, (m * e ∈ Work.CORE3.invSetIn B.Hhat y ↔
        e₀ * (y * e * y) * (m * e * m) = 1) := by
      intro e he
      have heH : e ∈ B.Hhat := hDleHhat (hEsub he)
      have hL : y * (m * e) * y = (m * e₀) * (y * e * y) := by
        rw [hconj2 m e, he₀]
      have hR : (m * e)⁻¹ = e⁻¹ * m := by simp only [mul_inv_rev, hminv]
      have key : (y * (m * e) * y = (m * e)⁻¹) ↔
          e₀ * (y * e * y) * (m * e * m) = 1 := by
        constructor
        · intro hh
          have h1 : e₀ * (y * e * y) = m * e⁻¹ * m := by
            have h2 : (m * e₀) * (y * e * y) = e⁻¹ * m := by rw [← hL, hh, hR]
            have h3 := congrArg (fun t => m * t) h2
            rw [show m * ((m * e₀) * (y * e * y)) = e₀ * (y * e * y) by
                  rw [show m * ((m * e₀) * (y * e * y)) = (m * m) * e₀ * (y * e * y) by group,
                    hm2, one_mul],
                show m * (e⁻¹ * m) = m * e⁻¹ * m by group] at h3
            exact h3
          rw [h1]
          rw [show (m * e⁻¹ * m) * (m * e * m) = 1 by
            rw [show (m * e⁻¹ * m) * (m * e * m) = m * (e⁻¹ * (m * m) * e) * m by group,
              hm2, mul_one, inv_mul_cancel, mul_one, hm2]]
        · intro hc
          have h3 : e₀ * (y * e * y) = m * e⁻¹ * m := by
            have h4 : e₀ * (y * e * y) = (m * e * m)⁻¹ := eq_inv_of_mul_eq_one_left hc
            rw [h4]
            rw [show (m * e * m)⁻¹ = m * e⁻¹ * m by
              rw [show (m * e * m)⁻¹ = m⁻¹ * e⁻¹ * m⁻¹ by group, hminv]]
          rw [hL, mul_assoc, h3, hR]
          rw [show m * (m * e⁻¹ * m) = e⁻¹ * m by
            rw [show m * (m * e⁻¹ * m) = (m * m) * e⁻¹ * m by group, hm2, one_mul]]
      constructor
      · intro hI
        exact key.mp hI.2
      · intro hh
        exact ⟨B.Hhat.mul_mem hmHhat heH, key.mpr hh⟩
    -- ### the unique element of `I \ E`
    have hIXcard : (Work.CORE3.invSetIn B.Hhat y ∩ ((X ⊔ Uu : Subgroup G) : Set G)).ncard = 3 := by
      have hc : (X : Set G).ncard = Nat.card X := (Nat.card_coe_set_eq (X : Set G)).symm
      rw [hIX, hc, hXcard]
    have hdiffcard : (Work.CORE3.invSetIn B.Hhat y \ ((X ⊔ Uu : Subgroup G) : Set G)).ncard = 1 := by
      have heq : Work.CORE3.invSetIn B.Hhat y \ ((X ⊔ Uu : Subgroup G) : Set G) =
          Work.CORE3.invSetIn B.Hhat y \
            (Work.CORE3.invSetIn B.Hhat y ∩ ((X ⊔ Uu : Subgroup G) : Set G)) := by
        ext a; simp only [Set.mem_sdiff, Set.mem_inter_iff]; tauto
      have h2 : (Work.CORE3.invSetIn B.Hhat y).ncard -
          (Work.CORE3.invSetIn B.Hhat y ∩ ((X ⊔ Uu : Subgroup G) : Set G)).ncard = 1 := by
        have h3 : (Work.CORE3.invSetIn B.Hhat y).ncard -
            (Work.CORE3.invSetIn B.Hhat y ∩ ((X ⊔ Uu : Subgroup G) : Set G)).ncard = 4 - 3 := by
          rw [hIcard, hIXcard]
        rw [h3]
      rw [heq, Set.ncard_sdiff Set.inter_subset_left, h2]
    obtain ⟨w, hw⟩ := Set.ncard_eq_one.mp hdiffcard
    have hwmem : w ∈ ({(w : G)} : Set G) := Set.mem_singleton w
    have hwI : w ∈ Work.CORE3.invSetIn B.Hhat y := by
      have h : w ∈ Work.CORE3.invSetIn B.Hhat y \ ((X ⊔ Uu : Subgroup G) : Set G) := by rw [hw]; exact hwmem
      exact h.1
    have hwE : w ∉ X ⊔ Uu := by
      have h : w ∈ Work.CORE3.invSetIn B.Hhat y \ ((X ⊔ Uu : Subgroup G) : Set G) := by rw [hw]; exact hwmem
      exact h.2
    obtain ⟨e₁, he₁E, hwe₁⟩ : ∃ e₁ ∈ X ⊔ Uu, w = m * e₁ := by
      rcases hsplit w (hIleD hwI) with h | h
      · exact absurd h hwE
      · exact h
    -- ### `K = {1}`
    have hK1 : ∀ f ∈ X ⊔ Uu, (y * f * y) * (m * f * m) = 1 → f = 1 := by
      intro f hfE hfK
      have h1 : e₀ * (y * e₁ * y) * (m * e₁ * m) = 1 :=
        (hcriterion e₁ he₁E).mp (by rw [← hwe₁]; exact hwI)
      have h2 : y * e₁ * y ∈ X ⊔ Uu := hyEy e₁ he₁E
      have h2' : y * f * y ∈ X ⊔ Uu := hyEy f hfE
      have h4 : m * e₁ * m ∈ X ⊔ Uu := hconjEm e₁ he₁E
      have h4' : m * f * m ∈ X ⊔ Uu := hconjEm f hfE
      have h6 : e₀ * ((y * e₁ * y) * (y * f * y)) * ((m * e₁ * m) * (m * f * m)) = 1 := by
        calc e₀ * ((y * e₁ * y) * (y * f * y)) * ((m * e₁ * m) * (m * f * m))
            = e₀ * (((y * e₁ * y) * (y * f * y)) * ((m * e₁ * m) * (m * f * m))) := by
              group
          _ = e₀ * (((y * e₁ * y) * (m * e₁ * m)) * ((y * f * y) * (m * f * m))) := by
              rw [hEswap (y * e₁ * y) h2 (y * f * y) h2' (m * e₁ * m) h4 (m * f * m) h4']
          _ = (e₀ * ((y * e₁ * y) * (m * e₁ * m))) * ((y * f * y) * (m * f * m)) := by
              group
          _ = (e₀ * (y * e₁ * y) * (m * e₁ * m)) * ((y * f * y) * (m * f * m)) := by
              group
          _ = 1 := by rw [h1, hfK, mul_one]
      have h7 : m * (e₁ * f) ∈ Work.CORE3.invSetIn B.Hhat y := by
        refine (hcriterion (e₁ * f) ((X ⊔ Uu).mul_mem he₁E hfE)).mpr ?_
        rw [hconj2 e₁ f, hmconj2 e₁ f]
        exact h6
      have h8 : m * (e₁ * f) ∉ X ⊔ Uu := by
        intro hcon
        refine hmE ?_
        have h9 : m = (m * (e₁ * f)) * (e₁ * f)⁻¹ := by group
        rw [h9]
        exact (X ⊔ Uu).mul_mem hcon ((X ⊔ Uu).inv_mem ((X ⊔ Uu).mul_mem he₁E hfE))
      have h10 : m * (e₁ * f) = w := by
        have h11 : m * (e₁ * f) ∈ Work.CORE3.invSetIn B.Hhat y \ ((X ⊔ Uu : Subgroup G) : Set G) := ⟨h7, h8⟩
        have h12 : m * (e₁ * f) ∈ ({(w : G)} : Set G) := by rw [← hw]; exact h11
        exact h12
      have h12 : m * (e₁ * f) = m * e₁ := by rw [h10, hwe₁]
      have h13 : e₁ * f = e₁ := mul_left_cancel h12
      exact mul_left_cancel (by rw [h13, mul_one])
    -- ### `ρ = σ ∘ M` is the identity on `E`
    have hρ2 : ∀ e ∈ X ⊔ Uu, m * (y * (m * (y * e * y) * m) * y) * m = e := by
      intro e he
      have h1 : y * e * y ∈ X ⊔ Uu := hyEy e he
      rw [hMσ (y * e * y) h1, show y * (y * e * y) * y = e by
        rw [show y * (y * e * y) * y = (y * y) * e * (y * y) by group, hy1, one_mul, mul_one]]
      exact hσ2 e he
    have hρmul : ∀ a ∈ X ⊔ Uu, ∀ b ∈ X ⊔ Uu,
        m * (y * (a * b) * y) * m = (m * (y * a * y) * m) * (m * (y * b * y) * m) := by
      intro a _ b _
      rw [hconj2 a b, hmconj2 (y * a * y) (y * b * y)]
    have hρinv : ∀ e ∈ X ⊔ Uu, m * (y * e⁻¹ * y) * m = (m * (y * e * y) * m)⁻¹ := by
      intro e _
      rw [show (m * (y * e * y) * m)⁻¹ = m * (y * e⁻¹ * y) * m by
        rw [show (m * (y * e * y) * m)⁻¹ = m⁻¹ * (y * e * y)⁻¹ * m⁻¹ by group,
          show (y * e * y)⁻¹ = y * e⁻¹ * y by
            rw [show (y * e * y)⁻¹ = y⁻¹ * e⁻¹ * y⁻¹ by group, hyinv],
          hminv]]
    have hρid : ∀ e ∈ X ⊔ Uu, m * (y * e * y) * m = e := by
      intro e he
      by_contra hne'
      set g := (m * (y * e * y) * m) * e⁻¹ with hg
      have hρeE : m * (y * e * y) * m ∈ X ⊔ Uu := hconjEm (y * e * y) (hyEy e he)
      have hgE : g ∈ X ⊔ Uu := (X ⊔ Uu).mul_mem hρeE ((X ⊔ Uu).inv_mem he)
      have hgne : g ≠ 1 := by
        intro h1
        apply hne'
        have h2 : (m * (y * e * y) * m) * e⁻¹ = 1 := h1
        have h3 : m * (y * e * y) * m = 1 * e := by rw [← h2]; group
        rwa [one_mul] at h3
      have hKg : (y * g * y) * (m * g * m) = 1 := by
        have hρg : m * (y * g * y) * m = g⁻¹ := by
          rw [hg]
          rw [hρmul (m * (y * e * y) * m) hρeE e⁻¹ ((X ⊔ Uu).inv_mem he)]
          rw [hρ2 e he, hρinv e he]
          group
        have h4 : m * g * m = (y * g * y)⁻¹ := by
          have h5 : y * (m * (y * g * y) * m) * y = y * g⁻¹ * y := by rw [hρg]
          have h6 : y * (m * (y * g * y) * m) * y = m * g * m := by
            rw [hMσ (y * g * y) (hyEy g hgE),
              show y * (y * g * y) * y = g by
                rw [show y * (y * g * y) * y = (y * y) * g * (y * y) by group, hy1, one_mul,
                  mul_one]]
          rw [h6] at h5
          rw [h5]
          rw [show (y * g * y)⁻¹ = y * g⁻¹ * y by
            rw [show (y * g * y)⁻¹ = y⁻¹ * g⁻¹ * y⁻¹ by group, hyinv]]
        rw [h4, mul_inv_cancel]
      exact hgne (hK1 g hgE hKg)
    -- ### final contradiction
    have hcen : m * y ∈ Subgroup.centralizer (Uu : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro u hu
      have h1 : (m * y) * u * (m * y)⁻¹ = m * (y * u * y) * m := by
        rw [show (m * y)⁻¹ = y * m by simp only [mul_inv_rev, hyinv, hminv]]
        group
      have h3 : (m * y) * u * (m * y)⁻¹ = u := by
        rw [h1, hρid u (Subgroup.mem_sup_right hu)]
      have h4 : (m * y) * u = u * (m * y) := by
        calc (m * y) * u = ((m * y) * u * (m * y)⁻¹) * (m * y) := by group
          _ = u * (m * y) := by rw [h3]
      exact h4.symm
    have hN : m * y ∈ Subgroup.normalizer (Uu : Set G) :=
      (Subgroup.centralizer_le_normalizer (Uu : Set G)) hcen
    rw [hNUeq] at hN
    have hmH : m⁻¹ ∈ B.Hhat := B.Hhat.inv_mem hmHhat
    exact hyH (by
      have h : y = m⁻¹ * (m * y) := by group
      rw [h]
      exact B.Hhat.mul_mem hmH hN)
  -- ### assembly
  have hVDbot : V ⊓ DD = ⊥ := by
    by_contra hne
    exact case1 hne
  have hUDbot : Uu ⊓ DD = ⊥ := by
    by_contra hne
    exact case2 hVDbot hne
  have hmain : VU ⊓ DD = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro a ha
    rw [Subgroup.mem_inf] at ha
    obtain ⟨haVU, haD⟩ := ha
    by_contra ha1
    obtain ⟨v, hv, u, hu, haeq⟩ := Work.CORE3.exists_mul_of_mem_sup_of_normal
      (S := B.Hhat) hVleHhat hUleHhat hVnorm'' hUnorm'' a haVU
    have hcube : a ^ 3 = v := by
      rw [haeq]
      have hcomm : Commute v u := hcommVU v hv u hu
      rw [hcomm.mul_pow]
      have hv3 : v ^ 3 = v := by
        rw [show v ^ 3 = v ^ 2 * v by rw [pow_succ],
          show v ^ 2 = 1 by simpa [pow_two] using hVsq v hv, one_mul]
      have hu3 : u ^ 3 = 1 := by
        have hd : orderOf u ∣ 3 := by rw [← hUcard]; exact Subgroup.orderOf_dvd_natCard Uu hu
        exact orderOf_dvd_iff_pow_eq_one.mp hd
      rw [hv3, hu3, mul_one]
    have hvD : v ∈ DD := by rw [← hcube]; exact DD.pow_mem haD 3
    by_cases hv1 : v = 1
    · have hmem : a ∈ Uu ⊓ DD := by
        refine ⟨?_, haD⟩
        rw [haeq, hv1, one_mul]
        exact hu
      rw [hUDbot] at hmem
      exact ha1 (Subgroup.mem_bot.mp hmem)
    · have hmem : v ∈ V ⊓ DD := ⟨hv, hvD⟩
      rw [hVDbot] at hmem
      exact hv1 (Subgroup.mem_bot.mp hmem)
  rw [hDD, hVU, hV, hU] at hmain
  exact hmain


end Work.CORE3.J4
