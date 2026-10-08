import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.thm26_aux
import Submission.Work.CORE2A.lemma24
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.SylowDihedral
import Submission.Work.CORE3.OutsideS0OrderTwo
import Submission.Work.CORE3.SylowLeCentralizer
import Submission.Work.CORE3.H_eq_U_sup_S
import Submission.OddOrder.Isaacs.Ch03_SplitExtensions.NilpotentInjector.PiParts

open scoped MatrixGroups Pointwise
open Subgroup
namespace Work.CORE3
open Work.GW2

variable {G : Type} [Group G] [Finite G]

/-- A subgroup of type (2,2) is not cyclic. -/
theorem not_isCyclic_of_isFourGroup {V : Subgroup G} (h : IsFourGroup V) : ¬ IsCyclic V := by
  intro hc
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥V)
  have hord : orderOf g = Nat.card ↥V := orderOf_eq_card_of_forall_mem_zpowers hg
  have hcard : Nat.card ↥V = 4 := h.1
  have hg2 : (g : G) ^ 2 = 1 := by
    have := h.2 (g : G) g.2
    simpa using this
  have hg2' : g ^ 2 = 1 := Subtype.ext (by simpa using hg2)
  have hdvd : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hg2'
  have h4 : orderOf g = 4 := by rw [hord, hcard]
  have hle : orderOf g ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
  omega

/-- `|A ⊔ B| = |A| * |B|` when `A` normalizes `B` and `A ⊓ B = ⊥`. -/
theorem natCard_sup_eq_mul {A B : Subgroup G}
    (hN : A ≤ Subgroup.normalizer (B : Set G)) (hinf : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  rw [← Nat.card_prod]
  refine Nat.card_congr (Equiv.ofBijective
    (fun x : ↥A × ↥B =>
      (⟨(x.1 : G) * (x.2 : G), mul_mem (Subgroup.mem_sup_left x.1.2) (Subgroup.mem_sup_right x.2.2)⟩ : ↥(A ⊔ B)))
    ⟨?_, ?_⟩).symm
  · rintro ⟨a, b⟩ ⟨a', b'⟩ hxy
    simp only [Subtype.mk.injEq] at hxy
    have h1 : (a' : G)⁻¹ * (a : G) = (b' : G) * (b : G)⁻¹ := by
      have h := congrArg (fun z => (a' : G)⁻¹ * z * (b : G)⁻¹) hxy
      simpa [mul_assoc] using h
    have h2 : (a' : G)⁻¹ * (a : G) ∈ A ⊓ B :=
      ⟨A.mul_mem (A.inv_mem a'.2) a.2, by rw [h1]; exact B.mul_mem b'.2 (B.inv_mem b.2)⟩
    rw [hinf] at h2
    simp only [Subgroup.mem_bot] at h2
    have haa : a = a' := by
      apply Subtype.ext
      calc (a : G) = (a' : G) * ((a' : G)⁻¹ * (a : G)) := by group
        _ = (a' : G) := by rw [h2, mul_one]
    have hbb : b = b' := by
      apply Subtype.ext
      rw [haa] at hxy
      exact mul_left_cancel hxy
    rw [haa, hbb]
  · intro x
    have hx : (x : G) ∈ (↑A : Set G) * (↑B : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A B hN]; exact x.2
    obtain ⟨a, ha, b, hb, hab⟩ := hx
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩

/-- Sylow conjugacy inside `Ĥ`. -/
theorem sylow_conj_hhat (B : BenderSetup G) {s : G} (hs : s ∈ B.Hhat) (hord : orderOf s = 2) :
    ∃ h : G, h ∈ B.Hhat ∧ h * s * h⁻¹ ∈ (B.S : Subgroup G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSleH : (B.S : Subgroup G) ≤ B.Hhat := Work.CORE2A.bSetup_S_le_Hhat B
  let S' : Sylow 2 ↥B.Hhat := B.S.subtype hSleH
  have hS'coe : (S' : Subgroup ↥B.Hhat) = (B.S : Subgroup G).subgroupOf B.Hhat :=
    Sylow.coe_subtype _ _
  have hQ2 : IsPGroup 2 (Subgroup.zpowers s) := by
    refine (IsPGroup.iff_card).mpr ⟨1, ?_⟩
    simp [Nat.card_zpowers, hord]
  have hQleH : Subgroup.zpowers s ≤ B.Hhat := Subgroup.zpowers_le.mpr hs
  let Q' : Subgroup ↥B.Hhat := (Subgroup.zpowers s).subgroupOf B.Hhat
  have hQ'2 : IsPGroup 2 Q' :=
    IsPGroup.of_equiv hQ2 (Subgroup.subgroupOfEquivOfLe hQleH).symm
  obtain ⟨P, hQP⟩ := IsPGroup.exists_le_sylow hQ'2
  obtain ⟨κ, hκ⟩ := MulAction.IsPretransitive.exists_smul_eq (M := ↥B.Hhat)
    (α := Sylow 2 ↥B.Hhat) S' P
  have hQle : Q' ≤ (S' : Subgroup ↥B.Hhat).map (MulAut.conj κ).toMonoidHom := by
    rw [← hκ] at hQP
    rwa [Sylow.coe_subgroup_smul, Work.CORE2A.smul_conj_eq_map] at hQP
  have hmem : (⟨s, hs⟩ : ↥B.Hhat) ∈ Q' := by
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_zpowers s
  have hmem2 := hQle hmem
  rw [Subgroup.mem_map] at hmem2
  obtain ⟨y, hy, hyx⟩ := hmem2
  have hyS : (y : G) ∈ (B.S : Subgroup G) := by
    have hy' : y ∈ (S' : Subgroup ↥B.Hhat) := hy
    rw [hS'coe, Subgroup.mem_subgroupOf] at hy'
    exact hy'
  have hyx' : (κ : G) * (y : G) * (κ : G)⁻¹ = s := by
    have := congrArg (fun z : ↥B.Hhat => (z : G)) hyx
    simpa [MulAut.conj_apply, mul_assoc] using this
  refine ⟨(κ : G)⁻¹, B.Hhat.inv_mem κ.2, ?_⟩
  have hgoal : (κ : G)⁻¹ * s * (κ : G)⁻¹⁻¹ = (y : G) := by
    rw [inv_inv, ← hyx']; group
  rw [hgoal]; exact hyS

/-- On `S \ O₂(Ĥ)`, the inverted set `I_U(s)` is constant. -/
theorem invSet_eq_of_mem_S_notMem {B : BenderSetup G}
    (h26 : Thm26Concl B) (hS8 : Nat.card (B.S : Subgroup G) = 8)
    (h4 : IsFourGroup (pCoreIn 2 B.Hhat))
    {s s' : G} (hs : s ∈ (B.S : Subgroup G)) (hs' : s' ∈ (B.S : Subgroup G))
    (hsV : s ∉ pCoreIn 2 B.Hhat) (hs'V : s' ∉ pCoreIn 2 B.Hhat) :
    invSet B.U s = invSet B.U s' := by
  have hVleS : pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) := Work.CORE2A.thm26Concl_O2_le_S h26
  have hVcU : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_centralizer_eq h26]; exact inf_le_right
  have hrel : (pCoreIn 2 B.Hhat).relIndex (B.S : Subgroup G) = 2 := by
    have h := Subgroup.relIndex_mul_card (pCoreIn 2 B.Hhat) (B.S : Subgroup G)
    rw [inf_eq_left.mpr hVleS, h4.1, hS8] at h
    omega
  have hidx : ((pCoreIn 2 B.Hhat).subgroupOf (B.S : Subgroup G)).index = 2 := hrel
  -- s'⁻¹ * s ∈ V
  have hz : s'⁻¹ * s ∈ pCoreIn 2 B.Hhat := by
    set H' : Subgroup ↥(B.S : Subgroup G) :=
      (pCoreIn 2 B.Hhat).subgroupOf (B.S : Subgroup G) with hH'def
    have hsH : (⟨s, hs⟩ : ↥(B.S : Subgroup G)) ∉ H' := by
      rw [Subgroup.mem_subgroupOf]; exact hsV
    have hs'H : (⟨s', hs'⟩ : ↥(B.S : Subgroup G)) ∉ H' := by
      rw [Subgroup.mem_subgroupOf]; exact hs'V
    have hinv : (⟨s', hs'⟩ : ↥(B.S : Subgroup G))⁻¹ ∉ H' := fun hh => hs'H (by
      rwa [← inv_mem_iff])
    have hmem : (⟨s', hs'⟩ : ↥(B.S : Subgroup G))⁻¹ * ⟨s, hs⟩ ∈ H' := by
      rw [Subgroup.mul_mem_iff_of_index_two (H := H') hidx]
      exact ⟨fun h => absurd h hinv, fun h => absurd h hsH⟩
    have := hmem
    rw [Subgroup.mem_subgroupOf] at this
    simpa using this
  -- conclude
  ext x
  constructor
  · rintro ⟨hxU, hxin⟩
    refine ⟨hxU, ?_⟩
    have hzC : s'⁻¹ * s ∈ Subgroup.centralizer (B.U : Set G) := hVcU hz
    have hcomm := (Subgroup.mem_centralizer_iff.mp hzC) x hxU
    have hzx : (s'⁻¹ * s) * x * (s'⁻¹ * s)⁻¹ = x := by
      rw [show (s'⁻¹ * s) * x = x * (s'⁻¹ * s) from hcomm.symm]; group
    calc s' * x * s'⁻¹ = s' * ((s'⁻¹ * s) * x * (s'⁻¹ * s)⁻¹) * s'⁻¹ := by rw [hzx]
      _ = s * x * s⁻¹ := by group
      _ = x⁻¹ := hxin
  · rintro ⟨hxU, hxin⟩
    refine ⟨hxU, ?_⟩
    have hzC : s'⁻¹ * s ∈ Subgroup.centralizer (B.U : Set G) := hVcU hz
    have hcomm := (Subgroup.mem_centralizer_iff.mp hzC) x hxU
    have hzx : (s'⁻¹ * s) * x * (s'⁻¹ * s)⁻¹ = x := by
      rw [show (s'⁻¹ * s) * x = x * (s'⁻¹ * s) from hcomm.symm]; group
    calc s * x * s⁻¹ = s' * ((s'⁻¹ * s) * x * (s'⁻¹ * s)⁻¹) * s'⁻¹ := by group
      _ = s' * x * s'⁻¹ := by rw [hzx]
      _ = x⁻¹ := hxin

end Work.CORE3

namespace Work.CORE3
open Work.GW2

variable {G : Type} [Group G] [Finite G]

/-- Hall subgroups of equal order in a nilpotent group coincide. -/
theorem isHallIn_eq_of_card_eq_of_nilpotent (N : Subgroup G) [Group.IsNilpotent ↥N]
    {A B : Subgroup G} (hA : IsHallIn A N) (hB : IsHallIn B N)
    (hcard : Nat.card A = Nat.card B) : A = B := by
  have hA' : OddOrder.Isaacs.Ch03.IsHallPart N A (primesOf A) := by
    refine ⟨hA.1, ?_, ?_⟩
    · intro p hp
      have hc : Nat.card ↥(A.subgroupOf N) = Nat.card ↥A :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv
      rw [hc] at hp
      rw [primesOf]
      exact hp
    · intro p hp hpA
      rw [primesOf] at hpA
      have hp' : p ∈ (A.relIndex N).primeFactors := hp
      obtain ⟨hpp, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp'
      obtain ⟨-, hpdvdA, -⟩ := Nat.mem_primeFactors.mp hpA
      have hcop : Nat.Coprime (Nat.card ↥A) (A.relIndex N) := hA.2
      rw [Nat.coprime_iff_gcd_eq_one] at hcop
      refine hpp.not_dvd_one ?_
      rw [← hcop]
      exact Nat.dvd_gcd hpdvdA hpdvd
  have hB' : OddOrder.Isaacs.Ch03.IsHallPart N B (primesOf A) := by
    refine ⟨hB.1, ?_, ?_⟩
    · intro p hp
      have hc : Nat.card ↥(B.subgroupOf N) = Nat.card ↥B :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hB.1).toEquiv
      rw [hc] at hp
      rw [primesOf, hcard]
      exact hp
    · intro p hp hpA
      rw [primesOf] at hpA
      have hp' : p ∈ (B.relIndex N).primeFactors := hp
      obtain ⟨hpp, hpdvd, -⟩ := Nat.mem_primeFactors.mp hp'
      obtain ⟨-, hpdvdA, -⟩ := Nat.mem_primeFactors.mp hpA
      have hpdvdB : p ∣ Nat.card ↥B := hcard ▸ hpdvdA
      have hcop : Nat.Coprime (Nat.card ↥B) (B.relIndex N) := hB.2
      rw [Nat.coprime_iff_gcd_eq_one] at hcop
      refine hpp.not_dvd_one ?_
      rw [← hcop]
      exact Nat.dvd_gcd hpdvdB hpdvd
  exact OddOrder.Isaacs.Ch03.IsHallPart.unique ‹Group.IsNilpotent ↥N› hA' hB'

end Work.CORE3

namespace Work.CORE3

namespace Work.CORE3

open Work.GW2

/-- Bender 1981 §3, p. 223, subcase `V = O₂(Ĥ)` of type (2,2).  Deliverable
`Work.GW2.Case1bSetupProp`.

From `Case1 B` and `IsFourGroup (pCoreIn 2 B.Hhat)`: `V = O₂(Ĥ)` is a normal four-group of `Ĥ`
with `V ≤ S`; `Ĥ/O₂(Ĥ)O(Ĥ) ≅ Z₃` or `D₃` (Bender 1.6(c), toolkit `I.T.d16`) forces `|Ĥ/O(Ĥ)| ≤ 24`
and, since `V ⊴ S` and `S` is dihedral (a four-group normal in a dihedral 2-group of order
`≥ 16` contains the centre and is necessarily non-normal, cf. `Work.CORE3.SylowDihedral`), `|S| = 8`.
Also `N_G(V) = Ĥ` (`Work.CORE3.NormalizerPcoreEqHhat`), and the Hall subgroup `K = I_U(s) ≤ F(U)`
is independent of the involution `s ∈ Ĥ − V`, with `K ≠ 1` (Bender's Lemma 2.2, `I.h22`). -/
theorem Case1bSetup (I : Case1Inputs) : Case1bSetupProp := by
  intro G _ _ hFT hBc B hCase1 h4
  classical
  have h26 : Thm26Concl B := I.h26 G hFT hBc B
  have hUnb : B.U ≠ ⊥ := Work.CORE2A.lemma22Prop_U_ne_bot I.h22 hFT hBc B
  have hUodd : Odd (Nat.card B.U) := Work.CORE2A.bSetup_U_odd B
  have hVleS : pCoreIn 2 B.Hhat ≤ (B.S : Subgroup G) := Work.CORE2A.thm26Concl_O2_le_S h26
  have hVleH : pCoreIn 2 B.Hhat ≤ B.Hhat := Work.CORE2A.thm26Concl_O2_le_Hhat h26
  have hVnc : ¬ IsCyclic (pCoreIn 2 B.Hhat) := not_isCyclic_of_isFourGroup h4
  have hVcU : pCoreIn 2 B.Hhat ≤ Subgroup.centralizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_centralizer_eq h26]; exact inf_le_right
  have hVnormH : B.Hhat ≤ Subgroup.normalizer ((pCoreIn 2 B.Hhat : Subgroup G) : Set G) := by
    simpa [pCoreIn] using le_normalizer_map_subtype B.Hhat (pCore 2 ↥B.Hhat)
  have hUnormH : B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := by
    rw [← Work.CORE2A.thm26Concl_oddCore_eq h26]
    simpa [oddCoreIn] using le_normalizer_map_subtype B.Hhat (oddCore ↥B.Hhat)
  have hSleNU : (B.S : Subgroup G) ≤ Subgroup.normalizer (B.U : Set G) :=
    le_trans (Work.CORE2A.bSetup_S_le_Hhat B) hUnormH
  have hVleNU : pCoreIn 2 B.Hhat ≤ Subgroup.normalizer (B.U : Set G) := le_trans hVleH hUnormH
  have hVU : pCoreIn 2 B.Hhat ⊓ B.U = ⊥ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2g : IsPGroup 2 ↥(pCoreIn 2 B.Hhat ⊓ B.U) :=
      B.S.isPGroup'.to_le (le_trans inf_le_left hVleS)
    have hodd : Odd (Nat.card ↥(pCoreIn 2 B.Hhat ⊓ B.U)) :=
      Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_right)
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h2g
    have hm0 : m = 0 := by
      by_contra h
      rw [hm] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (dvd_pow_self 2 h))
    exact Subgroup.card_eq_one.mp (by rw [hm, hm0]; norm_num)
  have hSU : (B.S : Subgroup G) ⊓ B.U = ⊥ := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have h2g : IsPGroup 2 ↥((B.S : Subgroup G) ⊓ B.U) :=
      B.S.isPGroup'.to_le inf_le_left
    have hodd : Odd (Nat.card ↥((B.S : Subgroup G) ⊓ B.U)) :=
      Odd.of_dvd_nat hUodd (Subgroup.card_dvd_of_le inf_le_right)
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp h2g
    have hm0 : m = 0 := by
      by_contra h
      rw [hm] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr (dvd_pow_self 2 h))
    exact Subgroup.card_eq_one.mp (by rw [hm, hm0]; norm_num)
  -- rule out the first branch of Theorem 2.6
  have hnotS0 : ¬ (pCoreIn 2 B.Hhat ≤ B.S0) := by
    intro hle
    haveI : IsCyclic ↥B.S0 := B.S0_cyclic
    haveI h1 : IsCyclic ↥((pCoreIn 2 B.Hhat).subgroupOf B.S0) := isCyclic _
    exact hVnc (isCyclic_of_surjective
      (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hle).surjective)
  obtain ⟨hrel, -⟩ : (pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 ∧
      ∃ a ∈ B.Hhat, ∃ b ∈ B.Hhat, a * b * a⁻¹ * b⁻¹ ∉ pCoreIn 2 B.Hhat ⊔ B.U := by
    rcases h26.2.2 with h | h
    · exact absurd h.1 hnotS0
    · exact h.2
  -- cardinal arithmetic
  have hcardVU : Nat.card ↥(pCoreIn 2 B.Hhat ⊔ B.U) = 4 * Nat.card B.U := by
    rw [natCard_sup_eq_mul hVleNU hVU, h4.1]
  have hcardHhat : Nat.card B.Hhat = 6 * Nat.card ↥(pCoreIn 2 B.Hhat ⊔ B.U) := by
    have h := Subgroup.relIndex_mul_card (pCoreIn 2 B.Hhat ⊔ B.U) B.Hhat
    rw [hrel, inf_eq_left.mpr (sup_le hVleH (Work.CORE2A.thm26Concl_U_le_Hhat h26))] at h
    exact h.symm
  have hHeq : B.H = (B.S : Subgroup G) ⊔ B.U := by
    rw [← H_eq_U_sup_S G I.T hBc B, sup_comm]
  have hcardH : Nat.card B.H = Nat.card (B.S : Subgroup G) * Nat.card B.U := by
    rw [hHeq, natCard_sup_eq_mul hSleNU hSU]
  have hcardHhat2 : Nat.card B.Hhat = B.H.relIndex B.Hhat * Nat.card B.H := by
    have h := Subgroup.relIndex_mul_card B.H B.Hhat
    rw [inf_eq_left.mpr B.H_le_Hhat] at h
    exact h.symm
  have hkey : (6 * 4) * Nat.card B.U =
      (B.H.relIndex B.Hhat * Nat.card (B.S : Subgroup G)) * Nat.card B.U := by
    calc (6 * 4) * Nat.card B.U = 6 * (4 * Nat.card B.U) := by ring
      _ = 6 * Nat.card ↥(pCoreIn 2 B.Hhat ⊔ B.U) := by rw [hcardVU]
      _ = Nat.card B.Hhat := hcardHhat.symm
      _ = B.H.relIndex B.Hhat * Nat.card B.H := hcardHhat2
      _ = B.H.relIndex B.Hhat * (Nat.card (B.S : Subgroup G) * Nat.card B.U) := by rw [hcardH]
      _ = (B.H.relIndex B.Hhat * Nat.card (B.S : Subgroup G)) * Nat.card B.U := by ring
  have hcancel : 6 * 4 = B.H.relIndex B.Hhat * Nat.card (B.S : Subgroup G) :=
    Nat.mul_right_cancel Nat.card_pos hkey
  have hdiv : Nat.card (B.S : Subgroup G) ∣ 24 := by
    rw [show (24:ℕ) = 6 * 4 from by norm_num, hcancel]
    exact ⟨_, mul_comm _ _⟩
  have hSge : 4 ≤ Nat.card (B.S : Subgroup G) := by
    have hle : Nat.card ↥(pCoreIn 2 B.Hhat) ≤ Nat.card ↥(B.S : Subgroup G) :=
      Nat.card_le_card_of_injective
        (fun v : ↥(pCoreIn 2 B.Hhat) => (⟨(v : G), hVleS v.2⟩ : ↥(B.S : Subgroup G)))
        (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
    rw [h4.1] at hle
    exact hle
  have h8 : Nat.card (B.S : Subgroup G) = 8 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp B.S.isPGroup'
    rw [hm] at hdiv hSge
    have hmge : 2 ≤ m := by
      by_contra h
      have hm1 : m ≤ 1 := by omega
      interval_cases m <;> simp only [pow_zero, pow_one] at hSge <;> omega
    have hmle : m ≤ 3 := by
      have hcop : Nat.Coprime ((2:ℕ)^m) 3 := Nat.Coprime.pow_left m (by norm_num)
      have h2 : (2:ℕ)^m ∣ 2^3 := by
        refine hcop.dvd_of_dvd_mul_right ?_
        rw [show (2:ℕ)^3 * 3 = 24 from by norm_num]
        exact hdiv
      exact (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < (2:ℕ))).mp h2
    have hm23 : m = 2 ∨ m = 3 := by omega
    rcases hm23 with rfl | rfl
    · exfalso
      have hS4 : Nat.card (B.S : Subgroup G) = 4 := by rw [hm]; norm_num
      have hVS : (B.S : Subgroup G) = pCoreIn 2 B.Hhat :=
        (Subgroup.eq_of_le_of_card_ge hVleS (by rw [hS4, h4.1])).symm
      have hSleCU : (B.S : Subgroup G) ≤ Subgroup.centralizer (B.U : Set G) := by
        rw [hVS]; exact hVcU
      have hconfig : (B.S0 ≤ Subgroup.centralizer (B.U : Set G)) ∧
          ∃ s ∈ (B.S : Subgroup G), s ∉ B.S0 ∧ ∃ I : Subgroup G,
            (I : Set G) = invSet B.U s ∧ (I.subgroupOf B.U).Normal ∧
            ∀ X : Subgroup G, X ≠ ⊥ → X ≤ I → Subgroup.normalizer (X : Set G) ≤ B.H := by
        refine ⟨le_trans B.S0_le hSleCU, ?_⟩
        obtain ⟨s, hsS, hs0⟩ := Work.CORE2A.bSetup_exists_mem_S_not_mem_S0 B
        refine ⟨s, hsS, hs0, ⊥, ?_, ?_, ?_⟩
        · have hsCU : s ∈ Subgroup.centralizer (B.U : Set G) := hSleCU hsS
          ext x
          rw [Subgroup.coe_bot, Set.mem_singleton_iff, Work.CORE2A.mem_invSet]
          constructor
          · rintro rfl; exact ⟨B.U.one_mem, by simp⟩
          · rintro ⟨hxU, hxin⟩
            have hcomm := (Subgroup.mem_centralizer_iff.mp hsCU) x hxU
            have hxc : s * x * s⁻¹ = x := by
              rw [show s * x = x * s from hcomm.symm]; group
            have hxinv : x = x⁻¹ := by rw [← hxin, hxc]
            have hx2 : x ^ 2 = 1 := by
              rw [pow_two]
              nth_rewrite 1 [hxinv]
              exact inv_mul_cancel x
            have hdvd : orderOf x ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hx2
            have hoddx : Odd (orderOf x) :=
              Odd.of_dvd_nat hUodd (Subgroup.orderOf_dvd_natCard B.U hxU)
            rcases (Nat.dvd_prime (by norm_num : Nat.Prime 2)).mp hdvd with h | h
            · exact orderOf_eq_one_iff.mp h
            · exact absurd (h ▸ (show Even 2 from ⟨1, by norm_num⟩)) (Nat.not_even_iff_odd.mpr hoddx)
        · show ((⊥ : Subgroup G).subgroupOf B.U).Normal
          infer_instance
        · intro X hX hXbot
          exact absurd (le_bot_iff.mp hXbot) hX
      exact (I.h22 G hFT hBc B) hconfig
    · rw [hm]; norm_num

  -- an involution of `S` outside `S₀` and outside `V`
  have hS0card : Nat.card B.S0 = 4 := by
    have h := Subgroup.relIndex_mul_card B.S0 (B.S : Subgroup G)
    rw [inf_eq_left.mpr B.S0_le, B.S0_index, h8] at h
    omega
  have hexists : ∃ s ∈ (B.S : Subgroup G), s ∉ B.S0 ∧ s ∉ pCoreIn 2 B.Hhat := by
    by_contra hcon
    push_neg at hcon
    have hSsub : ∀ x ∈ (B.S : Subgroup G), x ∈ B.S0 ∨ x ∈ pCoreIn 2 B.Hhat := by
      intro x hx
      by_cases hx0 : x ∈ B.S0
      · exact Or.inl hx0
      · exact Or.inr (hcon x hx hx0)
    have hS0notleV : ¬ B.S0 ≤ pCoreIn 2 B.Hhat := by
      intro hle
      have heq : B.S0 = pCoreIn 2 B.Hhat :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [hS0card, h4.1])
      exact hVnc (heq ▸ B.S0_cyclic)
    have hVnotleS0 : ¬ pCoreIn 2 B.Hhat ≤ B.S0 := by
      intro hle
      haveI : IsCyclic ↥B.S0 := B.S0_cyclic
      haveI h1 : IsCyclic ↥((pCoreIn 2 B.Hhat).subgroupOf B.S0) := isCyclic _
      exact hVnc (isCyclic_of_surjective
        (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hle).surjective)
    obtain ⟨a, haS0, haV⟩ := Set.not_subset.mp hS0notleV
    obtain ⟨b, hbV, hbS0⟩ := Set.not_subset.mp hVnotleS0
    have habS : a * b ∈ (B.S : Subgroup G) :=
      (B.S).mul_mem (B.S0_le haS0) (hVleS hbV)
    rcases hSsub (a * b) habS with h | h
    · apply hbS0
      have := (B.S0).mul_mem ((B.S0).inv_mem haS0) h
      rwa [show a⁻¹ * (a * b) = b from by group] at this
    · apply haV
      have := (pCoreIn 2 B.Hhat).mul_mem h ((pCoreIn 2 B.Hhat).inv_mem hbV)
      rwa [show a * b * b⁻¹ = a from by group] at this
  obtain ⟨s₁, hs₁S, hs₁S0, hs₁V⟩ := hexists
  obtain ⟨n, hn2, ⟨e⟩⟩ := SylowDihedral G hBc B
  have hn4 : n = 4 := by
    have hcard : Nat.card ↥(B.S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    rw [h8] at hcard; omega
  subst hn4
  have hs₁ord : orderOf s₁ = 2 :=
    OutsideS0OrderTwo G hBc B 4 (by norm_num) ⟨e⟩ s₁ hs₁S hs₁S0
  -- K from Case 1
  obtain ⟨K, hKset, hKhall⟩ := hCase1.1 s₁ hs₁S hs₁S0
  have hs₁norm : s₁ ∈ Subgroup.normalizer (B.U : Set G) := hSleNU hs₁S
  have hCUprop : B.U ⊓ Subgroup.centralizer ({s₁} : Set G) ≠ B.U := by
    intro heq
    have hs₁CU : s₁ ∈ Subgroup.centralizer (B.U : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : u ∈ B.U ⊓ Subgroup.centralizer ({s₁} : Set G) := by rw [heq]; exact hu
      exact ((Subgroup.mem_centralizer_iff.mp hu'.2) s₁ (by simp)).symm
    apply hs₁V
    rw [← Work.CORE2A.thm26Concl_centralizer_eq h26]
    exact ⟨hs₁S, hs₁CU⟩
  have hCUlt : Nat.card ↥(B.U ⊓ Subgroup.centralizer ({s₁} : Set G)) < Nat.card ↥B.U := by
    have hle : Nat.card ↥(B.U ⊓ Subgroup.centralizer ({s₁} : Set G)) ≤ Nat.card ↥B.U :=
      Nat.card_le_card_of_injective
        (fun x : ↥(B.U ⊓ Subgroup.centralizer ({s₁} : Set G)) =>
          (⟨(x : G), x.2.1⟩ : ↥B.U))
        (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
    rcases lt_or_eq_of_le hle with h | h
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge inf_le_left h.ge) hCUprop
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have hset1 : invSet B.U s₁ = {1} := by rw [← hKset, hKbot, Subgroup.coe_bot]
    have hcard1 : (invSet B.U s₁).ncard = 1 := by rw [hset1, Set.ncard_singleton]
    obtain ⟨-, h15, -⟩ := I.T.c15 G hFT B.U s₁ hs₁ord hUodd hs₁norm
    rw [hcard1, one_mul] at h15
    exact absurd h15 (Nat.ne_of_lt hCUlt)
  -- Nilpotency of F(U)
  haveI hFnil : Group.IsNilpotent ↥(fittingIn B.U) := by
    change Group.IsNilpotent ↥((Work.GW2.fitting ↥B.U).map B.U.subtype)
    rw [Work.CORE2A.fitting_eq_isaacsFitting]
    exact (Group.isNilpotent_congr
      (Subgroup.equivMapOfInjective (OddOrder.Isaacs.Ch01.fitting ↥B.U) B.U.subtype
        B.U.subtype_injective)).mp
      (OddOrder.Isaacs.Ch01.fitting.isNilpotent (G := ↥B.U))
  have hinv : ∀ s ∈ B.Hhat, orderOf s = 2 → s ∉ pCoreIn 2 B.Hhat →
      (K : Set G) = invSet B.U s := by
    intro s hsH hsord hsV
    obtain ⟨h, hhH, hhS⟩ := sylow_conj_hhat B hsH hsord
    have hs'V : h * s * h⁻¹ ∉ pCoreIn 2 B.Hhat := by
      intro hmem
      apply hsV
      have h1 := (Subgroup.mem_normalizer_iff.mp (hVnormH (B.Hhat.inv_mem hhH)) (h * s * h⁻¹)).mp hmem
      rwa [show h⁻¹ * (h * s * h⁻¹) * (h⁻¹)⁻¹ = s from by group] at h1
    have hinvset : invSet B.U (h * s * h⁻¹) = invSet B.U s₁ :=
      invSet_eq_of_mem_S_notMem h26 h8 h4 hhS hs₁S hs'V hs₁V
    have hKset_h : (K : Set G) = invSet B.U (h * s * h⁻¹) := by rw [hKset, hinvset]
    have hN : h ∈ Subgroup.normalizer (B.U : Set G) := hUnormH hhH
    have hNinv : h⁻¹ ∈ Subgroup.normalizer (B.U : Set G) := hUnormH (B.Hhat.inv_mem hhH)
    have hconj : (Work.GW2.conjSub h⁻¹ K : Set G) = invSet B.U s := by
      refine Set.ext fun z => ?_
      change z ∈ Work.GW2.conjSub h⁻¹ K ↔ z ∈ invSet B.U s
      rw [Work.CORE2A.mem_conjSub_iff']
      constructor
      · intro hz
        rw [Work.CORE2A.mem_invSet]
        have hz' : h * z * h⁻¹ ∈ invSet B.U (h * s * h⁻¹) := by
          rw [← hKset_h]; exact hz
        rw [Work.CORE2A.mem_invSet] at hz'
        obtain ⟨hzU, hzeq⟩ := hz'
        refine ⟨?_, ?_⟩
        · have h1 := (Subgroup.mem_normalizer_iff.mp hNinv) (h * z * h⁻¹)
          rw [inv_inv, show h⁻¹ * (h * z * h⁻¹) * h = z from by group] at h1
          exact h1.mp hzU
        · have heq' : h * (s * z * s⁻¹) * h⁻¹ = h * z⁻¹ * h⁻¹ := by
            calc h * (s * z * s⁻¹) * h⁻¹
                = (h * s * h⁻¹) * (h * z * h⁻¹) * (h * s * h⁻¹)⁻¹ := by group
              _ = (h * z * h⁻¹)⁻¹ := hzeq
              _ = h * z⁻¹ * h⁻¹ := by group
          have h2 : s * z * s⁻¹ = z⁻¹ := by
            have := congrArg (fun w => h⁻¹ * w * h) heq'
            simpa [mul_assoc] using this
          exact h2
      · intro hz
        rw [Work.CORE2A.mem_invSet] at hz
        obtain ⟨hzU, hzeq⟩ := hz
        have hz' : h * z * h⁻¹ ∈ invSet B.U (h * s * h⁻¹) := by
          rw [Work.CORE2A.mem_invSet]
          exact ⟨(Subgroup.mem_normalizer_iff.mp hN z).mp hzU, by
            calc (h * s * h⁻¹) * (h * z * h⁻¹) * (h * s * h⁻¹)⁻¹
                = h * (s * z * s⁻¹) * h⁻¹ := by group
              _ = h * z⁻¹ * h⁻¹ := by rw [hzeq]
              _ = (h * z * h⁻¹)⁻¹ := by group⟩
        exact (Set.ext_iff.mp hKset_h (h * z * h⁻¹)).mpr hz'
    have hsnorm : s ∈ Subgroup.normalizer (B.U : Set G) := hUnormH hsH
    obtain ⟨-, -, h15s⟩ := I.T.c15 G hFT B.U s hsord hUodd hsnorm
    have hle' : Work.GW2.conjSub h⁻¹ K ≤ fittingIn B.U := by
      have := h15s (Work.GW2.conjSub h⁻¹ K) hconj
      exact this.2.2
    have hKhall' : IsHallIn (Work.GW2.conjSub h⁻¹ K) (fittingIn B.U) := by
      refine ⟨hle', ?_⟩
      have h1 : (Work.GW2.conjSub h⁻¹ K).relIndex (fittingIn B.U) *
          Nat.card ↥(Work.GW2.conjSub h⁻¹ K) = Nat.card ↥(fittingIn B.U) := by
        have hinf : Work.GW2.conjSub h⁻¹ K ⊓ fittingIn B.U = Work.GW2.conjSub h⁻¹ K :=
          inf_eq_left.mpr hle'
        have := Subgroup.relIndex_mul_card (Work.GW2.conjSub h⁻¹ K) (fittingIn B.U)
        rwa [hinf] at this
      have h2 : K.relIndex (fittingIn B.U) * Nat.card ↥K = Nat.card ↥(fittingIn B.U) := by
        have hinf : K ⊓ fittingIn B.U = K := inf_eq_left.mpr hKhall.1
        have := Subgroup.relIndex_mul_card K (fittingIn B.U)
        rwa [hinf] at this
      have hcard := Work.CORE2A.card_conjSub h⁻¹ K
      have hrel : (Work.GW2.conjSub h⁻¹ K).relIndex (fittingIn B.U) =
          K.relIndex (fittingIn B.U) := by
        rw [hcard] at h1
        exact Nat.mul_right_cancel Nat.card_pos (h1.trans h2.symm)
      rw [hrel, hcard]
      exact hKhall.2
    have hKeq : Work.GW2.conjSub h⁻¹ K = K :=
      isHallIn_eq_of_card_eq_of_nilpotent (fittingIn B.U) hKhall' hKhall
        (Work.CORE2A.card_conjSub h⁻¹ K)
    rw [← hKeq]
    exact hconj
  exact ⟨K, h4, h8, hKhall, hKne, hinv⟩

end Work.CORE3

end Work.CORE3

namespace Work.CORE3

open Work.GW2

/-- The same statement, exposed under the name `Work.CORE3.Case1bSetup` used by the CORE3
assembly and by the harness (the module's main proof sits in the doubly nested namespace
`Work.CORE3.Work.CORE3`, the skeleton's original layout). -/
theorem Case1bSetup (I : Case1Inputs) : Case1bSetupProp :=
  _root_.Work.CORE3.Work.CORE3.Case1bSetup I

end Work.CORE3
