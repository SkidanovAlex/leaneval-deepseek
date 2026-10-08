import Mathlib
import Submission.Work.CORE2A.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.PcoreInBasic
import Submission.Work.CORE2A.dihedral_index_two
import Submission.Work.CORE2A.relIndex_le_two_of_fourGroup_normal
import Submission.Work.CORE2A.relIndex_S_V_eq_two
import Submission.Work.CORE2A.thm26a_U_eq_Ohat
import Submission.Work.CORE2A.le_oddCoreIn_of_normal_of_odd
import Submission.Work.CORE2A.inf_U_S_eq_bot
import Submission.Work.CORE2A.oneInvClassIn_of_sylow_le_of_involutions_conj
import Submission.Work.CORE2A.isFourGroup_closure_pair
import Submission.Work.CORE3.H_eq_U_sup_S

namespace Work.CORE2A

open Subgroup
open Work.GW2

set_option linter.style.haveILetI false
set_option linter.unusedVariables false

variable {G : Type} [Group G] [Finite G]

/-! ## 0. The element structure of a Klein four-group -/

/-- For commuting involutions `u, v` in a group, the subgroup `⟨{u, v}⟩` is exactly
`{1, u, v, uv}`.  (Private copy of the corresponding helper of `isFourGroup_closure_pair`.) -/
private theorem mem_closure_pair_of_sq_eq_one {G : Type*} [Group G] {u v x : G}
    (hu : u ^ 2 = 1) (hv : v ^ 2 = 1) (hc : u * v = v * u) :
    x ∈ Subgroup.closure ({u, v} : Set G) ↔ x = 1 ∨ x = u ∨ x = v ∨ x = u * v := by
  have hu2 : u * u = 1 := by simpa [pow_two] using hu
  have hv2 : v * v = 1 := by simpa [pow_two] using hv
  have hcs : v * u = u * v := hc.symm
  have hu' : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu2
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have huuv : u * (u * v) = v := by rw [← mul_assoc, hu2, one_mul]
  have huvv : (u * v) * v = u := by rw [mul_assoc, hv2, mul_one]
  have hvuv : v * (u * v) = u := by rw [← mul_assoc, ← hc, huvv]
  have huvu : (u * v) * u = v := by rw [mul_assoc, ← hc, ← mul_assoc, hu2, one_mul]
  have huvuv : (u * v) * (u * v) = 1 := by rw [← mul_assoc, huvu, hv2]
  have huv' : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right huvuv
  constructor
  · intro hx
    refine Subgroup.closure_induction (k := ({u, v} : Set G))
      (p := fun y (_ : y ∈ Subgroup.closure ({u, v} : Set G)) =>
        y = 1 ∨ y = u ∨ y = v ∨ y = u * v) ?_ ?_ ?_ ?_ hx
    · rintro y hy
      rcases hy with rfl | rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
    · exact Or.inl rfl
    · rintro x y _ _ hx' hy'
      rcases hx' with rfl | rfl | rfl | rfl <;> rcases hy' with rfl | rfl | rfl | rfl <;>
        simp [hu2, hv2, hcs, huuv, hvuv, huvu, huvv, huvuv]
    · rintro x _ hx'
      rcases hx' with rfl | rfl | rfl | rfl <;> simp [hu', hv', huv']
  · rintro (rfl | rfl | rfl | rfl)
    · exact one_mem _
    · exact Subgroup.subset_closure (by simp)
    · exact Subgroup.subset_closure (by simp)
    · exact mul_mem (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp))

/-- In a Klein four-group `V`, two distinct nonidentity elements `t, s` generate `V`, and every
element of `V` is one of `1, t, s, ts`. -/
theorem fourGroup_mem_structure {V : Subgroup G} (hV4 : Work.GW2.IsFourGroup V) {t s : G}
    (ht : t ∈ V) (hs : s ∈ V) (ht1 : t ≠ 1) (hs1 : s ≠ 1) (hts : t ≠ s) :
    ∀ x ∈ V, x = 1 ∨ x = t ∨ x = s ∨ x = t * s := by
  haveI : IsMulCommutative ↥V := Work.CORE2A.IsFourGroup.isMulCommutative' hV4
  have hcomm : t * s = s * t :=
    congrArg Subtype.val (mul_comm' (⟨t, ht⟩ : ↥V) (⟨s, hs⟩ : ↥V))
  have ht2 : t ^ 2 = 1 := hV4.2 t ht
  have hs2 : s ^ 2 = 1 := hV4.2 s hs
  have hcard : Nat.card ↥(Subgroup.closure ({t, s} : Set G)) = 4 :=
    (Work.CORE2A.isFourGroup_closure_pair ht2 hs2 hcomm ht1 hs1 hts).1
  have hWle : Subgroup.closure ({t, s} : Set G) ≤ V := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact ht
    · exact hs
  have hWV : Subgroup.closure ({t, s} : Set G) = V :=
    Subgroup.eq_of_le_of_card_ge hWle (by rw [hcard, hV4.1])
  intro x hx
  rw [← hWV] at hx
  exact (mem_closure_pair_of_sq_eq_one (u := t) (v := s) ht2 hs2 hcomm).mp hx

/-! ## 1. Elementary Bender-setup facts -/

/-- `|S| ≥ 4`. -/
theorem card_S_ge_four' (B : Work.GW2.BenderSetup G) :
    4 ≤ Nat.card ↥(B.S : Subgroup G) := by
  have h2 : 2 ≤ Nat.card ↥B.S0 := by
    have hle : Subgroup.zpowers B.t ≤ B.S0 := Subgroup.zpowers_le.mpr B.t_mem
    have hcard : Nat.card ↥(Subgroup.zpowers B.t) ≤ Nat.card ↥B.S0 :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
    rw [Nat.card_zpowers, B.t_order] at hcard
    exact hcard
  have h := bSetup_card_S_eq B
  omega

/-- `S` is dihedral of order `2n`, `n ≥ 2`. -/
theorem exists_dihedral_S' (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) :
    ∃ n : ℕ, 2 ≤ n ∧ Nonempty ((B.S : Subgroup G) ≃* DihedralGroup n) := by
  have h2 : 2 ≤ Nat.card (B.S : Subgroup G) := by have := card_S_ge_four' B; omega
  rcases hctx.sylow B.S with hcyc | ⟨n, hn⟩
  · exact absurd hcyc (sylow_two_not_isCyclic hctx.simple hctx.nonab B.S h2)
  · obtain ⟨e⟩ := hn
    have hcard : Nat.card (B.S : Subgroup G) = 2 * n := by
      rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
    have h4 := card_S_ge_four' B
    exact ⟨n, by omega, ⟨e⟩⟩

/-- `G` has no normal subgroup of index `2`: `G` is simple and non-abelian. -/
theorem no_normal_index_two' (hctx : Work.GW2.BenderCtx G) :
    ∀ N : Subgroup G, N.Normal → N.index ≠ 2 := by
  haveI : IsSimpleGroup G := hctx.simple
  intro N hN h2
  haveI : N.Normal := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with hbot | htop
  · rw [hbot, Subgroup.index_bot] at h2
    obtain ⟨a, b, hab⟩ := hctx.nonab
    refine hab ?_
    have hall : ∀ x : G, x * x = 1 := fun x => by
      have h : orderOf x ∣ 2 := h2 ▸ orderOf_dvd_natCard x
      have h1 := orderOf_dvd_iff_pow_eq_one.mp h
      simpa [pow_two] using h1
    have hinv : ∀ x : G, x⁻¹ = x := fun x => inv_eq_iff_mul_eq_one.mpr (hall x)
    calc a * b = (a * b)⁻¹⁻¹ := by simp
      _ = (b⁻¹ * a⁻¹)⁻¹ := by rw [mul_inv_rev]
      _ = (b * a)⁻¹ := by rw [hinv a, hinv b]
      _ = b * a := hinv (b * a)
  · rw [htop, Subgroup.index_top] at h2
    exact absurd h2 (by norm_num)

/-- `t ∈ O₂(Ĥ)` when `O₂(Ĥ)` is a four-group not contained in `S₀`. -/
theorem t_mem_pCoreIn_of_not_le_S0 (B : Work.GW2.BenderSetup G)
    (hV4 : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat))
    (hnot : ¬ Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0) :
    B.t ∈ Work.GW2.pCoreIn 2 B.Hhat := by
  have hVne : Work.GW2.pCoreIn 2 B.Hhat ≠ ⊥ := by
    intro h
    have hc : Nat.card ↥(Work.GW2.pCoreIn 2 B.Hhat) = 1 := by
      rw [h]; exact Subgroup.card_bot
    have : (1 : ℕ) = 4 := hc.symm.trans hV4.1
    omega
  obtain ⟨-, ht | ⟨hc, -⟩⟩ := pCoreIn_dichotomy B hVne
  · exact ht
  · exfalso
    have : (2 : ℕ) = 4 := hc.symm.trans hV4.1
    omega

/-! ## 2. `O(Ĥ) ≤ U` when `t ∈ O₂(Ĥ)` -/

/-- `O(Ĥ)` centralizes `O₂(Ĥ)`: they are normal subgroups of `Ĥ` of coprime order. -/
theorem oddCoreIn_le_centralizer_pCoreIn (B : Work.GW2.BenderSetup G) :
    Work.GW2.oddCoreIn B.Hhat ≤ Subgroup.centralizer ((Work.GW2.pCoreIn 2 B.Hhat) : Set G) := by
  have hOle : Work.GW2.oddCoreIn B.Hhat ≤ B.Hhat := Subgroup.map_subtype_le _
  have hVle : Work.GW2.pCoreIn 2 B.Hhat ≤ B.Hhat := Subgroup.map_subtype_le _
  have hOn := oddCoreIn_normal_inSelf B.Hhat
  have hVn := pCoreIn_subgroupOf_normal B
  have hOodd : Odd (Nat.card ↥(Work.GW2.oddCoreIn B.Hhat)) := by
    rw [Work.GW2.oddCoreIn, Subgroup.card_map_of_injective B.Hhat.subtype_injective]
    exact Work.ASM.oddCore_odd ↥B.Hhat
  have hbot : Work.GW2.oddCoreIn B.Hhat ⊓ Work.GW2.pCoreIn 2 B.Hhat = ⊥ :=
    inf_eq_bot_of_odd_of_isPGroup_two hOodd (pCoreIn_isPGroup_two B)
  exact le_centralizer_of_normal_of_inf_eq_bot hOle hVle hOn hVn hbot

/-- **Bender p. 220**: if `t ∈ O₂(Ĥ)` then `O(Ĥ) ≤ U = O(H)`. -/
theorem oddCoreIn_le_U_of_t_mem (B : Work.GW2.BenderSetup G)
    (htV : B.t ∈ Work.GW2.pCoreIn 2 B.Hhat) : Work.GW2.oddCoreIn B.Hhat ≤ B.U := by
  have hOleC := oddCoreIn_le_centralizer_pCoreIn B
  have hOleH : Work.GW2.oddCoreIn B.Hhat ≤ B.H := by
    intro z hz
    rw [show B.H = Subgroup.centralizer ({B.t} : Set G) from rfl, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_iff.mp (hOleC hz) B.t htV
  have hOodd : Odd (Nat.card ↥(Work.GW2.oddCoreIn B.Hhat)) := by
    rw [Work.GW2.oddCoreIn, Subgroup.card_map_of_injective B.Hhat.subtype_injective]
    exact Work.ASM.oddCore_odd ↥B.Hhat
  have hOleHhat : Work.GW2.oddCoreIn B.Hhat ≤ B.Hhat := Subgroup.map_subtype_le _
  have hOnH : ((Work.GW2.oddCoreIn B.Hhat).subgroupOf B.H).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hOleH]
    intro a b ha hb
    exact (Subgroup.normal_subgroupOf_iff hOleHhat).mp
      (oddCoreIn_normal_inSelf B.Hhat) a b ha (B.H_le_Hhat hb)
  exact le_oddCoreIn_of_normal_of_odd hOleH hOnH hOodd

/-! ## 3. `H ≠ Ĥ` -/

/-- `Ĥ ≠ H = C(t)` when `O₂(Ĥ)` is a four-group not contained in `S₀`. -/
theorem Hhat_ne_H_of_not_le_S0 (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop)
    (hFT : Work.GW2.FeitThompsonProp) (hctx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G)
    (hV4 : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat))
    (hnot : ¬ Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0) :
    B.Hhat ≠ B.H := by
  intro hEq
  haveI : IsSimpleGroup G := hctx.simple
  set V := Work.GW2.pCoreIn 2 B.Hhat with hVdef
  have htV : B.t ∈ V := t_mem_pCoreIn_of_not_le_S0 B hV4 hnot
  have hVleHhat : V ≤ B.Hhat := Subgroup.map_subtype_le _
  have hVn := pCoreIn_subgroupOf_normal B
  have hleN : B.Hhat ≤ Subgroup.normalizer (V : Set G) := by
    intro h hh
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      exact (Subgroup.normal_subgroupOf_iff hVleHhat).mp hVn v h hv hh
    · intro hv
      have h2 : h⁻¹ * (h * v * h⁻¹) * (h⁻¹)⁻¹ ∈ V :=
        (Subgroup.normal_subgroupOf_iff hVleHhat).mp hVn (h * v * h⁻¹) h⁻¹ hv
          (B.Hhat.inv_mem hh)
      have h3 : h⁻¹ * (h * v * h⁻¹) * (h⁻¹)⁻¹ = v := by group
      rw [h3] at h2
      exact h2
  have hVne : V ≠ ⊥ := by
    intro h
    have hc : Nat.card ↥V = 1 := by rw [h]; exact Subgroup.card_bot
    have : (1 : ℕ) = 4 := hc.symm.trans hV4.1
    omega
  have hNG : Subgroup.normalizer (V : Set G) = B.Hhat :=
    normalizer_eq_of_coatom B.Hhat_coatom hVleHhat hVne hleN
  have hlt : Subgroup.zpowers B.t < V := by
    refine lt_of_le_of_ne (Subgroup.zpowers_le.mpr htV) ?_
    intro heq
    have hcard : Nat.card ↥(Subgroup.zpowers B.t) = Nat.card ↥V := by rw [heq]
    rw [Nat.card_zpowers, B.t_order] at hcard
    have h4 := hV4.1
    omega
  obtain ⟨s, hsV, hszp⟩ := SetLike.exists_of_lt hlt
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hszp
    exact hszp (Subgroup.one_mem (Subgroup.zpowers B.t))
  have hst : s ≠ B.t := by
    intro h
    rw [h] at hszp
    exact hszp (Subgroup.mem_zpowers B.t)
  obtain ⟨n, hn2, hdih⟩ := exists_dihedral_S' hctx B
  have hnoN := no_normal_index_two' hctx
  obtain ⟨g, hgN, hgt⟩ :=
    (T.fus G B.S n hn2 hdih hnoN).2 V hV4 B.t htV s hsV (bSetup_t_ne_one B) hs1
  rw [hNG, hEq] at hgN
  have hcomm : B.t * g = g * B.t :=
    Subgroup.mem_centralizer_iff.mp hgN B.t (Set.mem_singleton B.t)
  have h1 : g * B.t * g⁻¹ = B.t := by rw [← hcomm]; group
  rw [h1] at hgt
  exact hst hgt.symm

/-! ## 4. `[Ĥ : H] = 3` -/

/-- `[Ĥ : H] = 3` in the second case of Bender's Theorem 2.6. -/
theorem H_relIndex_Hhat_eq_three (T : Work.GW2.LocalToolkit) (h21 : Work.GW2.Lemma21Prop)
    (hFT : Work.GW2.FeitThompsonProp) (hctx : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G)
    (hV4 : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat))
    (hnot : ¬ Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0)
    (hrel : ((Work.GW2.pCoreIn 2 B.Hhat ⊔ Work.GW2.oddCoreIn B.Hhat).relIndex B.Hhat = 3 ∨
        (Work.GW2.pCoreIn 2 B.Hhat ⊔ Work.GW2.oddCoreIn B.Hhat).relIndex B.Hhat = 6)) :
    B.H.relIndex B.Hhat = 3 := by
  set V := Work.GW2.pCoreIn 2 B.Hhat with hVdef
  set O := Work.GW2.oddCoreIn B.Hhat with hOdef
  set C := Subgroup.centralizer (V : Set G) ⊓ B.Hhat with hCdef
  have htV : B.t ∈ V := t_mem_pCoreIn_of_not_le_S0 B hV4 hnot
  have hVleHhat : V ≤ B.Hhat := Subgroup.map_subtype_le _
  have hOleHhat : O ≤ B.Hhat := Subgroup.map_subtype_le _
  have hVleC : V ≤ C := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨?_, hVleHhat hx⟩
    haveI : IsMulCommutative ↥V := Work.CORE2A.IsFourGroup.isMulCommutative' hV4
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : ↥V) (⟨x, hx⟩ : ↥V))
  have hOleC : O ≤ C := by
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨oddCoreIn_le_centralizer_pCoreIn B hx, hOleHhat hx⟩
  have hCleH : C ≤ B.H := by
    intro z hz
    obtain ⟨hzC, -⟩ := Subgroup.mem_inf.mp hz
    rw [show B.H = Subgroup.centralizer ({B.t} : Set G) from rfl, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_iff.mp hzC B.t htV
  have hdiv1 : B.H.relIndex B.Hhat ∣ C.relIndex B.Hhat :=
    Subgroup.relIndex_dvd_of_le_left B.Hhat hCleH
  have hdiv2 : C.relIndex B.Hhat ∣ (V ⊔ O).relIndex B.Hhat :=
    Subgroup.relIndex_dvd_of_le_left B.Hhat (sup_le hVleC hOleC)
  have hdvd : B.H.relIndex B.Hhat ∣ 3 ∨ B.H.relIndex B.Hhat ∣ 6 := by
    rcases hrel with h | h
    · exact Or.inl (h ▸ dvd_trans hdiv1 hdiv2)
    · exact Or.inr (h ▸ dvd_trans hdiv1 hdiv2)
  have hodd : Odd (B.H.relIndex B.Hhat) := by
    have h2 : ¬ 2 ∣ B.H.relIndex B.Hhat :=
      not_two_dvd_relIndex_of_sylow_le B.S (bSetup_S_le_Hhat B) B.H_le_Hhat (bSetup_S_le_H B)
    exact Nat.not_even_iff_odd.mp (fun he => h2 (even_iff_two_dvd.mp he))
  have hne1 : B.H.relIndex B.Hhat ≠ 1 := by
    intro h1
    exact Hhat_ne_H_of_not_le_S0 T h21 hFT hctx B hV4 hnot
      (le_antisymm (Subgroup.relIndex_eq_one.mp h1) B.H_le_Hhat)
  rcases hdvd with hd | hd
  · rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact absurd h1 hne1
    · exact h3
  · have hc : Nat.Coprime (B.H.relIndex B.Hhat) 2 := (Nat.coprime_two_right).mpr hodd
    have h3 : B.H.relIndex B.Hhat ∣ 3 := hc.dvd_of_dvd_mul_left (by simpa using hd)
    rcases (Nat.dvd_prime Nat.prime_three).mp h3 with h1 | h3'
    · exact absurd h1 hne1
    · exact h3'

/-! ## 5. `[H : O₂(Ĥ)·U] = 2` -/

/-- **Bender p. 219 / 2.6**: `H = U ⋊ S` and `[S : O₂(Ĥ)] = 2` give `[H : O₂(Ĥ)·U] = 2`. -/
theorem sup_V_U_relIndex_H_eq_two (T : Work.GW2.LocalToolkit) (hFT : Work.GW2.FeitThompsonProp)
    (hctx : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G)
    (hV4 : Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat))
    (hSV : (Work.GW2.pCoreIn 2 B.Hhat).relIndex (B.S : Subgroup G) = 2) :
    (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.H = 2 := by
  set V := Work.GW2.pCoreIn 2 B.Hhat with hVdef
  set U := B.U with hUdef
  have hHSU : U ⊔ (B.S : Subgroup G) = B.H := Work.CORE3.H_eq_U_sup_S G T hctx B
  have hUleH : U ≤ B.H := by rw [← hHSU]; exact le_sup_left
  have hSleH : (B.S : Subgroup G) ≤ B.H := by rw [← hHSU]; exact le_sup_right
  have hVleH : V ≤ B.H := (pCoreIn_le_S B).trans hSleH
  set A : Subgroup ↥B.H := U.subgroupOf B.H with hAdef
  set Bs : Subgroup ↥B.H := (B.S : Subgroup G).subgroupOf B.H with hBsdef
  set Cs : Subgroup ↥B.H := V.subgroupOf B.H with hCsdef
  have hAn : A.Normal := by
    rw [hAdef]; exact oddCoreIn_normal_inSelf B.H
  haveI : A.Normal := hAn
  have hAB : A ⊔ Bs = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUleH hSleH, hHSU, Subgroup.subgroupOf_self]
  have hAbs : A ⊓ Bs = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxA, hxBs⟩ := Subgroup.mem_inf.mp hx
    rw [hAdef] at hxA
    rw [hBsdef] at hxBs
    rw [Subgroup.mem_subgroupOf] at hxA hxBs
    have hmem : (x : G) ∈ U ⊓ (B.S : Subgroup G) := ⟨hxA, hxBs⟩
    rw [inf_U_S_eq_bot B] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hACs : A ⊓ Cs = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxA, hxCs⟩ := Subgroup.mem_inf.mp hx
    rw [hAdef] at hxA
    rw [hCsdef] at hxCs
    rw [Subgroup.mem_subgroupOf] at hxA hxCs
    have hmem : (x : G) ∈ U ⊓ V := ⟨hxA, hxCs⟩
    rw [inf_eq_bot_of_odd_of_isPGroup_two (bSetup_U_odd B) (pCoreIn_isPGroup_two B)] at hmem
    exact Subtype.ext (Subgroup.mem_bot.mp hmem)
  have hcardBs : Nat.card ↥Bs = 8 := by
    rw [hBsdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSleH).toEquiv]
    have h := Subgroup.relIndex_mul_card V (B.S : Subgroup G)
    rw [inf_eq_left.mpr (pCoreIn_le_S B), hSV, hV4.1] at h
    omega
  have hcardCs : Nat.card ↥Cs = 4 := by
    rw [hCsdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVleH).toEquiv]
    exact hV4.1
  have hArelCs : A.relIndex Cs = Nat.card ↥Cs := by
    have h := Subgroup.relIndex_mul_card A Cs
    rw [hACs, Subgroup.card_bot, mul_one] at h
    exact h
  have hArelBs : A.relIndex Bs = Nat.card ↥Bs := by
    have h := Subgroup.relIndex_mul_card A Bs
    rw [hAbs, Subgroup.card_bot, mul_one] at h
    exact h
  have hkey : (A ⊔ Cs).relIndex (⊤ : Subgroup ↥B.H) = 2 := by
    have h := Subgroup.relIndex_mul_relIndex A (A ⊔ Cs) (⊤ : Subgroup ↥B.H) le_sup_left le_top
    rw [Subgroup.relIndex_sup_left (H := Cs) (K := A), hArelCs] at h
    have h2 : A.relIndex (⊤ : Subgroup ↥B.H) = Nat.card ↥Bs := by
      rw [← hAB, Subgroup.relIndex_sup_left (H := Bs) (K := A), hArelBs]
    rw [h2, hcardCs, hcardBs] at h
    omega
  have key : (A ⊔ Cs).relIndex (⊤ : Subgroup ↥B.H) = (V ⊔ U).relIndex B.H := by
    have h1 := Subgroup.relIndex_subgroupOf (H := V ⊔ U) (K := B.H) (L := B.H) le_rfl
    rw [Subgroup.subgroupOf_self, Subgroup.subgroupOf_sup hVleH hUleH] at h1
    rw [sup_comm] at h1
    exact h1
  rw [← key]
  exact hkey

/-! ## 6. The commutator -/

/-- If `V` is a four-group normalised by `Ĥ`, `t ∈ V`, `H ≠ Ĥ` and `[H : C_Ĥ(V)] = 2`, then
there is a commutator of two elements of `Ĥ` outside `C_Ĥ(V)`. -/
theorem exists_commutator_notMem_centralizer (B : Work.GW2.BenderSetup G) (V : Subgroup G)
    (hV4 : Work.GW2.IsFourGroup V) (htV : B.t ∈ V)
    (hVn : ∀ k ∈ B.Hhat, ∀ v ∈ V, k * v * k⁻¹ ∈ V)
    (hHne : B.H ≠ B.Hhat)
    (hCidx : (Subgroup.centralizer (V : Set G) ⊓ B.Hhat).relIndex B.H = 2) :
    ∃ a ∈ B.Hhat, ∃ b ∈ B.Hhat,
      a * b * a⁻¹ * b⁻¹ ∉ Subgroup.centralizer (V : Set G) ⊓ B.Hhat := by
  classical
  set C := Subgroup.centralizer (V : Set G) ⊓ B.Hhat with hCdef
  have hCleH : C ≤ B.H := by
    intro z hz
    obtain ⟨hzC, -⟩ := Subgroup.mem_inf.mp hz
    rw [show B.H = Subgroup.centralizer ({B.t} : Set G) from rfl, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_iff.mp hzC B.t htV
  have hneCH : C ≠ B.H := by
    intro heq
    have h1 : C.relIndex B.H = 1 := by rw [heq, Subgroup.relIndex_self]
    omega
  obtain ⟨h, hhH, hhC⟩ := SetLike.exists_of_lt (lt_of_le_of_ne hCleH hneCH)
  obtain ⟨u, huHhat, huH⟩ := SetLike.exists_of_lt (lt_of_le_of_ne B.H_le_Hhat hHne)
  have hhHhat : h ∈ B.Hhat := B.H_le_Hhat hhH
  have ht1 : B.t ≠ 1 := bSetup_t_ne_one B
  set s : G := u * B.t * u⁻¹ with hsdef
  have hsV : s ∈ V := hVn u huHhat B.t htV
  have hs1 : s ≠ 1 := by
    intro hh
    apply ht1
    have h2 : u⁻¹ * s * u = u⁻¹ * 1 * u := by rw [hh]
    rw [hsdef] at h2
    have h3 : u⁻¹ * (u * B.t * u⁻¹) * u = B.t := by group
    rw [h3] at h2
    simpa using h2
  have hst : s ≠ B.t := by
    intro hh
    apply huH
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h3 : u * B.t * u⁻¹ = B.t := by rw [← hsdef]; exact hh
    have h6 : u * B.t = B.t * u := by
      have h7 := congrArg (fun z => z * u) h3
      simpa [mul_assoc] using h7
    exact h6.symm
  have hstruct := fourGroup_mem_structure hV4 htV hsV ht1 hs1 hst.symm
  -- `h ∈ H = C(t)` fixes `t`
  have hcomm : B.t * h = h * B.t :=
    Subgroup.mem_centralizer_iff.mp (show h ∈ Subgroup.centralizer ({B.t} : Set G) from hhH)
      B.t (Set.mem_singleton B.t)
  have hht : h * B.t * h⁻¹ = B.t := by rw [← hcomm]; group
  have hhs_mem : h * s * h⁻¹ ∈ V := hVn h hhHhat s hsV
  have hne_hs_1 : h * s * h⁻¹ ≠ 1 := by
    intro hh
    apply hs1
    have h2 : h * s * h⁻¹ = 1 := hh
    have h3 : h⁻¹ * (h * s * h⁻¹) * h = h⁻¹ * 1 * h := by rw [h2]
    have h4 : h⁻¹ * (h * s * h⁻¹) * h = s := by group
    rw [h4] at h3
    simpa using h3
  have hne_hs_s : h * s * h⁻¹ ≠ s := by
    intro hh
    apply hhC
    refine Subgroup.mem_inf.mpr ⟨?_, hhHhat⟩
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rcases hstruct x hx with h1 | h2 | h3 | h4
    · rw [h1]; simp
    · rw [h2]; exact hcomm
    · rw [h3]
      have h4' : h * s = s * h := by
        have h5 : h * s * h⁻¹ = s := hh
        have h6 := congrArg (fun z => z * h) h5
        simpa [mul_assoc] using h6
      exact h4'.symm
    · rw [h4]
      have h5 : h * (B.t * s) * h⁻¹ = B.t * s := by
        calc h * (B.t * s) * h⁻¹ = (h * B.t * h⁻¹) * (h * s * h⁻¹) := by group
          _ = B.t * s := by rw [hht, hh]
      have h6 : h * (B.t * s) = (B.t * s) * h := by
        have h7 := congrArg (fun z => z * h) h5
        simpa [mul_assoc] using h7
      exact h6.symm
  have hhs : h * s * h⁻¹ = B.t * s := by
    have hne_hs_t : h * s * h⁻¹ ≠ B.t := by
      intro hh
      apply hst
      have h2 : h * s * h⁻¹ = B.t := hh
      calc s = h⁻¹ * (h * s * h⁻¹) * h := by group
        _ = h⁻¹ * B.t * h := by rw [h2]
        _ = h⁻¹ * (h * B.t * h⁻¹) * h := by rw [hht]
        _ = B.t := by group
    rcases hstruct (h * s * h⁻¹) hhs_mem with h1 | h2 | h3 | h4
    · exact absurd h1 hne_hs_1
    · exact absurd h2 hne_hs_t
    · exact absurd h3 hne_hs_s
    · exact h4
  have hhts : h * (B.t * s) * h⁻¹ = s := by
    calc h * (B.t * s) * h⁻¹ = (h * B.t * h⁻¹) * (h * s * h⁻¹) := by group
      _ = B.t * (B.t * s) := by rw [hht, hhs]
      _ = s := by
          rw [← mul_assoc, show B.t * B.t = 1 from by rw [← pow_two]; exact hV4.2 B.t htV,
            one_mul]
  have hhh : h * h ∈ C := by
    have h := Subgroup.pow_mem_of_relIndex_ne_zero_of_dvd (H := C) (K := B.H) (a := h) (n := 2)
      (by rw [hCidx]; norm_num) hhH
      (by rintro m hm1 hm2; rw [hCidx] at hm2; interval_cases m <;> norm_num)
    have h2 := (Subgroup.mem_inf.mp h).1
    rwa [pow_two] at h2
  have hhhc : h * h ∈ Subgroup.centralizer (V : Set G) := (Subgroup.mem_inf.mp hhh).1
  have htsV : B.t * s ∈ V := V.mul_mem htV hsV
  have hhhc_s : (h * h) * s = s * (h * h) :=
    (Subgroup.mem_centralizer_iff.mp hhhc s hsV).symm
  have hhhc_ts : (h * h) * (B.t * s) = (B.t * s) * (h * h) :=
    (Subgroup.mem_centralizer_iff.mp hhhc (B.t * s) htsV).symm
  have hcomm_ts : B.t * s = s * B.t := by
    haveI : IsMulCommutative ↥V := Work.CORE2A.IsFourGroup.isMulCommutative' hV4
    exact congrArg Subtype.val (mul_comm' (⟨B.t, htV⟩ : ↥V) (⟨s, hsV⟩ : ↥V))
  have hh_inv_s : h⁻¹ * s * h = B.t * s := by
    have hconv : s = h⁻¹ * (B.t * s) * h := by
      calc s = h⁻¹ * (h * s * h⁻¹) * h := by group
        _ = h⁻¹ * (B.t * s) * h := by rw [hhs]
    calc h⁻¹ * s * h = h⁻¹ * (h⁻¹ * (B.t * s) * h) * h := by
          nth_rewrite 1 [hconv]
          rfl
      _ = (h⁻¹ * h⁻¹) * (B.t * s) * (h * h) := by group
      _ = ((h * h)⁻¹) * (B.t * s) * (h * h) := by
            rw [show h⁻¹ * h⁻¹ = (h * h)⁻¹ from (mul_inv_rev h h).symm]
      _ = ((h * h)⁻¹) * ((B.t * s) * (h * h)) := by group
      _ = ((h * h)⁻¹) * ((h * h) * (B.t * s)) := by rw [← hhhc_ts]
      _ = B.t * s := by group
  have hh_inv_ts : h⁻¹ * (B.t * s) * h = s := by
    have hconv : B.t * s = h⁻¹ * s * h := by
      calc B.t * s = h⁻¹ * (h * (B.t * s) * h⁻¹) * h := by group
        _ = h⁻¹ * s * h := by rw [hhts]
    calc h⁻¹ * (B.t * s) * h = h⁻¹ * (h⁻¹ * s * h) * h := by rw [hconv]
      _ = (h⁻¹ * h⁻¹) * s * (h * h) := by group
      _ = ((h * h)⁻¹) * s * (h * h) := by
            rw [show h⁻¹ * h⁻¹ = (h * h)⁻¹ from (mul_inv_rev h h).symm]
      _ = ((h * h)⁻¹) * (s * (h * h)) := by group
      _ = ((h * h)⁻¹) * ((h * h) * s) := by rw [← hhhc_s]
      _ = s := by group
  -- `z = u⁻¹ t u ∈ V \ {1, t}`
  have hzV : u⁻¹ * B.t * u ∈ V := by
    simpa using hVn u⁻¹ (B.Hhat.inv_mem huHhat) B.t htV
  have hz1 : u⁻¹ * B.t * u ≠ 1 := by
    intro hh
    apply ht1
    have h2 : u * (u⁻¹ * B.t * u) * u⁻¹ = u * 1 * u⁻¹ := by rw [hh]
    have h3 : u * (u⁻¹ * B.t * u) * u⁻¹ = B.t := by group
    rw [h3] at h2
    simpa using h2
  have hzt : u⁻¹ * B.t * u ≠ B.t := by
    intro hh
    apply huH
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    have h3 : u * B.t * u⁻¹ = B.t := by
      have h4 : u * (u⁻¹ * B.t * u) * u⁻¹ = u * B.t * u⁻¹ := by rw [hh]
      have h5 : u * (u⁻¹ * B.t * u) * u⁻¹ = B.t := by group
      rw [h5] at h4
      exact h4.symm
    have h6 : u * B.t = B.t * u := by
      have h7 := congrArg (fun z => z * u) h3
      simpa [mul_assoc] using h7
    exact h6.symm
  have hzcz : u⁻¹ * B.t * u = s ∨ u⁻¹ * B.t * u = B.t * s := by
    rcases hstruct (u⁻¹ * B.t * u) hzV with h1 | h2 | h3 | h4
    · exact absurd h1 hz1
    · exact absurd h2 hzt
    · exact Or.inl h3
    · exact Or.inr h4
  -- the main computation
  have hid : h * u * h⁻¹ * u⁻¹ * B.t * (h * u * h⁻¹ * u⁻¹)⁻¹
      = h * (u * (h⁻¹ * (u⁻¹ * B.t * u) * h) * u⁻¹) * h⁻¹ := by
    rw [show (h * u * h⁻¹ * u⁻¹)⁻¹ = u * h * u⁻¹ * h⁻¹ from by group]
    group
  have hmain : h * u * h⁻¹ * u⁻¹ * B.t * (h * u * h⁻¹ * u⁻¹)⁻¹ = s := by
    rcases hzcz with hz | hz
    · have hus : u * s * u⁻¹ = B.t := by
        have h6 : u * (u⁻¹ * B.t * u) * u⁻¹ = u * s * u⁻¹ := by rw [hz]
        have h7 : u * (u⁻¹ * B.t * u) * u⁻¹ = B.t := by group
        rw [h7] at h6
        exact h6.symm
      have hval : u * (h⁻¹ * (u⁻¹ * B.t * u) * h) * u⁻¹ = B.t * s := by
        rw [hz, hh_inv_s]
        calc u * (B.t * s) * u⁻¹ = (u * B.t * u⁻¹) * (u * s * u⁻¹) := by group
          _ = s * B.t := by rw [hus, hsdef]
          _ = B.t * s := hcomm_ts.symm
      calc h * u * h⁻¹ * u⁻¹ * B.t * (h * u * h⁻¹ * u⁻¹)⁻¹
          = h * (u * (h⁻¹ * (u⁻¹ * B.t * u) * h) * u⁻¹) * h⁻¹ := hid
        _ = h * (B.t * s) * h⁻¹ := by rw [hval]
        _ = s := hhts
    · have huts : u * (B.t * s) * u⁻¹ = B.t := by
        have h6 : u * (u⁻¹ * B.t * u) * u⁻¹ = u * (B.t * s) * u⁻¹ := by rw [hz]
        have h7 : u * (u⁻¹ * B.t * u) * u⁻¹ = B.t := by group
        rw [h7] at h6
        exact h6.symm
      have hus : u * s * u⁻¹ = B.t * s := by
        calc u * s * u⁻¹ = u * (B.t * (B.t * s)) * u⁻¹ := by
              rw [show B.t * (B.t * s) = s from by
                rw [← mul_assoc, show B.t * B.t = 1 from by
                  rw [← pow_two]; exact hV4.2 B.t htV, one_mul]]
          _ = (u * B.t * u⁻¹) * (u * (B.t * s) * u⁻¹) := by group
          _ = s * B.t := by rw [huts, hsdef]
          _ = B.t * s := hcomm_ts.symm
      have hval : u * (h⁻¹ * (u⁻¹ * B.t * u) * h) * u⁻¹ = B.t * s := by
        rw [hz, hh_inv_ts]
        exact hus
      calc h * u * h⁻¹ * u⁻¹ * B.t * (h * u * h⁻¹ * u⁻¹)⁻¹
          = h * (u * (h⁻¹ * (u⁻¹ * B.t * u) * h) * u⁻¹) * h⁻¹ := hid
        _ = h * (B.t * s) * h⁻¹ := by rw [hval]
        _ = s := hhts
  refine ⟨h, hhHhat, u, huHhat, ?_⟩
  intro hmem
  have hc : h * u * h⁻¹ * u⁻¹ ∈ Subgroup.centralizer (V : Set G) := (Subgroup.mem_inf.mp hmem).1
  have ht_comm : B.t * (h * u * h⁻¹ * u⁻¹) = (h * u * h⁻¹ * u⁻¹) * B.t :=
    Subgroup.mem_centralizer_iff.mp hc B.t htV
  have hXt' : h * u * h⁻¹ * u⁻¹ * B.t * (h * u * h⁻¹ * u⁻¹)⁻¹ = B.t := by
    rw [← ht_comm]; group
  exact hst (hmain ▸ hXt')

/-! ## 7. Assembly -/

/-- Bender's Theorem 2.6, first paragraph, second case, the two numerical conclusions.

Setting: `V = O₂(Ĥ)` is a four-group with `V ⊄ S₀`, and Bender `1.6(c)`
(`Work.GW2.D16Prop`, the toolkit input `T.d16`) gives that `Ĥ/O₂(Ĥ)O(Ĥ)` has order `3` or `6`,
i.e. `(V ⊔ O(Ĥ)).relIndex Ĥ ∈ {3,6}`.

Then `V ⊔ U` (`U = O(H) = B.U`) has index `6` in `Ĥ` and `Ĥ/(V ⊔ U)` is not abelian, i.e. there
are `a, b ∈ Ĥ` with `⁅a,b⁆ ∉ V ⊔ U`. -/
theorem relIndex_sup_U_eq_six_and_commutator (T : Work.GW2.LocalToolkit)
    (h21 : Work.GW2.Lemma21Prop) :
    ∀ (G : Type) [Group G] [Finite G], Work.GW2.FeitThompsonProp → Work.GW2.BenderCtx G →
      ∀ B : Work.GW2.BenderSetup G, Work.GW2.IsFourGroup (Work.GW2.pCoreIn 2 B.Hhat) →
        ¬ Work.GW2.pCoreIn 2 B.Hhat ≤ B.S0 →
        ((Work.GW2.pCoreIn 2 B.Hhat ⊔ Work.GW2.oddCoreIn B.Hhat).relIndex B.Hhat = 3 ∨
          (Work.GW2.pCoreIn 2 B.Hhat ⊔ Work.GW2.oddCoreIn B.Hhat).relIndex B.Hhat = 6) →
        (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U).relIndex B.Hhat = 6 ∧
          ∃ a ∈ B.Hhat, ∃ b ∈ B.Hhat,
            a * b * a⁻¹ * b⁻¹ ∉ Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U := by
  intro G _ _ hFT hctx B hV4 hnotle hrel
  classical
  set V := Work.GW2.pCoreIn 2 B.Hhat with hVdef
  have htV : B.t ∈ V := t_mem_pCoreIn_of_not_le_S0 B hV4 hnotle
  have hSV : V.relIndex (B.S : Subgroup G) = 2 := relIndex_S_V_eq_two T h21 G hFT hctx B hV4 hnotle
  have hIdxH : B.H.relIndex B.Hhat = 3 := H_relIndex_Hhat_eq_three T h21 hFT hctx B hV4 hnotle hrel
  have hIdxHU : (V ⊔ B.U).relIndex B.H = 2 := sup_V_U_relIndex_H_eq_two T hFT hctx B hV4 hSV
  have hVleHhat : V ≤ B.Hhat := Subgroup.map_subtype_le _
  have hUleHhat : B.U ≤ B.Hhat := bSetup_U_le_Hhat B
  -- `[Ĥ : V ⊔ U] = 6`
  have hsix : (V ⊔ B.U).relIndex B.Hhat = 6 := by
    have hle : V ⊔ B.U ≤ B.H :=
      sup_le ((pCoreIn_le_S B).trans (bSetup_S_le_H B)) (bSetup_U_le_H B)
    have h := Subgroup.relIndex_mul_relIndex (V ⊔ B.U) B.H B.Hhat hle B.H_le_Hhat
    rw [hIdxHU, hIdxH] at h
    omega
  refine ⟨hsix, ?_⟩
  -- the centralizer `C = C_Ĥ(V)`
  set C := Subgroup.centralizer (V : Set G) ⊓ B.Hhat with hCdef
  have hVn : ∀ k ∈ B.Hhat, ∀ v ∈ V, k * v * k⁻¹ ∈ V :=
    fun k hk v hv => conj_mem_pCoreIn B hk hv
  have hVleH : V ≤ B.H := (pCoreIn_le_S B).trans (bSetup_S_le_H B)
  have hVleC : V ≤ C := by
    intro x hx
    refine Subgroup.mem_inf.mpr ⟨?_, hVleHhat hx⟩
    haveI : IsMulCommutative ↥V := Work.CORE2A.IsFourGroup.isMulCommutative' hV4
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact congrArg Subtype.val (mul_comm' (⟨y, hy⟩ : ↥V) (⟨x, hx⟩ : ↥V))
  have hUleC : B.U ≤ C := by
    have hUV : B.U ⊓ V = ⊥ :=
      inf_eq_bot_of_odd_of_isPGroup_two (bSetup_U_odd B) (pCoreIn_isPGroup_two B)
    have hUnH : (B.U.subgroupOf B.H).Normal := oddCoreIn_normal_inSelf B.H
    have hVnH : (V.subgroupOf B.H).Normal :=
      (Subgroup.normal_subgroupOf_iff hVleH).mpr
        (fun a b ha hb => conj_mem_pCoreIn B (B.H_le_Hhat hb) ha)
    have hUcent : B.U ≤ Subgroup.centralizer (V : Set G) :=
      le_centralizer_of_normal_of_inf_eq_bot (bSetup_U_le_H B) hVleH hUnH hVnH hUV
    intro x hx
    exact Subgroup.mem_inf.mpr ⟨hUcent hx, hUleHhat hx⟩
  have hCUle : V ⊔ B.U ≤ C := sup_le hVleC hUleC
  have hCleH : C ≤ B.H := by
    intro z hz
    obtain ⟨hzC, -⟩ := Subgroup.mem_inf.mp hz
    rw [show B.H = Subgroup.centralizer ({B.t} : Set G) from rfl, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    exact Subgroup.mem_centralizer_iff.mp hzC B.t htV
  -- `[H : C] = 2`
  have hCidx : C.relIndex B.H = 2 := by
    have h1 : (V ⊔ B.U).relIndex C * C.relIndex B.H = (V ⊔ B.U).relIndex B.H :=
      Subgroup.relIndex_mul_relIndex (V ⊔ B.U) C B.H hCUle hCleH
    rw [hIdxHU] at h1
    have hdvd : C.relIndex B.H ∣ 2 :=
      ⟨(V ⊔ B.U).relIndex C, by rw [mul_comm]; exact h1.symm⟩
    have hne : C.relIndex B.H ≠ 1 := by
      intro hh
      have hCH : C = B.H := le_antisymm hCleH (Subgroup.relIndex_eq_one.mp hh)
      have hcardS : Nat.card ↥(B.S : Subgroup G) = 8 := by
        have h := Subgroup.relIndex_mul_card V (B.S : Subgroup G)
        rw [inf_eq_left.mpr (pCoreIn_le_S B), hSV, hV4.1] at h
        omega
      have hcardS0 : Nat.card ↥B.S0 = 4 := by
        have h := bSetup_card_S_eq B
        omega
      have hr : ∃ r ∈ B.S0, r ^ 2 ≠ 1 := by
        obtain ⟨g, hg⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top B.S0).mp B.S0_cyclic
        have hordg : orderOf g = 4 := by
          rw [← Nat.card_zpowers g, hg]
          exact hcardS0
        refine ⟨g, hg ▸ Subgroup.mem_zpowers g, ?_⟩
        intro hg2
        have hdiv : orderOf g ∣ 2 :=
          orderOf_dvd_iff_pow_eq_one.mpr hg2
        have hle : orderOf g ≤ 2 := Nat.le_of_dvd (by norm_num) hdiv
        omega
      obtain ⟨r, hrS0, hr2⟩ := hr
      obtain ⟨s₀, hs₀V, hs₀S0⟩ : ∃ x ∈ V, x ∉ B.S0 := by
        by_contra hcon
        push Not at hcon
        exact hnotle hcon
      have hrH : r ∈ B.H := le_trans B.S0_le (bSetup_S_le_H B) hrS0
      have hrC : r ∈ C := hCH ▸ hrH
      have hrcomm : s₀ * r = r * s₀ :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hrC).1 s₀ hs₀V
      have hrsS : r * s₀ ∈ (B.S : Subgroup G) :=
        (B.S).mul_mem (B.S0_le hrS0) ((pCoreIn_le_S B) hs₀V)
      have hrsS0 : r * s₀ ∉ B.S0 := by
        intro hc
        apply hs₀S0
        have hmem : r⁻¹ * (r * s₀) ∈ B.S0 := B.S0.mul_mem (B.S0.inv_mem hrS0) hc
        simpa using hmem
      obtain ⟨n, hn2, hdih⟩ := exists_dihedral_S' hctx B
      have hrs2 : (r * s₀) ^ 2 = 1 := by
        have ho := dihedral_index_two n hn2 (B.S : Subgroup G) B.S0 hdih B.S0_le B.S0_cyclic
          B.S0_index (r * s₀) hrsS hrsS0
        simpa [ho] using pow_orderOf_eq_one (r * s₀)
      have hs₀2 : s₀ ^ 2 = 1 := hV4.2 s₀ hs₀V
      have hrs2' : (r * s₀) * (r * s₀) = 1 := by
        have h := hrs2
        rwa [pow_two] at h
      have hr2eq : r * r = 1 := by
        calc r * r = r * r * (s₀ * s₀) := by
              rw [show s₀ * s₀ = 1 from by rw [← pow_two]; exact hs₀2, mul_one]
          _ = r * s₀ * (r * s₀) := by
              calc r * r * (s₀ * s₀) = r * (r * s₀) * s₀ := by group
                _ = r * (s₀ * r) * s₀ := by rw [← hrcomm]
                _ = r * s₀ * (r * s₀) := by group
          _ = 1 := hrs2'
      have : r ^ 2 = 1 := by rwa [pow_two]
      exact hr2 this
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h2 | h2
    · exact absurd h2 hne
    · exact h2
  -- the commutator
  have hHne : B.H ≠ B.Hhat := by
    intro heq
    have h1 : B.H.relIndex B.Hhat = 1 := by rw [heq, Subgroup.relIndex_self]
    omega
  obtain ⟨a, ha, b, hb, hab⟩ :=
    exists_commutator_notMem_centralizer B V hV4 htV hVn hHne hCidx
  refine ⟨a, ha, b, hb, ?_⟩
  have hCVU : C = V ⊔ B.U := by
    have hle : V ⊔ B.U ≤ C := hCUle
    have h2 : (V ⊔ B.U).relIndex C * C.relIndex B.H = (V ⊔ B.U).relIndex B.H :=
      Subgroup.relIndex_mul_relIndex (V ⊔ B.U) C B.H hle hCleH
    rw [hIdxHU, hCidx] at h2
    have h1 : (V ⊔ B.U).relIndex C = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hle
  rw [← hCVU]
  exact hab

end Work.CORE2A
