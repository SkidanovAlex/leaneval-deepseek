import Mathlib
import Submission.Work.CORE4.NotA7Defs
import Submission.Work.CORE4.A7UMCard
import Submission.Work.CORE4.A7Split
import Submission.Work.CORE4.API
import Submission.Work.CORE4.A7Normalize

namespace Work.CORE4.NotA7

open Work.GW2 Subgroup

set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

variable {G : Type} [Group G] [Finite G]

/-! ## Pure group theory: an involution acting on a group of prime-power order

The two elementary facts used below.  They are stated for an abstract finite group and measured
only by a divisibility, because that is all the assembly needs.

* An involution `y` normalising a four-group `V` has a subgroup of fixed points of even order.
* An involution `y` normalising a subgroup `A` of order `9`, which does **not** normalise a given
  subgroup `F ≤ A` of order `3`, has a fixed-point subgroup on `A` of order divisible by `3`. -/

/-- A subgroup of exponent `2` is commutative. -/
theorem A6_isMulCommutative_of_sq_eq_one (V : Subgroup G) (h : ∀ v ∈ V, v ^ 2 = 1) :
    IsMulCommutative ↥V := by
  rw [← Subgroup.le_centralizer_iff_isMulCommutative]
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro w hw
  have hv2 : v * v = 1 := by simpa [pow_two] using h v hv
  have hw2 : w * w = 1 := by simpa [pow_two] using h w hw
  have hvw : (v * w) * (v * w) = 1 := by simpa [pow_two] using h (v * w) (V.mul_mem hv hw)
  have h1 : (v * w)⁻¹ = v * w := inv_eq_of_mul_eq_one_right hvw
  have h2 : (v * w)⁻¹ = w * v := by
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hw2, inv_eq_of_mul_eq_one_right hv2]
  rw [h2] at h1
  exact h1

/-- An involution normalising a four-group has a nontrivial fixed point, whence the fixed-point
subgroup has even order. -/
theorem A6_fourGroup_involution_dvd_two (V : Subgroup G) (y : G) (hV : Work.GW2.IsFourGroup V)
    (hy2 : orderOf y = 2) (hyV : y ∈ Subgroup.normalizer (V : Set G)) :
    2 ∣ Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) := by
  classical
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := by
    intro a ha b hb
    have hmem : a ∈ Subgroup.centralizer (V : Set G) :=
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        (A6_isMulCommutative_of_sq_eq_one V hV.2)) ha
    exact (Subgroup.mem_centralizer_iff.mp hmem b hb).symm
  have hVne : V ≠ ⊥ := by
    intro h
    have := hV.1
    rw [h] at this
    simp at this
  obtain ⟨v, hv, hv1⟩ : ∃ v : G, v ∈ V ∧ v ≠ 1 := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hVne
    exact ⟨(a : G), a.2, fun hcon => ha (Subtype.ext hcon)⟩
  have hvyV : y * v * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyV v).mp hv
  have hkey : ∃ w ∈ V, w ≠ 1 ∧ y * w * y⁻¹ = w := by
    by_cases hfix : y * v * y⁻¹ = v
    · exact ⟨v, hv, hv1, hfix⟩
    · refine ⟨v * (y * v * y⁻¹), V.mul_mem hv hvyV, ?_, ?_⟩
      · intro hw
        have h2 : (y * v * y⁻¹) * (y * v * y⁻¹) = 1 := by
          simpa [pow_two] using hV.2 (y * v * y⁻¹) hvyV
        have hinv : (y * v * y⁻¹)⁻¹ = y * v * y⁻¹ := inv_eq_of_mul_eq_one_right h2
        have hw' : (y * v * y⁻¹) * v = 1 := by
          rw [hcomm (y * v * y⁻¹) hvyV v hv, hw]
        have hv_eq : v = (y * v * y⁻¹)⁻¹ := eq_inv_of_mul_eq_one_right hw'
        exact hfix (hv_eq.trans hinv).symm
      · have hcomp : y * (y * v * y⁻¹) * y⁻¹ = v := by
          have h1 : y⁻¹ * y⁻¹ = 1 := by rw [← mul_inv_rev, hyy, inv_one]
          calc y * (y * v * y⁻¹) * y⁻¹ = (y * y) * v * (y⁻¹ * y⁻¹) := by group
            _ = 1 * v * 1 := by rw [hyy, h1]
            _ = v := by simp
        calc y * (v * (y * v * y⁻¹)) * y⁻¹
            = (y * v * y⁻¹) * (y * (y * v * y⁻¹) * y⁻¹) := by group
          _ = (y * v * y⁻¹) * v := by rw [hcomp]
          _ = v * (y * v * y⁻¹) := hcomm (y * v * y⁻¹) hvyV v hv
  obtain ⟨w, hwV, hw1, hwfix⟩ := hkey
  have hyw : y * w = w * y := by
    have hywy : y * w * y = w := by simpa [hyinv] using hwfix
    calc y * w = y * w * (y * y) := by rw [hyy, mul_one]
      _ = (y * w * y) * y := by group
      _ = w * y := by rw [hywy]
  have hwC : w ∈ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    exact hyw
  have hne : V ⊓ Subgroup.centralizer ({y} : Set G) ≠ ⊥ := by
    intro hbot
    have : (w : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact Subgroup.mem_inf.mpr ⟨hwV, hwC⟩
    exact hw1 (Subgroup.mem_bot.mp this)
  have hlt : 1 < Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) :=
    Subgroup.one_lt_card_iff_ne_bot _ |>.mpr hne
  have hdvd : Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) ∣ 2 ^ 2 := by
    rw [show (2 : ℕ) ^ 2 = 4 by norm_num, ← hV.1]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, _hk, hk2⟩ := (Nat.dvd_prime_pow (p := 2) (by norm_num) (m := 2)
    (i := Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)))).mp hdvd
  have hk0 : k ≠ 0 := by rintro rfl; rw [hk2] at hlt; simp at hlt
  rw [hk2]
  exact dvd_pow_self 2 hk0

/-- An involution `y` normalising a subgroup `A` of order `9` has a fixed-point subgroup on `A`
of order divisible by `3`, as soon as it moves some subgroup `F ≤ A` of order `3`. -/
theorem A6_three_dvd_centralizer_card (hc15 : Work.GW2.Coprime15Prop)
    (hft : Work.GW2.FeitThompsonProp) (A F : Subgroup G) (y : G)
    (hA9 : Nat.card A = 9) (hF3 : Nat.card F = 3) (hFle : F ≤ A)
    (hy2 : orderOf y = 2) (hyA : y ∈ Subgroup.normalizer (A : Set G))
    (hyF : y ∉ Subgroup.normalizer (F : Set G)) :
    3 ∣ Nat.card ↥(A ⊓ Subgroup.centralizer ({y} : Set G)) := by
  classical
  have hyy : y * y = 1 := by
    have h := pow_orderOf_eq_one y
    rwa [hy2, pow_two] at h
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hAodd : Odd (Nat.card A) := by rw [hA9]; norm_num
  obtain ⟨-, hprod, -⟩ := hc15 G hft A y hy2 hAodd hyA
  -- some `f ∈ F` is moved off `F` by `y`
  have hyna : ∃ a ∈ F, y * a * y⁻¹ ∉ F := by
    by_contra hcon
    push_neg at hcon
    apply hyF
    rw [Subgroup.mem_normalizer_iff]
    intro a
    constructor
    · exact hcon a
    · intro ha
      have hback : y⁻¹ * (y * a * y⁻¹) * y⁻¹ ∈ F := by
        simpa [hyinv] using hcon (y * a * y⁻¹) ha
      have heq : y⁻¹ * (y * a * y⁻¹) * y⁻¹ = a := by
        rw [hyinv]
        calc y * (y * a * y) * y = (y * y) * a * (y * y) := by group
          _ = 1 * a * 1 := by rw [hyy]
          _ = a := by simp
      rwa [heq] at hback
  obtain ⟨f, hfF, hfnot⟩ := hyna
  have hfA : f ∈ A := hFle hfF
  have hnotmem : f ∉ Work.GW2.invSet A y := by
    intro hmem
    apply hfnot
    rw [hmem.2]
    exact F.inv_mem hfF
  have hcardA : (A : Set G).ncard = 9 := by
    rw [← Nat.card_coe_set_eq (A : Set G)]
    exact hA9
  have hneq9 : (Work.GW2.invSet A y).ncard ≠ 9 := by
    intro hm9
    have hsub : (Work.GW2.invSet A y : Set G) ⊆ (A : Set G) := fun x hx => hx.1
    have heq : (Work.GW2.invSet A y : Set G) = (A : Set G) :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hcardA, hm9])
    exact hnotmem (heq ▸ hfA)
  have hc_dvd : Nat.card ↥(A ⊓ Subgroup.centralizer ({y} : Set G)) ∣ 9 := by
    rw [← hA9]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hcne : Nat.card ↥(A ⊓ Subgroup.centralizer ({y} : Set G)) ≠ 1 := by
    intro hc1
    apply hneq9
    have h1 : (Work.GW2.invSet A y).ncard * 1 = 9 := by
      rw [← hc1, hprod, hA9]
    simpa using h1
  have hc_dvd' : Nat.card ↥(A ⊓ Subgroup.centralizer ({y} : Set G)) ∣ 3 ^ 2 := by
    rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact hc_dvd
  obtain ⟨k, _hk, hk2⟩ := (Nat.dvd_prime_pow (p := 3) (by norm_num) (m := 2)
    (i := Nat.card ↥(A ⊓ Subgroup.centralizer ({y} : Set G)))).mp hc_dvd'
  have hk0 : k ≠ 0 := by rintro rfl; exact hcne (by rw [hk2]; norm_num)
  rw [hk2]
  exact dvd_pow_self 3 hk0

/-! ## The `A := F ⊔ K ⊴ H` computation -/

/-- `A := F ⊔ K = U ⊓ M` is normalised by `H = U ⊔ S`. -/
theorem A6_FK_normal_H (I : Work.GW2.C4Inputs) (B : Work.GW2.BenderSetup G)
    (C : Work.GW2.Case2Ctx6 B) (hHyp : Work.GW2.Hyp9 G B C) (h2 : Work.GW2.A7Facts2 B C.D)
    (hpre : Work.GW2.Case2Pre B C.D) (hB0F : C.D.B0 = C.D.F) (h5 : Work.GW2.A7Facts5 B C.D) :
    B.H ≤ Subgroup.normalizer (((C.D.F ⊔ C.D.K : Subgroup G)) : Set G) := by
  obtain ⟨hbc, _hcase2, _hplus, _hseven, _height⟩ := hHyp
  have hUM : B.U ⊓ C.D.M = C.D.F ⊔ C.D.K := by
    rw [Work.GW2.Case2Pre.U_eq B C.D hpre, hB0F, sup_comm]
  have hHsplit : B.H = B.U ⊔ (B.S : Subgroup G) := Work.CORE4.A7Split I hbc h2
  have hSleM : (B.S : Subgroup G) ≤ C.D.M := le_trans h2.2.2.1 (Work.CORE4.layerIn_le C.D.M)
  have hAnormU : ((C.D.F ⊔ C.D.K).subgroupOf B.U).Normal := h5.2.2
  have hAleU : (C.D.F ⊔ C.D.K) ≤ B.U := hUM ▸ inf_le_left
  have hUleN : B.U ≤ Subgroup.normalizer (((C.D.F ⊔ C.D.K : Subgroup G)) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAleU).mp hAnormU
  have hSleN : (B.S : Subgroup G) ≤
      Subgroup.normalizer (((C.D.F ⊔ C.D.K : Subgroup G)) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs a ha
    have hsH : s ∈ B.H := B.S_le_H hs
    have haUM : a ∈ B.U ⊓ C.D.M := by rw [hUM]; exact ha
    obtain ⟨haU, haM⟩ := Subgroup.mem_inf.mp haUM
    have hsU : s * a * s⁻¹ ∈ B.U :=
      (Subgroup.normal_subgroupOf_iff B.U_le_H).mp B.U_normal a s haU hsH
    have hsM : s * a * s⁻¹ ∈ C.D.M :=
      C.D.M.mul_mem (C.D.M.mul_mem (hSleM hs) haM) (C.D.M.inv_mem (hSleM hs))
    rw [← hUM]
    exact Subgroup.mem_inf.mpr ⟨hsU, hsM⟩
  rw [hHsplit]
  exact sup_le hUleN hSleN

/-- **A6, even case, centralizer bound.**

With `A := F ⊔ K = U ⊓ M` (order `9`) and `V := O₂(H ⊓ M)` (a four-group), both `A` and `V` lie
in `N := M ⊓ M^y` (they are `y`-invariant, and `A`/`V` are inside `M`).  Since `y ∉ N_G(F) = M`,
the involution `y` moves the order-`3` subgroup `F` of `A`; hence `3 ∣ |C_A(y)|`
(`A6_three_dvd_centralizer_card`, via `y ∈ N_G(A)` from `A6_FK_normal_H`).  And `y` normalises the
four-group `V`, so `2 ∣ |C_V(y)|` (`A6_fourGroup_involution_dvd_two`).  As `C_A(y)` and `C_V(y)`
are subgroups of `N ⊓ C_G(y)`, Lagrange gives `6 ∣ |N ⊓ C_G(y)|`. -/
theorem A6EvenCentralizer (I : Work.GW2.C4Inputs) :
    ∀ (G : Type) [Group G] [Finite G] (B : Work.GW2.BenderSetup G) (C : Work.GW2.Case2Ctx6 B)
      (y : G),
      Work.GW2.Hyp9 G B C → Work.GW2.IsA7Case C.D → Work.GW2.A7Facts1 C.D →
        Work.GW2.A7Facts2 B C.D → Work.CORE4.A7Mid B C.D →
          orderOf y = 2 → y ∈ B.H → y ∉ C.D.M →
            6 ≤ Nat.card ↥((C.D.M ⊓ Work.GW2.conjSub y C.D.M) ⊓
              Subgroup.centralizer ({y} : Set G)) := by
  intro G _ _ B C y hHyp _hA7 hf1 hf2 hMid hy2 hyH hyM
  classical
  obtain ⟨hKcard, hFcard, _hK0eq, _hpiFU⟩ := hf1
  obtain ⟨hUData, _hNotInv, hFacts5⟩ := hMid
  obtain ⟨_hU3, hB0F, _hoddCoreF, _hXbound⟩ := hUData
  set A : Subgroup G := C.D.F ⊔ C.D.K with hAdef
  set V : Subgroup G := Work.GW2.pCoreIn 2 (B.H ⊓ C.D.M) with hVdef
  set N : Subgroup G := C.D.M ⊓ Work.GW2.conjSub y C.D.M with hNdef
  -- `A = U ⊓ M`, so `A ≤ U` and `A ≤ M`
  have hUM : B.U ⊓ C.D.M = A := by
    rw [hAdef, Work.GW2.Case2Pre.U_eq B C.D C.pre, hB0F, sup_comm]
  have hAleM : A ≤ C.D.M := hUM ▸ inf_le_right
  have hFleA : C.D.F ≤ A := by rw [hAdef]; exact le_sup_left
  have hA9 : Nat.card A = 9 := by
    rw [hAdef]; exact Work.CORE4.A7UMCard (B := B) (C := C) hB0F hKcard hFcard
  -- `y` normalises `A` but not `F`
  have hynormA : y ∈ Subgroup.normalizer (A : Set G) := by
    rw [hAdef]; exact A6_FK_normal_H I B C hHyp hf2 C.pre hB0F hFacts5 hyH
  have hynotF : y ∉ Subgroup.normalizer (C.D.F : Set G) := by
    rw [Work.GW2.Case2Pre.N_F B C.D C.pre]; exact hyM
  have h3 : 3 ∣ Nat.card ↥(A ⊓ Subgroup.centralizer ({y} : Set G)) :=
    A6_three_dvd_centralizer_card I.toolkit.c15 I.toolkit.ft A C.D.F y hA9 hFcard hFleA hy2
      hynormA hynotF
  -- `V` is a four-group, normalised by `y` and lying in `M`
  have hVH : B.H ≤ Subgroup.normalizer (V : Set G) := by
    rw [hVdef, hHyp.2.2.2.1.1]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer
      (Work.CORE4.pCoreIn_le_self 2 B.H)).mp (Work.CORE4.subgroupOf_pCoreIn_normal 2 B.H)
  have hynormV : y ∈ Subgroup.normalizer (V : Set G) := hVH hyH
  have hVleM : V ≤ C.D.M := by
    rw [hVdef]
    exact le_trans (Work.CORE4.pCoreIn_le_self 2 (B.H ⊓ C.D.M)) inf_le_right
  have h2 : 2 ∣ Nat.card ↥(V ⊓ Subgroup.centralizer ({y} : Set G)) :=
    A6_fourGroup_involution_dvd_two V y (by rw [hVdef]; exact hf2.1) hy2 hynormV
  -- `A ≤ N` and `V ≤ N`
  have hAleN : A ≤ N := by
    rw [hNdef]
    refine le_inf hAleM ?_
    intro a ha
    rw [Work.CORE4.mem_conjSub_iff']
    refine ⟨y⁻¹ * a * y, ?_, by group⟩
    have hyinv : y⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normalizer (A : Set G)).inv_mem hynormA
    have hmem := (Subgroup.mem_normalizer_iff.mp hyinv a).mp ha
    exact hAleM (by rwa [inv_inv] at hmem)
  have hVleN : V ≤ N := by
    rw [hNdef]
    refine le_inf hVleM ?_
    intro v hv
    rw [Work.CORE4.mem_conjSub_iff']
    refine ⟨y⁻¹ * v * y, ?_, by group⟩
    have hyinv : y⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      (Subgroup.normalizer (V : Set G)).inv_mem hynormV
    have hmem := (Subgroup.mem_normalizer_iff.mp hyinv v).mp hv
    exact hVleM (by rwa [inv_inv] at hmem)
  -- assemble
  have hle3 : (A ⊓ Subgroup.centralizer ({y} : Set G)) ≤
      (N ⊓ Subgroup.centralizer ({y} : Set G)) :=
    le_inf (le_trans inf_le_left hAleN) inf_le_right
  have hle2 : (V ⊓ Subgroup.centralizer ({y} : Set G)) ≤
      (N ⊓ Subgroup.centralizer ({y} : Set G)) :=
    le_inf (le_trans inf_le_left hVleN) inf_le_right
  have h3N : 3 ∣ Nat.card ↥(N ⊓ Subgroup.centralizer ({y} : Set G)) :=
    dvd_trans h3 (Subgroup.card_dvd_of_le hle3)
  have h2N : 2 ∣ Nat.card ↥(N ⊓ Subgroup.centralizer ({y} : Set G)) :=
    dvd_trans h2 (Subgroup.card_dvd_of_le hle2)
  have h6 : 6 ∣ Nat.card ↥(N ⊓ Subgroup.centralizer ({y} : Set G)) :=
    Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 2 3) h2N h3N
  exact Nat.le_of_dvd Nat.card_pos h6

end Work.CORE4.NotA7
