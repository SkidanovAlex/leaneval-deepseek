import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.CosetInvCountBasic
import Submission.Work.CORE3.RelIndexHHhat
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.CosetInvCountNeFive
import Submission.Work.CORE3.SixInvSetElements
import Submission.Work.CORE3.NormalizerPcoreEqHhat
import Submission.Work.CORE3.NcardOrderOfEqThreeLeTwo

namespace Work.CORE3

open Work.GW2

/-! ## Bender 1981 §3, step (6): a coset with at least five involutions

Given Bender's (5) — no involution `z ∉ Ĥ` inverts a non-trivial element of `VU = O₂(Ĥ)·O(Ĥ)` —
and an involution `y ∉ Ĥ` whose coset `yĤ` carries at least five involutions, we produce an
involution `z ∈ Ĥy` inverting an odd-order subgroup `X ≤ Ĥ` whose centralizer and normalizer in
`G` both have even order.

The counting lemmas `CosetInvCountLeSix` and `CosetInvCountNeFive` force `cosetInvCount Ĥ y = 6`.
`Work.CORE3.SixInvSetElements` then provides an element `a ∈ I_Ĥ(y)` of order `3` and two
distinct involutions `b₁, b₂ ∈ I_Ĥ(y)`.  The key point is that `b₁` normalizes `⟨a⟩`: its
conjugate `b₁ a b₁⁻¹` again lies in `I_Ĥ(y)` and has order `3`, while `I_Ĥ(y)` has at most two
elements of order `3` (the order-`3` elements of `I_Ĥ(y)` inject, via the coset map to `Ĥ/VU`,
into the order-`3` elements of the group `Ĥ/VU` of order `6`, of which there are at most `2`).
Hence `b₁ a b₁⁻¹ = a` or `= a⁻¹`; in the first case `b₁` centralizes `a`, in the second `y·b₁`
is an involution centralizing `a`. -/

/-- A group of order `6` has at most two elements of order `3` (this is
`Work.CORE3.NcardOrderOfEqThreeLeTwo`, imported above). -/

theorem BenderSix (G : Type) [Group G] [Finite G] (I : Work.CORE3.Case1Inputs) (h : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B) (D : Work.GW2.Case1bData B)
    (h5 : ∀ z : G, orderOf z = 2 → z ∉ B.Hhat →
      Work.GW2.invSet (Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U) z = {1})
    {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (hbig : 5 ≤ Work.GW2.cosetInvCount B.Hhat y) :
    ∃ z : G, orderOf z = 2 ∧ (∃ h ∈ B.Hhat, z = h * y) ∧
      ∃ X : Subgroup G, X ≤ B.Hhat ∧ X ≠ ⊥ ∧ Odd (Nat.card ↥X) ∧ Work.GW2.Inverts z X ∧
        Even (Nat.card (Subgroup.centralizer (X : Set G))) ∧
        Even (Nat.card (Subgroup.normalizer (X : Set G))) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hy : y * y = 1 := ((Work.CORE3.orderOf_eq_two_iff_mul_self y).mp hy2).1
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy
  -- ## The coset contains exactly six involutions.
  have hn6 : Work.GW2.cosetInvCount B.Hhat y = 6 := by
    have hle := Work.CORE3.cosetInvCount_le_six G I h B h1 D h5 y hy2 hyH
    have hne := Work.CORE3.CosetInvCountNeFive G I h B h1 D h5 y hy2 hyH
    omega
  -- ## The structure of `I_Ĥ(y)`.
  obtain ⟨a, b1, b2, haI, ha3, hb1I, hb1o, hb2I, hb2o, hb12⟩ :=
    Work.CORE3.SixInvSetElements G I h B h1 D h5 y hy2 hyH hn6
  have hb1sq : b1 * b1 = 1 := ((Work.CORE3.orderOf_eq_two_iff_mul_self b1).mp hb1o).1
  have hb1ne : b1 ≠ 1 := ((Work.CORE3.orderOf_eq_two_iff_mul_self b1).mp hb1o).2
  have hb1inv : b1⁻¹ = b1 := inv_eq_of_mul_eq_one_right hb1sq
  have hb1y : y * b1 * y = b1 := by rw [hb1I.2, hb1inv]
  have hane : a ≠ 1 := by
    intro hc
    rw [hc, orderOf_one] at ha3
    exact absurd ha3 (by norm_num)
  -- ## `VU = O₂(Ĥ) ⊔ O(Ĥ)` and its quotient.
  have h26 : Work.GW2.Thm26Concl B := I.h26 G I.T.ft h B
  let W : Subgroup G := Work.GW2.pCoreIn 2 B.Hhat ⊔ B.U
  let N : Subgroup ↥B.Hhat := W.subgroupOf B.Hhat
  have hWle : W ≤ B.Hhat :=
    sup_le (Work.CORE2A.thm26Concl_O2_le_Hhat h26) (Work.CORE2A.thm26Concl_U_le_Hhat h26)
  have hWn : N.Normal := Work.CORE3.normal_VU_subgroupOf G I h B h1 D
  haveI : N.Normal := hWn
  have hcard6 : Nat.card (↥B.Hhat ⧸ N) = 6 := by
    rw [← Subgroup.index_eq_card N]
    exact Work.CORE3.relIndex_VU_Hhat G I h B h1 D
  have h5' : ∀ z : G, z * z = 1 → z ∉ B.Hhat → Work.GW2.invSet W z = {1} := by
    intro z hz hzH
    have hz1 : z ≠ 1 := by rintro rfl; exact hzH B.Hhat.one_mem
    exact h5 z ((Work.CORE3.orderOf_eq_two_iff_mul_self z).mpr ⟨hz, hz1⟩) hzH
  -- An element of `W` lying in `I_Ĥ(y)` is trivial.
  have hkill1 : ∀ z : G, z ∈ W → z ∈ Work.CORE3.invSetIn B.Hhat y → z = 1 := by
    intro z hzW hzI
    have hmem : z ∈ Work.GW2.invSet W y := by
      refine ⟨hzW, ?_⟩
      rw [hyinv]
      exact hzI.2
    rw [h5' y hy hyH] at hmem
    exact Set.mem_singleton_iff.mp hmem
  -- ## `I_Ĥ(y)` has at most two elements of order `3`.
  have hT3 : ({x : G | x ∈ Work.CORE3.invSetIn B.Hhat y ∧ orderOf x = 3} : Set G).ncard ≤ 2 := by
    let mkq : {x : G // x ∈ Work.CORE3.invSetIn B.Hhat y} → (↥B.Hhat ⧸ N) :=
      fun p => (QuotientGroup.mk (⟨p.1, Work.CORE3.invSetIn_subset B.Hhat y p.2⟩ : ↥B.Hhat) :
        ↥B.Hhat ⧸ N)
    set Ssub : Set {x : G // x ∈ Work.CORE3.invSetIn B.Hhat y} :=
      {p | orderOf (p : G) = 3} with hSsubdef
    have hcard_eq : Ssub.ncard =
        ({x : G | x ∈ Work.CORE3.invSetIn B.Hhat y ∧ orderOf x = 3} : Set G).ncard := by
      refine Set.ncard_congr (fun p _ => (p : G)) ?_ ?_ ?_
      · intro p hp; exact ⟨p.2, hp⟩
      · intro p q _ _ hpq; exact Subtype.ext hpq
      · intro b hb; exact ⟨⟨b, hb.1⟩, hb.2, rfl⟩
    rw [← hcard_eq]
    refine le_trans (Set.ncard_le_ncard_of_injOn mkq ?_ ?_)
      (Work.CORE3.NcardOrderOfEqThreeLeTwo hcard6)
    · intro p hp
      have hxord : orderOf (⟨p.1, Work.CORE3.invSetIn_subset B.Hhat y p.2⟩ : ↥B.Hhat) = 3 := by
        rw [Subgroup.orderOf_mk]
        exact hp
      have hdvd : orderOf (mkq p) ∣ 3 := by
        rw [← hxord]
        exact orderOf_map_dvd (QuotientGroup.mk' N) _
      have hne : orderOf (mkq p) ≠ 1 := by
        intro h1
        have hx1 : QuotientGroup.mk' N (⟨p.1, Work.CORE3.invSetIn_subset B.Hhat y p.2⟩ : ↥B.Hhat)
            = 1 := orderOf_eq_one_iff.mp h1
        have hmemN : (⟨p.1, Work.CORE3.invSetIn_subset B.Hhat y p.2⟩ : ↥B.Hhat) ∈ N := by
          rw [← QuotientGroup.ker_mk' (N := N)]
          exact MonoidHom.mem_ker.mpr hx1
        have hmemW : (p.1 : G) ∈ W := Subgroup.mem_subgroupOf.mp hmemN
        have hp1 : (p.1 : G) = 1 := hkill1 p.1 hmemW p.2
        have hpord : orderOf (p.1 : G) = 3 := hp
        rw [hp1, orderOf_one] at hpord
        exact absurd hpord (by norm_num)
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact absurd h1 hne
      · exact h3
    · intro p hp q hq hpq
      apply Subtype.ext
      have hmem : ((⟨p.1, Work.CORE3.invSetIn_subset B.Hhat y p.2⟩ : ↥B.Hhat)⁻¹ *
          (⟨q.1, Work.CORE3.invSetIn_subset B.Hhat y q.2⟩ : ↥B.Hhat) : ↥B.Hhat) ∈ N := by
        rw [← QuotientGroup.eq]
        exact hpq
      have hmem' : (p.1 : G)⁻¹ * (q.1 : G) ∈ W := by
        have hh := Subgroup.mem_subgroupOf.mp hmem
        simpa using hh
      have hconj : (q.1 : G) * (p.1 : G)⁻¹ ∈ W := by
        have hnorm := (Subgroup.normal_subgroupOf_iff hWle).mp hWn
        have hh := hnorm ((p.1 : G)⁻¹ * (q.1 : G)) (p.1 : G) hmem'
          (Work.CORE3.invSetIn_subset B.Hhat y p.2)
        simpa [mul_assoc] using hh
      exact (Work.CORE3.invSetIn_eq_of_mul_inv_mem hWle h5' hy hyH q.2 p.2 hconj).symm
  -- ## `b₁` normalises `⟨a⟩`.
  have hconj : b1 * a * b1⁻¹ = a ∨ b1 * a * b1⁻¹ = a⁻¹ := by
    have ha'ord : orderOf (b1 * a * b1⁻¹) = 3 := by
      rw [show b1 * a * b1⁻¹ = (MulAut.conj b1) a from by rw [MulAut.conj_apply],
        MulEquiv.orderOf_eq, ha3]
    have ha'mem : b1 * a * b1⁻¹ ∈ Work.CORE3.invSetIn B.Hhat y := by
      rw [hb1inv]
      exact Work.CORE3.mul_mem_invSetIn_conj hy hb1I haI
    have haT3 : a ∈ ({x : G | x ∈ Work.CORE3.invSetIn B.Hhat y ∧ orderOf x = 3} : Set G) :=
      ⟨haI, ha3⟩
    have hainvT3 : a⁻¹ ∈ ({x : G | x ∈ Work.CORE3.invSetIn B.Hhat y ∧ orderOf x = 3} : Set G) :=
      ⟨Work.CORE3.inv_mem_invSetIn hy haI, by rw [orderOf_inv, ha3]⟩
    have hsubset : ({a, a⁻¹} : Set G) ⊆
        ({x : G | x ∈ Work.CORE3.invSetIn B.Hhat y ∧ orderOf x = 3} : Set G) := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact haT3
      · exact hainvT3
    have hane2 : a ≠ a⁻¹ := by
      intro hc
      have h2 : a * a = 1 := (mul_eq_one_iff_eq_inv (a := a) (b := a)).mpr hc
      have hdvd : orderOf a ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact h2)
      rw [ha3] at hdvd
      norm_num at hdvd
    have hpair : ({a, a⁻¹} : Set G).ncard = 2 := by
      rw [Set.ncard_insert_of_notMem (by simpa using hane2), Set.ncard_singleton]
    have heq : ({a, a⁻¹} : Set G) =
        ({x : G | x ∈ Work.CORE3.invSetIn B.Hhat y ∧ orderOf x = 3} : Set G) :=
      Set.eq_of_subset_of_ncard_le hsubset (by rw [hpair]; exact hT3)
    have hmemb : b1 * a * b1⁻¹ ∈ ({a, a⁻¹} : Set G) := by
      rw [heq]
      exact ⟨ha'mem, ha'ord⟩
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hmemb
  -- ## Produce an involution `w` centralising `⟨a⟩`.
  have hmain : ∃ w : G, w * w = 1 ∧ w ≠ 1 ∧
      w ∈ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
    have key : ∀ w : G, w * w = 1 → w * a = a * w →
        w ∈ Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
      intro w hw2 hcw
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      exact ((show Commute w a from hcw).zpow_right k).eq.symm
    rcases hconj with hcc | hcinv
    · have hcw : b1 * a = a * b1 := by
        have hh := congrArg (fun t => t * b1) hcc
        simpa [mul_assoc] using hh
      exact ⟨b1, hb1sq, hb1ne, key b1 hb1sq hcw⟩
    · have hwa : (y * b1) * a * (y * b1)⁻¹ = a := by
        have e1 : (y * b1) * a * (y * b1)⁻¹ = y * (b1 * a * b1) * y := by
          rw [mul_inv_rev, hb1inv, hyinv]
          group
        have e2 : b1 * a * b1 = a⁻¹ := by rw [← hcinv, hb1inv]
        have e3 : y * a⁻¹ * y = a := by
          rw [show a⁻¹ = y * a * y from haI.2.symm]
          rw [show y * (y * a * y) * y = (y * y) * a * (y * y) from by group, hy,
            one_mul, mul_one]
        rw [e1, e2, e3]
      have hw2 : (y * b1) * (y * b1) = 1 := by
        rw [show (y * b1) * (y * b1) = (y * b1 * y) * b1 from by group, hb1y, hb1sq]
      have hwne : y * b1 ≠ 1 := by
        intro hc
        have h1 : y = b1⁻¹ := (mul_eq_one_iff_eq_inv).mp hc
        rw [hb1inv] at h1
        exact hyH (by rw [h1]; exact hb1I.1)
      have hcw : (y * b1) * a = a * (y * b1) := by
        have hh := congrArg (fun t => t * (y * b1)) hwa
        simpa [mul_assoc] using hh
      exact ⟨y * b1, hw2, hwne, key (y * b1) hw2 hcw⟩
  obtain ⟨w, hw2, hwne, hwC⟩ := hmain
  have hword : orderOf w = 2 := by
    refine orderOf_eq_prime (p := 2) ?_ hwne
    rw [pow_two]; exact hw2
  -- ## The subgroup `X = ⟨a⟩` and the involution `y` doing the job.
  have hXle : Subgroup.zpowers a ≤ B.Hhat := Subgroup.zpowers_le.mpr haI.1
  have hXne : Subgroup.zpowers a ≠ ⊥ := by
    intro hbot
    have : a ∈ (⊥ : Subgroup G) := by rw [← hbot]; exact Subgroup.mem_zpowers a
    exact hane (Subgroup.mem_bot.mp this)
  have hXodd : Odd (Nat.card ↥(Subgroup.zpowers a)) := by
    rw [Nat.card_zpowers, ha3]
    norm_num
  have hinvY : Work.GW2.Inverts y (Subgroup.zpowers a) := by
    intro u hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    show y * a ^ k * y⁻¹ = (a ^ k)⁻¹
    rw [show y * a ^ k * y⁻¹ = (MulAut.conj y) (a ^ k) from by rw [MulAut.conj_apply],
      map_zpow, MulAut.conj_apply, hyinv, haI.2, inv_zpow]
  have hEvenC : Even (Nat.card (Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G))) := by
    rw [even_iff_two_dvd]
    have hle : Subgroup.zpowers w ≤
        Subgroup.centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr hwC
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers, hword] at hdvd
    exact hdvd
  have hEvenN : Even (Nat.card (Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G))) := by
    rw [even_iff_two_dvd]
    have hyN : y ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) := by
      have hconj1 : ∀ k : ℤ, y * a ^ k * y⁻¹ = a ^ (-k) := by
        intro k
        rw [show y * a ^ k * y⁻¹ = (MulAut.conj y) (a ^ k) from by rw [MulAut.conj_apply],
          map_zpow, MulAut.conj_apply, hyinv, haI.2, inv_zpow, zpow_neg]
      rw [Subgroup.mem_normalizer_iff]
      intro u
      constructor
      · intro hu
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        rw [hconj1 k]
        exact Subgroup.zpow_mem_zpowers a (-k)
      · intro hu
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hu
        have h1 : u = y⁻¹ * a ^ k * y := by
          rw [hk]
          group
        rw [h1]
        have h2 : y⁻¹ * a ^ k * y = a ^ (-k) := by
          rw [show y⁻¹ * a ^ k * y = (MulAut.conj y⁻¹) (a ^ k) from by
                rw [MulAut.conj_apply, inv_inv],
            map_zpow, MulAut.conj_apply, inv_inv, hyinv, haI.2, inv_zpow, zpow_neg]
        rw [h2]
        exact Subgroup.zpow_mem_zpowers a (-k)
    have hle : Subgroup.zpowers y ≤
        Subgroup.normalizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
      Subgroup.zpowers_le.mpr hyN
    have hdvd := Subgroup.card_dvd_of_le hle
    rw [Nat.card_zpowers, hy2] at hdvd
    exact hdvd
  exact ⟨y, hy2, ⟨1, B.Hhat.one_mem, by rw [one_mul]⟩, Subgroup.zpowers a, hXle, hXne, hXodd,
    hinvY, hEvenC, hEvenN⟩

end Work.CORE3
