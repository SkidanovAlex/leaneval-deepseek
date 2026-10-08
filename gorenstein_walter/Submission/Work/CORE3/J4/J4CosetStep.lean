import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.J4.VUInvSetTrivial
import Submission.Work.CORE3.Case1bEightNineDefs
import Submission.Work.CORE3.CosetInvCountLeSix
import Submission.Work.CORE3.J4.CardDvdSixOfDisjoint
import Submission.Work.CORE2A.isFourGroup_closure_pair

namespace Work.CORE3.J4

open Work.GW2

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary helpers -/

/-- `H = ⊥` from `∀ x ∈ H, x = 1`. -/
theorem eq_bot_of_forall {H : Subgroup G} (h : ∀ x ∈ H, x = 1) : H = ⊥ :=
  le_antisymm (fun x hx => by rw [Subgroup.mem_bot]; exact h x hx) bot_le

/-- An element of order two is its own inverse. -/
theorem inv_eq_self_of_orderOf_two {u : G} (h : orderOf u = 2) : u⁻¹ = u :=
  inv_eq_of_mul_eq_one_right ((orderOf_eq_two_iff_mul_self u).mp h).1

/-- For an element of order three, `(x⁻¹)² = x`. -/
theorem inv_sq_of_orderOf_three {x : G} (hx3 : orderOf x = 3) : (x⁻¹) ^ 2 = x := by
  have h3 : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
  have hxinv : x⁻¹ = x ^ 2 := inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h3)
  rw [hxinv, pow_two, ← pow_add, show (2 : ℕ) + 2 = 3 + 1 by norm_num, pow_add, h3, one_mul,
    pow_one]

/-- If `a ∈ I_Ĥ(y)` then so is every integer power of `a`. -/
theorem zpow_mem_invSetIn {Hh : Subgroup G} {y x : G} (hy : y * y = 1)
    (hx : x ∈ Work.CORE3.invSetIn Hh y) (n : ℤ) : x ^ n ∈ Work.CORE3.invSetIn Hh y := by
  rcases n with n | n
  · rw [Int.ofNat_eq_coe, zpow_natCast]
    exact Work.CORE3.pow_mem_invSetIn hy hx n
  · rw [zpow_negSucc]
    exact Work.CORE3.inv_mem_invSetIn hy (Work.CORE3.pow_mem_invSetIn hy hx (n + 1))

/-- If `z * g * z⁻¹ = g⁻¹` then `z` inverts the cyclic subgroup `⟨g⟩`. -/
theorem inverts_zpowers_of {z g : G} (h : z * g * z⁻¹ = g⁻¹) :
    Work.GW2.Inverts z (Subgroup.zpowers g) := by
  intro u hu
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  have h1 : z * g ^ n * z⁻¹ = (z * g * z⁻¹) ^ n := by
    rw [← MulAut.conj_apply z (g ^ n), map_zpow, MulAut.conj_apply]
  rw [h1, h, inv_zpow]

/-- An involution `w ≠ 1` centralizing `X` makes `|C_G(X)|` even. -/
theorem even_card_centralizer_of_involution {X : Subgroup G} {w : G} (hw : w * w = 1)
    (hw1 : w ≠ 1) (hwc : w ∈ Subgroup.centralizer (X : Set G)) :
    Even (Nat.card ↥(Subgroup.centralizer (X : Set G))) := by
  rw [even_iff_two_dvd]
  have hle : Subgroup.zpowers w ≤ Subgroup.centralizer (X : Set G) :=
    Subgroup.zpowers_le.mpr hwc
  have hdvd := Subgroup.card_dvd_of_le hle
  rwa [Nat.card_zpowers, (orderOf_eq_two_iff_mul_self w).mpr ⟨hw, hw1⟩] at hdvd

/-- An involution `z ≠ 1` inverting `X` makes `|N_G(X)|` even. -/
theorem even_card_normalizer_of_inverts {X : Subgroup G} {z : G} (hz : z * z = 1) (hz1 : z ≠ 1)
    (hinv : Work.GW2.Inverts z X) :
    Even (Nat.card ↥(Subgroup.normalizer (X : Set G))) := by
  rw [even_iff_two_dvd]
  have hzN : z ∈ Subgroup.normalizer (X : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      rw [hinv h hh]
      exact X.inv_mem hh
    · intro hh
      have hw : z * h * z⁻¹ ∈ X := hh
      have heq : h = z * (z * h * z⁻¹) * z⁻¹ := by
        rw [show z * (z * h * z⁻¹) * z⁻¹ = (z * z) * h * (z⁻¹ * z⁻¹) by group]
        rw [hz, one_mul, show z⁻¹ * z⁻¹ = 1 by rw [← mul_inv_rev, hz, inv_one], mul_one]
      rw [heq, hinv (z * h * z⁻¹) hw]
      exact X.inv_mem hw
  have hle : Subgroup.zpowers z ≤ Subgroup.normalizer (X : Set G) :=
    Subgroup.zpowers_le.mpr hzN
  have hdvd := Subgroup.card_dvd_of_le hle
  rwa [Nat.card_zpowers, (orderOf_eq_two_iff_mul_self z).mpr ⟨hz, hz1⟩] at hdvd

/-- `VU = O₂(Ĥ)·O(Ĥ)` is contained in `Ĥ`. -/
theorem VU_le_Hhat (I : Work.CORE3.Case1Inputs) (hBc : Work.GW2.BenderCtx G)
    (B : Work.GW2.BenderSetup G) : ((pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G)) ≤ B.Hhat :=
  sup_le (Work.CORE2A.thm26Concl_O2_le_Hhat (I.h26 G I.T.ft hBc B))
    (Work.CORE2A.thm26Concl_U_le_Hhat (I.h26 G I.T.ft hBc B))

/-- If `a` and `b` are distinct involutions of `I_Ĥ(y) = {1, a, b, c}` which do not commute,
then `a * b` has order three: `a b a = b a b = c`. -/
theorem orderOf_mul_eq_three_of_not_commute {Hh : Subgroup G} {c y a b : G} (hy : y * y = 1)
    (hIeq : Work.CORE3.invSetIn Hh y = ({1, a, b, c} : Set G))
    (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (ha2 : orderOf a = 2) (hb2 : orderOf b = 2) (hcomm : a * b ≠ b * a) :
    orderOf (a * b) = 3 := by
  have ha2' : a * a = 1 := ((orderOf_eq_two_iff_mul_self a).mp ha2).1
  have hb2' : b * b = 1 := ((orderOf_eq_two_iff_mul_self b).mp hb2).1
  have ha_ne1 : a ≠ 1 := ((orderOf_eq_two_iff_mul_self a).mp ha2).2
  have hb_ne1 : b ≠ 1 := ((orderOf_eq_two_iff_mul_self b).mp hb2).2
  have haI : a ∈ Work.CORE3.invSetIn Hh y := by rw [hIeq]; simp
  have hbI : b ∈ Work.CORE3.invSetIn Hh y := by rw [hIeq]; simp
  have haba : a * b * a ∈ Work.CORE3.invSetIn Hh y :=
    Work.CORE3.mul_mem_invSetIn_conj hy haI hbI
  have hbab : b * a * b ∈ Work.CORE3.invSetIn Hh y :=
    Work.CORE3.mul_mem_invSetIn_conj hy hbI haI
  have haba_ne1 : a * b * a ≠ 1 := by
    intro hh
    have h3 : a * b * a * a = 1 * a := congrArg (fun z => z * a) hh
    rw [show a * b * a * a = a * b by rw [mul_assoc, ha2', mul_one], one_mul] at h3
    exact hb_ne1 (mul_left_cancel (by rw [mul_one]; exact h3))
  have hbab_ne1 : b * a * b ≠ 1 := by
    intro hh
    have h3 : b * a * b * b = 1 * b := congrArg (fun z => z * b) hh
    rw [show b * a * b * b = b * a by rw [mul_assoc, hb2', mul_one], one_mul] at h3
    exact ha_ne1 (mul_left_cancel (by rw [mul_one]; exact h3))
  have haba_ne_a : a * b * a ≠ a := by
    intro hh
    have h3 : a * b * a * a = a * a := congrArg (fun z => z * a) hh
    rw [show a * b * a * a = a * b by rw [mul_assoc, ha2', mul_one], ha2'] at h3
    exact hab ((mul_eq_one_iff_eq_inv.mp h3).trans (inv_eq_self_of_orderOf_two hb2))
  have hbab_ne_b : b * a * b ≠ b := by
    intro hh
    have h3 : b * a * b * b = b * b := congrArg (fun z => z * b) hh
    rw [show b * a * b * b = b * a by rw [mul_assoc, hb2', mul_one], hb2'] at h3
    exact hab ((mul_eq_one_iff_eq_inv.mp h3).trans (inv_eq_self_of_orderOf_two ha2)).symm
  have haba_ne_b : a * b * a ≠ b := by
    intro hh
    exact hcomm (by
      have h3 : a * (a * b * a) = a * b := congrArg (fun z => a * z) hh
      have h3' : a * (a * b * a) = b * a := by
        rw [← mul_assoc a (a * b) a, ← mul_assoc a a b, ha2', one_mul]
      rw [h3'] at h3
      exact h3.symm)
  have hbab_ne_a : b * a * b ≠ a := by
    intro hh
    exact hcomm (by
      have h3 : b * (b * a * b) = b * a := congrArg (fun z => b * z) hh
      have h3' : b * (b * a * b) = a * b := by
        rw [← mul_assoc b (b * a) b, ← mul_assoc b b a, hb2', one_mul]
      rw [h3'] at h3
      exact h3)
  have haba_eq : a * b * a = c := by
    rw [hIeq] at haba
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at haba
    rcases haba with hh | hh | hh | hh
    · exact absurd hh haba_ne1
    · exact absurd hh haba_ne_a
    · exact absurd hh haba_ne_b
    · exact hh
  have hbab_eq : b * a * b = c := by
    rw [hIeq] at hbab
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hbab
    rcases hbab with hh | hh | hh | hh
    · exact absurd hh hbab_ne1
    · exact absurd hh hbab_ne_a
    · exact absurd hh hbab_ne_b
    · exact hh
  have hc2 : c * c = 1 := by
    rw [← haba_eq]
    rw [show (a * b * a) * (a * b * a) = a * b * (a * a) * b * a by group, ha2', mul_one,
      show a * b * b * a = a * (b * b) * a by group, hb2', mul_one, ha2']
  have h3 : (a * b) ^ 3 = 1 := by
    have hexp : (a * b) ^ 3 = (a * b * a) * (b * a * b) := by
      rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ, pow_two]
      group
    rw [hexp, haba_eq, hbab_eq, hc2]
  have hne1 : a * b ≠ 1 := by
    intro hh
    have h5 : a = b⁻¹ := (mul_eq_one_iff_eq_inv).mp hh
    rw [inv_eq_self_of_orderOf_two hb2] at h5
    exact hab h5
  have hdvd : orderOf (a * b) ∣ 3 := (orderOf_dvd_iff_pow_eq_one).mpr h3
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hne1
  · exact h

end Work.CORE3.J4

namespace Work.CORE3.J4

open Work.GW2

/-- Bender 1981 §3, step (6) (first half): if the coset `Ĥy` of an involution `y ∉ Ĥ` contains
exactly four involutions then some involution `z = h * y` of the coset inverts an odd-order
subgroup `X ≤ Ĥ` whose centralizer and normalizer have even order, and `X` is inverted by an
involution `s ∈ Ĥ` as well (Bender's `N_Ĥ(X)` hypothesis in step (7); the extra conjunct is what
`Work.CORE3.D23.J4U3V18s` needs). -/
theorem J4CosetStep {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (hy4 : Work.GW2.cosetInvCount B.Hhat y = 4) :
    ∃ z : G, orderOf z = 2 ∧ (∃ h ∈ B.Hhat, z = h * y) ∧
      ∃ X : Subgroup G, X ≤ B.Hhat ∧ X ≠ ⊥ ∧ Odd (Nat.card X) ∧ Work.GW2.Inverts z X ∧
        Even (Nat.card (Subgroup.centralizer (X : Set G))) ∧
        Even (Nat.card (Subgroup.normalizer (X : Set G))) ∧
        (∃ s ∈ B.Hhat, orderOf s = 2 ∧ Work.GW2.Inverts s X) := by
  classical
  have hy : y * y = 1 := ((orderOf_eq_two_iff_mul_self y).mp hy2).1
  have hyne : y ≠ 1 := ((orderOf_eq_two_iff_mul_self y).mp hy2).2
  have hVUinv : invSet (pCoreIn 2 B.Hhat ⊔ B.U) y = {1} :=
    VUInvSetTrivial I hBc B h1 D y hy2 hyH
  have hIcard : (Work.CORE3.invSetIn B.Hhat y).ncard = 4 := by
    rw [Work.CORE3.ncard_invSetIn_eq_cosetInvCount B.Hhat y hy hyH]
    exact hy4
  -- `I ∩ VU = {1}`
  have hmemVU : ∀ z : G, z ∈ Work.CORE3.invSetIn B.Hhat y →
      z ∈ (pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G) → z = 1 := by
    intro z hzI hzVU
    have h1' : z ∈ invSet B.Hhat y := by
      rw [← Work.CORE3.invSetIn_eq_invSet hy]
      exact hzI
    have h2 : z ∈ invSet (pCoreIn 2 B.Hhat ⊔ B.U) y := ⟨hzVU, h1'.2⟩
    rw [hVUinv] at h2
    exact h2
  -- every element of `I` has order at most four
  have hord_le : ∀ x : G, x ∈ Work.CORE3.invSetIn B.Hhat y → orderOf x ≤ 4 := by
    intro x hx
    have hsub : (Subgroup.zpowers x : Set G) ⊆ Work.CORE3.invSetIn B.Hhat y := by
      intro z hz
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact zpow_mem_invSetIn hy hx n
    have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
    rw [hIcard] at hle
    have h2 : (Subgroup.zpowers x : Set G).ncard = orderOf x := by
      rw [← Nat.card_zpowers]
      exact (Nat.card_coe_set_eq _).symm
    rwa [h2] at hle
  by_cases h3 : ∃ x : G, x ∈ Work.CORE3.invSetIn B.Hhat y ∧ orderOf x = 3
  · -- ## Case 1: `I` contains an element of order three
    obtain ⟨x, hxI, hx3⟩ := h3
    have hxin : y * x * y = x⁻¹ := hxI.2
    have hyx : y * x * y⁻¹ = x⁻¹ := by
      rw [inv_eq_self_of_orderOf_two hy2]; exact hxin
    have hx3' : x ^ 3 = 1 := by rw [← hx3]; exact pow_orderOf_eq_one x
    have hx_ne1 : x ≠ 1 := fun hh => by rw [hh, orderOf_one] at hx3; norm_num at hx3
    have hx2I : x ^ 2 ∈ Work.CORE3.invSetIn B.Hhat y :=
      Work.CORE3.pow_mem_invSetIn hy hxI 2
    have hx_ne_x2 : x ≠ x ^ 2 := by
      intro hh
      have h2 : x ^ 2 * x⁻¹ = x * x⁻¹ := congrArg (fun z => z * x⁻¹) hh.symm
      rw [mul_inv_cancel,
        show x ^ 2 * x⁻¹ = x by rw [pow_two, mul_assoc, mul_inv_cancel, mul_one]] at h2
      exact hx_ne1 h2
    have hx2_ne1 : x ^ 2 ≠ 1 := by
      intro hh
      have hdvd : orderOf x ∣ 2 := (orderOf_dvd_iff_pow_eq_one).mpr hh
      rw [hx3] at hdvd
      norm_num at hdvd
    have h1x : (1 : G) ≠ x := hx_ne1.symm
    have h1x2 : (1 : G) ≠ x ^ 2 := hx2_ne1.symm
    have h3card : ({1, x, x ^ 2} : Set G).ncard = 3 :=
      Set.ncard_eq_three.mpr ⟨1, x, x ^ 2, h1x, h1x2, hx_ne_x2, rfl⟩
    have hsub3 : ({1, x, x ^ 2} : Set G) ⊆ Work.CORE3.invSetIn B.Hhat y := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl
      · exact Work.CORE3.one_mem_invSetIn hy
      · exact hxI
      · exact hx2I
    have hnotsub : ¬ ((Work.CORE3.invSetIn B.Hhat y) ⊆ ({1, x, x ^ 2} : Set G)) := by
      intro hss
      have hle := Set.ncard_le_ncard hss (Set.toFinite _)
      rw [hIcard, h3card] at hle
      omega
    obtain ⟨d, hdI, hdnot3⟩ := Set.not_subset.mp hnotsub
    have hd_ne1 : d ≠ 1 := fun hh => hdnot3 (by rw [hh]; exact Set.mem_insert_iff.mpr (Or.inl rfl))
    have hd_nex : d ≠ x := fun hh => hdnot3 (by rw [hh]; simp)
    have hd_nex2 : d ≠ x ^ 2 := fun hh => hdnot3 (by rw [hh]; simp)
    have h1d : (1 : G) ≠ d := hd_ne1.symm
    have hxd : x ≠ d := hd_nex.symm
    have hx2d : x ^ 2 ≠ d := hd_nex2.symm
    have h4card : ({1, x, x ^ 2, d} : Set G).ncard = 4 :=
      Set.ncard_eq_four.mpr ⟨1, x, x ^ 2, d, h1x, h1x2, h1d, hx_ne_x2, hxd, hx2d, rfl⟩
    have hsub4 : ({1, x, x ^ 2, d} : Set G) ⊆ Work.CORE3.invSetIn B.Hhat y := by
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl | rfl | rfl
      · exact Work.CORE3.one_mem_invSetIn hy
      · exact hxI
      · exact hx2I
      · exact hdI
    have hIeq : Work.CORE3.invSetIn B.Hhat y = ({1, x, x ^ 2, d} : Set G) := by
      refine (Set.eq_of_subset_of_ncard_le hsub4 ?_ (Set.toFinite _)).symm
      rw [hIcard, h4card]
    -- `d` is an involution
    have hord_d : orderOf d = 2 := by
      have hle := hord_le d hdI
      have h0 := orderOf_pos d
      have hne1 : orderOf d ≠ 1 := fun hh => hd_ne1 (orderOf_eq_one_iff.mp hh)
      have hne3 : orderOf d ≠ 3 := by
        intro hh
        have hd3 : d ^ 3 = 1 := by rw [← hh]; exact pow_orderOf_eq_one d
        have hd2I : d ^ 2 ∈ Work.CORE3.invSetIn B.Hhat y :=
          Work.CORE3.pow_mem_invSetIn hy hdI 2
        rw [hIeq] at hd2I
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd2I
        have hd2ne1 : d ^ 2 ≠ 1 := by
          intro h2
          have hdvd : orderOf d ∣ 2 := (orderOf_dvd_iff_pow_eq_one).mpr h2
          rw [hh] at hdvd
          norm_num at hdvd
        have hd2ne_d : d ^ 2 ≠ d := by
          intro h2
          have h3 : d ^ 2 * d⁻¹ = d * d⁻¹ := congrArg (fun z => z * d⁻¹) h2
          rw [mul_inv_cancel, show d ^ 2 * d⁻¹ = d by rw [pow_two, mul_assoc, mul_inv_cancel,
            mul_one]] at h3
          exact hd_ne1 h3
        have hd4 : d ^ 4 = (d ^ 2) ^ 2 := by rw [← pow_mul]
        have hd4' : d ^ 4 = d := by
          rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hd3, one_mul, pow_one]
        rcases hd2I with hh' | hh' | hh' | hh'
        · exact hd2ne1 hh'
        · exact hd_nex2 (by rw [← hd4', hd4, hh'])
        · have h4' : (x ^ 2) ^ 2 = x := by
            rw [← pow_mul, show (2 : ℕ) * 2 = 4 by norm_num,
              show (4 : ℕ) = 3 + 1 by norm_num, pow_add, hx3', one_mul, pow_one]
          exact hd_nex (by rw [← hd4', hd4, hh']; exact h4')
        · exact hd2ne_d hh'
      have hne4 : orderOf d ≠ 4 := by
        intro hh
        have hd2I : d ^ 2 ∈ Work.CORE3.invSetIn B.Hhat y :=
          Work.CORE3.pow_mem_invSetIn hy hdI 2
        rw [hIeq] at hd2I
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd2I
        have hd2ord : orderOf (d ^ 2) = 2 := by
          have hd4eq1 : d ^ 4 = 1 := by rw [← hh]; exact pow_orderOf_eq_one d
          refine (orderOf_eq_two_iff_mul_self (d ^ 2)).mpr ⟨?_, ?_⟩
          · rw [← pow_add]; norm_num; exact hd4eq1
          · intro hcon
            have hdvd : orderOf d ∣ 2 := (orderOf_dvd_iff_pow_eq_one).mpr hcon
            rw [hh] at hdvd
            norm_num at hdvd
        have hx2ord : orderOf (x ^ 2) = 3 := by rw [orderOf_pow, hx3]; norm_num
        rcases hd2I with hh' | hh' | hh' | hh'
        · rw [hh'] at hd2ord; norm_num at hd2ord
        · rw [hh', hx3] at hd2ord; norm_num at hd2ord
        · rw [hh', hx2ord] at hd2ord; norm_num at hd2ord
        · rw [hh', hh] at hd2ord; norm_num at hd2ord
      rcases Nat.lt_or_ge (orderOf d) 2 with h2 | h2
      · exact absurd (le_antisymm (Nat.lt_succ_iff.mp h2) h0) hne1
      · rcases Nat.lt_or_ge (orderOf d) 3 with h3 | h3
        · exact le_antisymm (Nat.lt_succ_iff.mp h3) h2
        · rcases Nat.lt_or_ge (orderOf d) 4 with h4 | h4
          · exact absurd (le_antisymm (Nat.lt_succ_iff.mp h4) h3) hne3
          · exact absurd (le_antisymm hle h4) hne4
    have hd_sq : d * d = 1 := ((orderOf_eq_two_iff_mul_self d).mp hord_d).1
    have hd_inv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hd_sq
    -- conjugation by `d` inverts `x`
    have hdxd : d * x * d = x ^ 2 := by
      have hmem := Work.CORE3.mul_mem_invSetIn_conj hy hdI hxI
      have hord : orderOf (d * x * d) = 3 := by
        have hc : d * x * d = (MulAut.conj d) x := by rw [MulAut.conj_apply, hd_inv]
        rw [hc, MulEquiv.orderOf_eq, hx3]
      rw [hIeq] at hmem
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
      rcases hmem with hh | hh | hh | hh
      · rw [hh] at hord; norm_num at hord
      · exact absurd hh (by
          intro hcon
          have hcd : d * x = x * d := by
            have h1 : d * (d * x * d) = d * x := congrArg (fun z => d * z) hcon
            rw [show d * (d * x * d) = (d * d) * x * d by group, hd_sq, one_mul] at h1
            exact h1.symm
          have hmem2 : d * x ∈ Work.CORE3.invSetIn B.Hhat y :=
            Work.CORE3.mul_mem_invSetIn hy hdI hxI hcd
          have hc2 : Commute d x := hcd
          have h6 : orderOf (d * x) = 6 := by
            have hcop : (orderOf d).Coprime (orderOf x) := by rw [hord_d, hx3]; norm_num
            rw [Commute.orderOf_mul_eq_mul_orderOf_of_coprime hc2 hcop, hord_d, hx3]
          have := hord_le (d * x) hmem2
          omega)
      · exact hh
      · rw [hh, hord_d] at hord; norm_num at hord
    have hydy : y * d * y = d := by
      have h := hdI.2
      rw [hd_inv] at h
      exact h
    have hyd : y * d = d * y := by
      have h := congrArg (fun z => z * y) hydy
      rwa [mul_assoc, hy, mul_one] at h
    -- `w = y * d` is an involution centralizing `x`
    have hw_sq : (y * d) * (y * d) = 1 := by
      rw [show (y * d) * (y * d) = (y * d * y) * d by group, hydy, hd_sq]
    have hw_ne1 : y * d ≠ 1 := by
      intro hh
      have h2 : y = d⁻¹ := (mul_eq_one_iff_eq_inv).mp hh
      rw [hd_inv] at h2
      exact hyH (by rw [h2]; exact hdI.1)
    have hwx : (y * d) * x * (y * d) = x := by
      have h1 : y * x ^ 2 * y = x := by
        rw [Work.CORE3.conj_pow_of_inv hy hxin 2, inv_sq_of_orderOf_three hx3]
      have hA : (y * d) * x * (y * d) = y * d * x * (d * y) := by rw [hyd]
      rw [hA, show y * d * x * (d * y) = y * (d * x * d) * y by group, hdxd, h1]
    have hwcomm : Commute (y * d) x := by
      have h1 := congrArg (fun z => z * (y * d)) hwx
      rwa [show (y * d) * x * (y * d) * (y * d) = (y * d) * x * ((y * d) * (y * d)) by group,
        hw_sq, mul_one] at h1
    have hwC : y * d ∈ Subgroup.centralizer ((Subgroup.zpowers x) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
      exact (hwcomm.zpow_right n).eq.symm
    have hx2inv : x ^ 2 = x⁻¹ :=
      mul_eq_one_iff_eq_inv.mp (by rw [← pow_succ]; norm_num; exact hx3')
    have hdxd' : d * x * d⁻¹ = x⁻¹ := by
      rw [hd_inv, hdxd, hx2inv]
    refine ⟨y, hy2, ⟨1, B.Hhat.one_mem, by rw [one_mul]⟩, Subgroup.zpowers x,
      Subgroup.zpowers_le.mpr hxI.1, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun hbot => hx_ne1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers x))
    · rw [Nat.card_zpowers, hx3]; norm_num
    · exact inverts_zpowers_of hyx
    · exact even_card_centralizer_of_involution hw_sq hw_ne1 hwC
    · exact even_card_normalizer_of_inverts hy hyne (inverts_zpowers_of hyx)
    · exact ⟨d, hdI.1, hord_d, inverts_zpowers_of hdxd'⟩
  · -- ## Case 2: every nonidentity element of `I` is an involution
    push_neg at h3
    have hno4 : ∀ x : G, x ∈ Work.CORE3.invSetIn B.Hhat y → orderOf x ≠ 4 := by
      intro x hxI hx4
      have hYcard : Nat.card ↥(Subgroup.zpowers x) = 4 := by
        rw [Nat.card_zpowers, hx4]
      have hYle : Subgroup.zpowers x ≤ B.Hhat := Subgroup.zpowers_le.mpr hxI.1
      have hdisj : Subgroup.zpowers x ⊓ (pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G) = ⊥ := by
        refine eq_bot_of_forall ?_
        intro z hz
        rw [Subgroup.mem_inf] at hz
        obtain ⟨hzY, hzVU⟩ := hz
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hzY
        exact hmemVU (x ^ n) (zpow_mem_invSetIn hy hxI n) hzVU
      have hdvd := CardDvdSixOfDisjoint I hBc B h1 D (Subgroup.zpowers x) hYle hdisj
      rw [hYcard] at hdvd
      norm_num at hdvd
    have hle2 : ∀ x : G, x ∈ Work.CORE3.invSetIn B.Hhat y → orderOf x ≤ 2 := by
      intro x hxI
      have h1 := hord_le x hxI
      have h2 := h3 x hxI
      have h4 := hno4 x hxI
      by_contra hcon
      rcases Nat.lt_or_ge (orderOf x) 4 with h | h
      · exact h2 (le_antisymm (Nat.lt_succ_iff.mp h) (Nat.lt_of_not_le hcon))
      · exact h4 (le_antisymm h1 h)
    have hone : (1 : G) ∈ Work.CORE3.invSetIn B.Hhat y := Work.CORE3.one_mem_invSetIn hy
    have hsdiff : (Work.CORE3.invSetIn B.Hhat y \ {1}).ncard = 3 := by
      rw [Set.ncard_sdiff_singleton_of_mem hone, hIcard]
    obtain ⟨a, b, c, hab, hac, hbc, hset⟩ := Set.ncard_eq_three.mp hsdiff
    have hamem : a ∈ Work.CORE3.invSetIn B.Hhat y \ {1} := by rw [hset]; simp
    have hbmem : b ∈ Work.CORE3.invSetIn B.Hhat y \ {1} := by rw [hset]; simp
    have hcmem : c ∈ Work.CORE3.invSetIn B.Hhat y \ {1} := by rw [hset]; simp
    have haI : a ∈ Work.CORE3.invSetIn B.Hhat y := hamem.1
    have hbI : b ∈ Work.CORE3.invSetIn B.Hhat y := hbmem.1
    have hcI : c ∈ Work.CORE3.invSetIn B.Hhat y := hcmem.1
    have ha_ne1 : a ≠ 1 := fun hh => hamem.2 (by rw [hh]; exact Set.mem_singleton 1)
    have hb_ne1 : b ≠ 1 := fun hh => hbmem.2 (by rw [hh]; exact Set.mem_singleton 1)
    have ha2 : orderOf a = 2 := by
      have h1 := hle2 a haI
      have h2 : orderOf a ≠ 1 := fun hh => ha_ne1 (orderOf_eq_one_iff.mp hh)
      rcases Nat.lt_or_ge (orderOf a) 2 with h | h
      · exact absurd (le_antisymm (Nat.lt_succ_iff.mp h) (orderOf_pos a)) h2
      · exact le_antisymm h1 h
    have hb2 : orderOf b = 2 := by
      have h1 := hle2 b hbI
      have h2 : orderOf b ≠ 1 := fun hh => hb_ne1 (orderOf_eq_one_iff.mp hh)
      rcases Nat.lt_or_ge (orderOf b) 2 with h | h
      · exact absurd (le_antisymm (Nat.lt_succ_iff.mp h) (orderOf_pos b)) h2
      · exact le_antisymm h1 h
    have ha2' : a * a = 1 := ((orderOf_eq_two_iff_mul_self a).mp ha2).1
    have hb2' : b * b = 1 := ((orderOf_eq_two_iff_mul_self b).mp hb2).1
    have ha2'' : a ^ 2 = 1 := by rw [pow_two]; exact ha2'
    have hb2'' : b ^ 2 = 1 := by rw [pow_two]; exact hb2'
    have hIeq : Work.CORE3.invSetIn B.Hhat y = ({1, a, b, c} : Set G) := by
      ext z
      constructor
      · intro hz
        by_cases hz1 : z = 1
        · rw [hz1]
          exact Set.mem_insert_iff.mpr (Or.inl rfl)
        · have hz' : z ∈ Work.CORE3.invSetIn B.Hhat y \ {1} := ⟨hz, by simpa using hz1⟩
          rw [hset] at hz'
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz' ⊢
          tauto
      · intro hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl | rfl | rfl
        · exact hone
        · exact haI
        · exact hbI
        · exact hcI
    by_cases hcomm : a * b = b * a
    · -- `a` and `b` commute: `⟨a,b⟩` is a four-group meeting `VU` trivially
      have hfour := Work.CORE2A.isFourGroup_closure_pair ha2'' hb2'' hcomm ha_ne1 hb_ne1 hab
      have hYcard : Nat.card ↥(Subgroup.closure ({a, b} : Set G)) = 4 := hfour.1
      have hYle : Subgroup.closure ({a, b} : Set G) ≤ B.Hhat := by
        rw [Subgroup.closure_le]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact haI.1
        · exact hbI.1
      have habI : a * b ∈ Work.CORE3.invSetIn B.Hhat y :=
        Work.CORE3.mul_mem_invSetIn hy haI hbI hcomm
      have hab_ne1 : a * b ≠ 1 := by
        intro hh
        exact hab ((mul_eq_one_iff_eq_inv.mp hh).trans (inv_eq_self_of_orderOf_two hb2))
      have hab_ne2 : a ≠ a * b := by
        intro hh
        have h := mul_left_cancel (show a * 1 = a * b by rw [mul_one, ← hh])
        exact hb_ne1 h.symm
      have hab_ne3 : b ≠ a * b := by
        intro hh
        have h1 : a * b * b = b * b := congrArg (fun z => z * b) hh.symm
        rw [mul_assoc, hb2', mul_one] at h1
        exact ha_ne1 h1
      have h4c : ({1, a, b, a * b} : Set G).ncard = 4 :=
        Set.ncard_eq_four.mpr ⟨1, a, b, a * b, ha_ne1.symm, hb_ne1.symm, hab_ne1.symm, hab,
          hab_ne2, hab_ne3, rfl⟩
      have ha_mem : a ∈ ({a, b} : Set G) := Set.mem_insert_iff.mpr (Or.inl rfl)
      have hb_mem : b ∈ ({a, b} : Set G) :=
        Set.mem_insert_iff.mpr (Or.inr (Set.mem_singleton_iff.mpr rfl))
      have hcl_eq : ((Subgroup.closure ({a, b} : Set G)) : Set G) = ({1, a, b, a * b} : Set G) := by
        have hsub : ({1, a, b, a * b} : Set G) ⊆ ((Subgroup.closure ({a, b} : Set G)) : Set G) := by
          intro u hu
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
          rcases hu with rfl | rfl | rfl | rfl
          · exact Subgroup.one_mem _
          · exact Subgroup.subset_closure ha_mem
          · exact Subgroup.subset_closure hb_mem
          · exact Subgroup.mul_mem _ (Subgroup.subset_closure ha_mem)
              (Subgroup.subset_closure hb_mem)
        refine (Set.eq_of_subset_of_ncard_le hsub ?_ (Set.toFinite _)).symm
        have hc : ((Subgroup.closure ({a, b} : Set G)) : Set G).ncard = 4 := by
          rw [← Nat.card_coe_set_eq]
          exact hYcard
        rw [hc, h4c]
      have hdisj : Subgroup.closure ({a, b} : Set G) ⊓
          (pCoreIn 2 B.Hhat ⊔ B.U : Subgroup G) = ⊥ := by
        refine eq_bot_of_forall ?_
        intro z hz
        rw [Subgroup.mem_inf] at hz
        obtain ⟨hzY, hzVU⟩ := hz
        have hzI : z ∈ Work.CORE3.invSetIn B.Hhat y := by
          have hz' : z ∈ ({1, a, b, a * b} : Set G) := by rw [← hcl_eq]; exact hzY
          simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz'
          rcases hz' with hh | hh | hh | hh
          · rw [hh]; exact hone
          · rw [hh]; exact haI
          · rw [hh]; exact hbI
          · rw [hh]; exact habI
        exact hmemVU z hzI hzVU
      have hdvd := CardDvdSixOfDisjoint I hBc B h1 D (Subgroup.closure ({a, b} : Set G)) hYle hdisj
      rw [hYcard] at hdvd
      norm_num at hdvd
    · -- `a` and `b` do not commute: `a * b` has order three
      have hord_ab : orderOf (a * b) = 3 :=
        orderOf_mul_eq_three_of_not_commute hy hIeq hab hac hbc ha2 hb2 hcomm
      have habH : a * b ∈ B.Hhat := B.Hhat.mul_mem haI.1 hbI.1
      have hab_ne1 : a * b ≠ 1 := by
        intro hh
        have h2 : a = b⁻¹ := (mul_eq_one_iff_eq_inv).mp hh
        rw [inv_eq_self_of_orderOf_two hb2] at h2
        exact hab h2
      have hyab : y * (a * b) * y = a * b := by
        have h1 : (y * a * y) * (y * b * y) = y * (a * b) * y := by
          rw [show (y * a * y) * (y * b * y) = y * a * (y * y) * b * y by group, hy, mul_one]
          group
        rw [← h1, haI.2, hbI.2, inv_eq_self_of_orderOf_two ha2, inv_eq_self_of_orderOf_two hb2]
      have hyc : Commute y (a * b) := by
        have h' := congrArg (fun z => z * y) hyab
        rwa [show (y * (a * b) * y) * y = y * (a * b) by rw [mul_assoc, hy, mul_one]] at h'
      have hz_sq : (a * y) * (a * y) = 1 := by
        rw [show (a * y) * (a * y) = a * (y * a * y) by group, haI.2,
          inv_eq_self_of_orderOf_two ha2]
        exact ha2'
      have hz_ne1 : a * y ≠ 1 := by
        intro hh
        have h2 : a = y⁻¹ := (mul_eq_one_iff_eq_inv).mp hh
        rw [inv_eq_self_of_orderOf_two hy2] at h2
        exact hyH (by rw [← h2]; exact haI.1)
      have hzgz : (a * y) * (a * b) * (a * y)⁻¹ = (a * b)⁻¹ := by
        have hzinv : (a * y)⁻¹ = y * a := by
          rw [mul_inv_rev, inv_eq_self_of_orderOf_two hy2, inv_eq_self_of_orderOf_two ha2]
        rw [hzinv]
        have h1 : a * y * (a * b) * (y * a) = a * (y * (a * b) * y) * a := by group
        rw [h1, hyab]
        have h2 : a * (a * b) * a = (a * b)⁻¹ := by
          rw [show a * (a * b) * a = (a * a) * b * a by group, ha2', one_mul]
          rw [show b * a = (a * b)⁻¹ by rw [mul_inv_rev, inv_eq_self_of_orderOf_two hb2,
            inv_eq_self_of_orderOf_two ha2]]
        rw [h2]
      have hyC : y ∈ Subgroup.centralizer ((Subgroup.zpowers (a * b)) : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
        exact (hyc.zpow_right n).eq.symm
      have hab_inv_self : a * (a * b) * a = (a * b)⁻¹ := by
        rw [show a * (a * b) * a = (a * a) * b * a by group, ha2', one_mul]
        rw [show b * a = (a * b)⁻¹ by rw [mul_inv_rev, inv_eq_self_of_orderOf_two hb2,
          inv_eq_self_of_orderOf_two ha2]]
      have hab_inv_a : a * (a * b) * a⁻¹ = (a * b)⁻¹ := by
        rw [inv_eq_self_of_orderOf_two ha2]
        exact hab_inv_self
      refine ⟨a * y, (orderOf_eq_two_iff_mul_self _).mpr ⟨hz_sq, hz_ne1⟩, ⟨a, haI.1, rfl⟩,
        Subgroup.zpowers (a * b), Subgroup.zpowers_le.mpr habH, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact fun hbot => hab_ne1 (Subgroup.mem_bot.mp (hbot ▸ Subgroup.mem_zpowers (a * b)))
      · rw [Nat.card_zpowers, hord_ab]; norm_num
      · exact inverts_zpowers_of hzgz
      · exact even_card_centralizer_of_involution hy hyne hyC
      · exact even_card_normalizer_of_inverts hz_sq hz_ne1 (inverts_zpowers_of hzgz)
      · exact ⟨a, haI.1, ha2, inverts_zpowers_of hab_inv_a⟩

/-- **The signature of `Work.CORE3.J4.J4CosetStep` before design pass 23 added Bender's
`N_Ĥ(X)` witness.**  Provided as an adapter so that consumers written against the old shape keep
building: it is the projection of `J4CosetStep` forgetting the last conjunct. -/
theorem j4CosetStep_old {G : Type} [Group G] [Finite G] (I : Work.CORE3.Case1Inputs)
    (hBc : Work.GW2.BenderCtx G) (B : Work.GW2.BenderSetup G) (h1 : Work.GW2.Case1 B)
    (D : Work.GW2.Case1bData B) {y : G} (hy2 : orderOf y = 2) (hyH : y ∉ B.Hhat)
    (hy4 : Work.GW2.cosetInvCount B.Hhat y = 4) :
    ∃ z : G, orderOf z = 2 ∧ (∃ h ∈ B.Hhat, z = h * y) ∧
      ∃ X : Subgroup G, X ≤ B.Hhat ∧ X ≠ ⊥ ∧ Odd (Nat.card X) ∧ Work.GW2.Inverts z X ∧
        Even (Nat.card (Subgroup.centralizer (X : Set G))) ∧
        Even (Nat.card (Subgroup.normalizer (X : Set G))) := by
  obtain ⟨z, hz2, hk, X, hXle, hXne, hXodd, hinv, hC, hN, _hs⟩ :=
    J4CosetStep (G := G) I hBc B h1 D hy2 hyH hy4
  exact ⟨z, hz2, hk, X, hXle, hXne, hXodd, hinv, hC, hN⟩

end Work.CORE3.J4
