import Mathlib
import Submission.Work.BSW.Concl
import Submission.Work.BSW.Cases.K4.Setup
import Submission.Work.BSW.Cases.K4.CardSup
import Submission.Work.BSW.Cases.K4.CyclicNormalizer
import Submission.Work.BSW.Cases.K4.card_normalizer_sylow_seven
import Submission.Work.BSW.Cases.K4.card_normalizer_sylow_three
import Submission.Work.BSW.Cases.K4.exists_involution_inverting_of_card_eq_three
import Submission.Work.BSW.Cases.K4.exists_involution_inverting_of_orderOf_eq_four
import Submission.Work.BSW.Cases.K4.exists_not_mem_centralizer_of_isPGroup
import Submission.Work.BSW.Cases.K4.exists_orderOf_eq_four_of_card_eq_thirtysix
import Submission.Work.BSW.Cases.K4.sylow_three_ti
import Submission.Work.BSW.Cases.K4.natCard_sylow_five_eq_thirtysix

namespace Work.BSW.Cases

open Subgroup Work.GW2
open Work.BSW.Cases.K4

/-! ## The two cases -/

/-- The `|K| = 4`, `|G| = 168` case: Bender's conclusion (1)–(4) with `q = 7`. -/
theorem isBSWData_seven {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {t s : G} {K : Subgroup G} (h : BSWHyps2 G t s K)
    (hK4 : Nat.card ↥K = 4) (hG : Nat.card G = 168) : IsBSWData G 7 := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  obtain ⟨Q⟩ := Sylow.nonempty (p := 7) (G := G)
  have hQcard : Nat.card ↥(Q : Subgroup G) = 7 := by
    rw [Sylow.card_eq_multiplicity, hG]
    norm_num [Nat.factorization]
  have hNcard : Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G)) = 21 :=
    card_normalizer_sylow_seven hG Q
  -- `Q` is cyclic of order `7`, hence abelian, so `Q ≤ C_G(Q) ≤ N_G(Q)`
  haveI hcyc : IsCyclic ↥(Q : Subgroup G) := isCyclic_of_prime_card hQcard
  haveI hcomm : IsMulCommutative ↥(Q : Subgroup G) := IsCyclic.isMulCommutative
  have hQ_le_C : (Q : Subgroup G) ≤ Subgroup.centralizer ((Q : Subgroup G) : Set G) :=
    Subgroup.le_centralizer (Q : Subgroup G)
  have hC_le_N : Subgroup.centralizer ((Q : Subgroup G) : Set G) ≤
      Subgroup.normalizer ((Q : Subgroup G) : Set G) := Subgroup.centralizer_le_normalizer _
  -- `C_G(Q) = Q` (otherwise `N_G(Q) = C_G(Q)` and Burnside gives a proper normal subgroup)
  have hC_eq_Q : Subgroup.centralizer ((Q : Subgroup G) : Set G) = (Q : Subgroup G) := by
    have hdvd : Nat.card ↥(Subgroup.centralizer ((Q : Subgroup G) : Set G)) ∣ 21 := by
      have h' : Nat.card ↥(Subgroup.centralizer ((Q : Subgroup G) : Set G)) ∣
          Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G)) :=
        Subgroup.card_dvd_of_le hC_le_N
      rwa [hNcard] at h'
    have h7 : 7 ∣ Nat.card ↥(Subgroup.centralizer ((Q : Subgroup G) : Set G)) := by
      have h' : Nat.card ↥(Q : Subgroup G) ∣
          Nat.card ↥(Subgroup.centralizer ((Q : Subgroup G) : Set G)) :=
        Subgroup.card_dvd_of_le hQ_le_C
      rwa [hQcard] at h'
    rcases nat_eq_seven_or_twentyone hdvd h7 with hC7 | hC21
    · exact (Subgroup.eq_of_le_of_card_ge hQ_le_C (le_of_eq (by rw [hC7, hQcard]))).symm
    · exfalso
      have hCeq : Subgroup.centralizer ((Q : Subgroup G) : Set G) =
          Subgroup.normalizer ((Q : Subgroup G) : Set G) :=
        Subgroup.eq_of_le_of_card_ge hC_le_N (le_of_eq (by rw [hNcard, hC21]))
      obtain ⟨g, hgN, hgC⟩ := exists_not_mem_centralizer_of_isPGroup hnab
        (p := 7) (P := (Q : Subgroup G)) Q.isPGroup' (Sylow.not_dvd_index Q)
        (by rw [hG]; norm_num)
      have hgC' : g ∈ Subgroup.centralizer ((Q : Subgroup G) : Set G) := by
        rw [← hCeq] at hgN
        exact hgN
      exact hgC hgC'
  -- `Q` is TI with respect to its normalizer (its order is the prime `7`)
  have hTI : ∀ g : G, g ∉ Subgroup.normalizer ((Q : Subgroup G) : Set G) →
      (Q : Subgroup G) ⊓ conjSub g (Q : Subgroup G) = ⊥ := by
    intro g hg
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    have hxQ : x ∈ (Q : Subgroup G) := hx.1
    have hxQg : x ∈ conjSub g (Q : Subgroup G) := hx.2
    have hxord : orderOf x = 7 := by
      have hd : orderOf x ∣ 7 := by
        have h' := Work.BSW.Cases.K4.orderOf_dvd_natCard_of_mem (H := (Q : Subgroup G)) hxQ
        rwa [hQcard] at h'
      rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_seven (orderOf x) hd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hx1
      · exact h
    have hgen : Subgroup.zpowers x = (Q : Subgroup G) := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxQ) ?_
      rw [Nat.card_zpowers, hxord, hQcard]
    have hle : (Q : Subgroup G) ≤ conjSub g (Q : Subgroup G) := by
      intro y hy
      rw [← hgen] at hy
      exact (Subgroup.zpowers_le (g := x) (H := conjSub g (Q : Subgroup G))).mpr hxQg hy
    have hcard : Nat.card ↥(conjSub g (Q : Subgroup G)) = Nat.card ↥(Q : Subgroup G) := by
      rw [conjSub]
      exact Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
        (MulAut.conj g).injective
    have heq : conjSub g (Q : Subgroup G) = (Q : Subgroup G) :=
      (Subgroup.eq_of_le_of_card_ge hle (le_of_eq hcard)).symm
    exact hg (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq)
  -- an element of order `3` in `N_G(Q) \ Q`
  let N : Subgroup G := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  have hNcard' : Nat.card ↥N = 21 := hNcard
  have hQ_le_N : (Q : Subgroup G) ≤ N := Subgroup.le_normalizer
  obtain ⟨y, hyN, hy_notQ⟩ : ∃ y : G, y ∈ N ∧ y ∉ Q := by
    by_contra hcon
    push Not at hcon
    have hNle : N ≤ (Q : Subgroup G) := fun x hx => hcon x hx
    have hcard : Nat.card ↥N ≤ Nat.card ↥(Q : Subgroup G) :=
      Nat.card_le_card_of_injective (fun x : ↥N => (⟨x.1, hNle x.2⟩ : ↥(Q : Subgroup G)))
        (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
    rw [hNcard', hQcard] at hcard
    omega
  have hy21 : orderOf y ∣ 21 := by
    have h1 := Work.BSW.Cases.K4.orderOf_dvd_natCard_of_mem (H := N) hyN
    rwa [hNcard'] at h1
  have hy_ne1 : orderOf y ≠ 1 := by
    intro h1
    exact hy_notQ (by rw [orderOf_eq_one_iff.mp h1]; exact (Q : Subgroup G).one_mem)
  have hy_ne7 : orderOf y ≠ 7 := by
    intro hy7
    have hzp_le_N : Subgroup.zpowers y ≤ N := Subgroup.zpowers_le.mpr hyN
    have hNrm : Subgroup.zpowers y ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) := hzp_le_N
    have hsup_le : (Q : Subgroup G) ⊔ Subgroup.zpowers y ≤ N := sup_le hQ_le_N hzp_le_N
    have hdvd : Nat.card ↥((Q : Subgroup G) ⊔ Subgroup.zpowers y) ∣ 21 := by
      have h' : Nat.card ↥((Q : Subgroup G) ⊔ Subgroup.zpowers y) ∣ Nat.card ↥N :=
        Subgroup.card_dvd_of_le hsup_le
      rwa [hNcard'] at h'
    have hinf : (Q : Subgroup G) ⊓ Subgroup.zpowers y = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      by_contra hx1
      have hxQ : x ∈ (Q : Subgroup G) := hx.1
      have hxy : x ∈ Subgroup.zpowers y := hx.2
      have hxord : orderOf x = 7 := by
        have hle : Subgroup.zpowers x ≤ Subgroup.zpowers y := Subgroup.zpowers_le.mpr hxy
        have hd : orderOf x ∣ orderOf y := by
          have h' := Subgroup.card_dvd_of_le hle
          rwa [Nat.card_zpowers, Nat.card_zpowers] at h'
        rw [hy7] at hd
        rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_seven (orderOf x) hd with h1 | h1
        · exact absurd (orderOf_eq_one_iff.mp h1) hx1
        · exact h1
      have hgen : Subgroup.zpowers x = Subgroup.zpowers y := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxy) ?_
        rw [Nat.card_zpowers, Nat.card_zpowers, hxord, hy7]
      have hyQ : y ∈ (Q : Subgroup G) := by
        have hy_in : y ∈ Subgroup.zpowers y := Subgroup.mem_zpowers y
        rw [← hgen] at hy_in
        exact (Subgroup.zpowers_le.mpr hxQ) hy_in
      exact hy_notQ hyQ
    have hcard49 : Nat.card ↥((Q : Subgroup G) ⊔ Subgroup.zpowers y) = 49 := by
      rw [card_sup_of_le_normalizer_of_inf_eq_bot hNrm hinf, hQcard, Nat.card_zpowers, hy7]
    rw [hcard49] at hdvd
    exact absurd hdvd (by norm_num)
  obtain ⟨d, hdN, hd3, hd_notQ⟩ : ∃ d : G, d ∈ N ∧ orderOf d = 3 ∧ d ∉ Q := by
    have hdiv : (21).divisors = {1, 3, 7, 21} := by decide
    have hy21' : orderOf y ∈ ({1, 3, 7, 21} : Finset ℕ) := by
      rw [← hdiv]
      exact Nat.mem_divisors.mpr ⟨hy21, by norm_num⟩
    simp only [Finset.mem_insert, Finset.mem_singleton] at hy21'
    rcases hy21' with h1 | h3 | h7 | h21
    · exact absurd h1 hy_ne1
    · exact ⟨y, hyN, h3, hy_notQ⟩
    · exact absurd h7 hy_ne7
    · refine ⟨y ^ 7, Subgroup.pow_mem _ hyN 7, ?_, ?_⟩
      · rw [orderOf_pow, h21]
        norm_num
      · intro h7Q
        have hle : Subgroup.zpowers (y ^ 7) ≤ (Q : Subgroup G) := Subgroup.zpowers_le.mpr h7Q
        have hdvd : Nat.card ↥(Subgroup.zpowers (y ^ 7)) ∣ Nat.card ↥(Q : Subgroup G) :=
          Subgroup.card_dvd_of_le hle
        have h3 : Nat.card ↥(Subgroup.zpowers (y ^ 7)) = 3 := by
          rw [Nat.card_zpowers, orderOf_pow, h21]
          norm_num
        rw [h3, hQcard] at hdvd
        exact absurd hdvd (by norm_num)
  -- build the data for `q = 7`
  have hDcard3 : Nat.card ↥(Subgroup.zpowers d) = 3 := by
    rw [Nat.card_zpowers, hd3]
  have hDcard : Nat.card ↥(Subgroup.zpowers d) = (7 - 1) / 2 := by
    rw [hDcard3, show (7 - 1) / 2 = 3 from rfl]
  have hQD : (Q : Subgroup G) ⊓ Subgroup.zpowers d = ⊥ := by
    refine Work.BSW.Cases.K4.inf_eq_bot_of_coprime ?_
    rw [hQcard, hDcard3]
    norm_num
  have hDnorm : Subgroup.zpowers d ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hdN
  have hsup : Subgroup.normalizer ((Q : Subgroup G) : Set G) =
      (Q : Subgroup G) ⊔ Subgroup.zpowers d := by
    exact (sup_eq_of_card_mul_eq (Q := (Q : Subgroup G)) (D := Subgroup.zpowers d) (N := N)
      hQ_le_N (Subgroup.zpowers_le.mpr hdN) hDnorm hQD
      (by rw [hQcard, hDcard3, hNcard'])).symm
  have hnorm : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ Subgroup.zpowers d →
      Subgroup.normalizer (X : Set G) =
        Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    intro X hXne hXle
    have hXcard : Nat.card ↥X ∣ 3 := by
      have h' : Nat.card ↥X ∣ Nat.card ↥(Subgroup.zpowers d) := Subgroup.card_dvd_of_le hXle
      rwa [hDcard3] at h'
    rcases Nat.Prime.eq_one_or_self_of_dvd Nat.prime_three (Nat.card ↥X) hXcard with h1 | h3c
    · exact absurd (eq_bot_of_card_eq_one h1) hXne
    · have hXz : X = Subgroup.zpowers d := by
        refine Subgroup.eq_of_le_of_card_ge hXle ?_
        rw [hDcard3, h3c]
      rw [hXz]
  have hinv : ∃ u : G, orderOf u = 2 ∧ u ∉ Subgroup.zpowers d ∧
      Inverts u (Subgroup.zpowers d) ∧
      Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) =
        Subgroup.zpowers d ⊔ Subgroup.zpowers u := by
    have hP : IsPGroup 3 ↥(Subgroup.zpowers d) :=
      IsPGroup.of_card (by rw [hDcard3]; exact (pow_one 3).symm)
    have hidx : ¬ 3 ∣ (Subgroup.zpowers d).index := by
      intro h3
      have hmul := Subgroup.card_mul_index (Subgroup.zpowers d)
      rw [Nat.card_zpowers, hd3, hG] at hmul
      obtain ⟨c, hc⟩ := h3
      omega
    obtain ⟨u0, hu0N, hu0C⟩ := exists_not_mem_centralizer_of_isPGroup hnab (p := 3)
      hP hidx (by rw [hG]; norm_num)
    obtain ⟨u, hu2, huD, huInv⟩ := exists_involution_inverting_of_card_eq_three
      (Subgroup.zpowers d) hDcard3 (Work.BSW.Cases.K4.orderOf_ne_six h hK4)
      ⟨u0, hu0N, hu0C⟩
    refine ⟨u, hu2, huD, huInv, ?_⟩
    exact normalizer_zpowers_eq_sup_of_order_three hd3 hu2 huD huInv
      (centralizer_zpowers_eq_of_order_three_168 hnab h hK4 hG d hd3)
  unfold Work.BSW.IsBSWData
  exact ⟨⟨7, 1, ⟨Nat.prime_seven⟩, by norm_num, by norm_num⟩, by norm_num, (Q : Subgroup G),
    hQcard, hC_eq_Q, hTI, Subgroup.zpowers d, inferInstance, hDcard, hQD, hsup, hnorm, hinv,
    by rw [hG]⟩

/-- The `|K| = 4`, `|G| = 360` case: Bender's conclusion (1)–(4) with `q = 9`. -/
theorem isBSWData_nine {G : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (hnab : ∃ a b : G, a * b ≠ b * a) {t s : G} {K : Subgroup G} (h : BSWHyps2 G t s K)
    (hK4 : Nat.card ↥K = 4) (hG : Nat.card G = 360) : IsBSWData G 9 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨Q⟩ := Sylow.nonempty (p := 3) (G := G)
  have hQcard : Nat.card ↥(Q : Subgroup G) = 9 := by
    rw [Sylow.card_eq_multiplicity, hG]
    norm_num [Nat.factorization]
  have hburn : ∀ {p : ℕ} [Fact (Nat.Prime p)] (Q' : Sylow p G), p ∣ Nat.card G →
      ∃ g : G, g ∈ Subgroup.normalizer (Q' : Set G) ∧
        g ∉ Subgroup.centralizer ((Q' : Subgroup G) : Set G) :=
    fun Q' hp => exists_not_mem_centralizer_of_isPGroup hnab Q'.isPGroup'
      (Sylow.not_dvd_index Q') hp
  have hNcard : Nat.card ↥(Subgroup.normalizer ((Q : Subgroup G) : Set G)) = 36 :=
    card_normalizer_sylow_three hG hburn Q
  let N : Subgroup G := Subgroup.normalizer ((Q : Subgroup G) : Set G)
  have hNcard' : Nat.card ↥N = 36 := hNcard
  have hQ_le_N : (Q : Subgroup G) ≤ N := Subgroup.le_normalizer
  -- `Q` has order `9`, hence is abelian
  haveI hcomm : IsMulCommutative ↥(Q : Subgroup G) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) (by rw [hQcard]; norm_num)
  have hQ_le_C : (Q : Subgroup G) ≤ Subgroup.centralizer ((Q : Subgroup G) : Set G) :=
    Subgroup.le_centralizer (Q : Subgroup G)
  have hC_le_N : Subgroup.centralizer ((Q : Subgroup G) : Set G) ≤ N :=
    Subgroup.centralizer_le_normalizer _
  -- `C_G(Q) = Q`
  have hC_eq_Q : Subgroup.centralizer ((Q : Subgroup G) : Set G) = (Q : Subgroup G) := by
    set C := Subgroup.centralizer ((Q : Subgroup G) : Set G) with hCdef
    have hQ_le_C' : (Q : Subgroup G) ≤ C := hQ_le_C
    have hC_le_N' : C ≤ N := hC_le_N
    have hdvd : Nat.card ↥C ∣ 36 := by
      have h' : Nat.card ↥C ∣ Nat.card ↥N := Subgroup.card_dvd_of_le hC_le_N'
      rwa [hNcard'] at h'
    have h9 : 9 ∣ Nat.card ↥C := by
      have h' : Nat.card ↥(Q : Subgroup G) ∣ Nat.card ↥C := Subgroup.card_dvd_of_le hQ_le_C'
      rwa [hQcard] at h'
    have hm : Nat.card ↥C = 9 ∨ Nat.card ↥C = 18 ∨ Nat.card ↥C = 36 := by
      obtain ⟨a, ha⟩ := hdvd
      obtain ⟨b, hb⟩ := h9
      have hb4 : b * a = 4 := by
        have h' : 9 * (b * a) = 9 * 4 := by
          calc 9 * (b * a) = (9 * b) * a := by ring
            _ = Nat.card ↥C * a := by rw [← hb]
            _ = 36 := ha.symm
            _ = 9 * 4 := by norm_num
        exact Nat.eq_of_mul_eq_mul_left (by norm_num) h'
      have hb_dvd : b ∣ 4 := ⟨a, hb4.symm⟩
      obtain ⟨i, hi, hbi⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mp (by simpa using hb_dvd)
      have hbcases : b = 1 ∨ b = 2 ∨ b = 4 := by
        interval_cases i
        · exact Or.inl (by simpa using hbi)
        · exact Or.inr (Or.inl (by simpa using hbi))
        · exact Or.inr (Or.inr (by simpa using hbi))
      rcases hbcases with h1 | h2 | h4
      · exact Or.inl (by rw [hb, h1, mul_one])
      · exact Or.inr (Or.inl (by rw [hb, h2]))
      · exact Or.inr (Or.inr (by rw [hb, h4]))
    rcases hm with h9' | h18 | h36
    · rw [hCdef]
      exact (Subgroup.eq_of_le_of_card_ge hQ_le_C' (le_of_eq (by rw [h9', hQcard]))).symm
    · -- `|C_G(Q)| = 18` would contain an involution centralizing `Q`, impossible
      exfalso
      haveI : Fintype ↥C := Fintype.ofFinite _
      obtain ⟨w, hw⟩ := exists_prime_orderOf_dvd_card (G := ↥C) (p := 2)
        (by rw [← Nat.card_eq_fintype_card, h18]; norm_num)
      set wG : G := (w : G) with hwG
      have hw2 : orderOf wG = 2 := by
        rw [hwG, Subgroup.orderOf_coe, hw]
      have hwmem : wG ∈ Subgroup.centralizer ((Q : Subgroup G) : Set G) := by
        rw [hwG, ← hCdef]
        exact w.2
      have hQ_le_Cw : (Q : Subgroup G) ≤ Subgroup.centralizer ({wG} : Set G) := by
        intro q hq
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact (Subgroup.mem_centralizer_iff.mp hwmem) q hq
      have hcard_le : Nat.card ↥(Q : Subgroup G) ≤
          Nat.card ↥(Subgroup.centralizer ({wG} : Set G)) :=
        Nat.card_le_card_of_injective (fun x : ↥(Q : Subgroup G) =>
          (⟨x.1, hQ_le_Cw x.2⟩ : ↥(Subgroup.centralizer ({wG} : Set G))))
          (fun a b hab => Subtype.ext (by simpa using congrArg Subtype.val hab))
      have hw8 := Work.BSW.Cases.K4.card_centralizer_of_orderOf_eq_two h hK4 hw2
      rw [hQcard, hw8] at hcard_le
      omega
    · -- `|C_G(Q)| = 36` means `C_G(Q) = N_G(Q)`, contradicting Burnside
      exfalso
      have hCeq : C = N :=
        Subgroup.eq_of_le_of_card_ge hC_le_N' (le_of_eq (by rw [hNcard', h36]))
      obtain ⟨g, hgN, hgC⟩ := hburn Q (by rw [hG]; norm_num)
      have hgN' : g ∈ N := hgN
      have hgC' : g ∈ C := hCeq ▸ hgN'
      rw [hCdef] at hgC'
      exact hgC hgC'
  -- `n₅ = 36` and `Q` is TI with respect to its normalizer
  have h5 : Nat.card (Sylow 5 G) = 36 :=
    natCard_sylow_five_eq_thirtysix hnab h hK4 hG
  have hTI : ∀ g : G, g ∉ Subgroup.normalizer ((Q : Subgroup G) : Set G) →
      (Q : Subgroup G) ⊓ conjSub g (Q : Subgroup G) = ⊥ :=
    fun g hg => sylow_three_ti hnab h hK4 hG h5 Q hNcard hC_eq_Q g hg
  -- `Q ⊴ N`
  have hQnorm : ((Q : Subgroup G).subgroupOf N).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le_N).mpr le_rfl
  -- an element of `N` of order `4`
  obtain ⟨d, hdN, hd4⟩ := exists_orderOf_eq_four_of_card_eq_thirtysix (N := N)
    (Q := (Q : Subgroup G)) hNcard' hQcard hQ_le_N hQnorm hC_eq_Q
    (fun x => Work.BSW.Cases.K4.orderOf_ne_six h hK4 x)
    (fun x => Work.BSW.Cases.K4.orderOf_ne_eighteen h hK4 x)
  have hDcard4 : Nat.card ↥(Subgroup.zpowers d) = 4 := by
    rw [Nat.card_zpowers, hd4]
  have hDcard : Nat.card ↥(Subgroup.zpowers d) = (9 - 1) / 2 := by
    rw [hDcard4, show (9 - 1) / 2 = 4 from rfl]
  have hQD : (Q : Subgroup G) ⊓ Subgroup.zpowers d = ⊥ := by
    refine Work.BSW.Cases.K4.inf_eq_bot_of_coprime ?_
    rw [hQcard, hDcard4]
    norm_num
  have hDnorm : Subgroup.zpowers d ≤ Subgroup.normalizer ((Q : Subgroup G) : Set G) :=
    Subgroup.zpowers_le.mpr hdN
  have hsup : Subgroup.normalizer ((Q : Subgroup G) : Set G) =
      (Q : Subgroup G) ⊔ Subgroup.zpowers d := by
    exact (sup_eq_of_card_mul_eq (Q := (Q : Subgroup G)) (D := Subgroup.zpowers d) (N := N)
      hQ_le_N (Subgroup.zpowers_le.mpr hdN) hDnorm hQD
      (by rw [hQcard, hDcard4, hNcard'])).symm
  -- the involution `u` inverting `D`, and the resulting description of `N_G(D)`
  obtain ⟨u, hu2, huD, huInv⟩ := exists_involution_inverting_of_orderOf_eq_four h hK4 d hd4
  have hC4 : Subgroup.centralizer (Subgroup.zpowers d : Set G) = Subgroup.zpowers d :=
    centralizer_zpowers_eq_of_order_four_360 h hK4 hG d hd4
  have hNsup : Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) =
      Subgroup.zpowers d ⊔ Subgroup.zpowers u :=
    normalizer_zpowers_eq_sup_of_order_four hd4 hu2 huD huInv hC4
  -- `N_G(⟨d * d⟩) = N_G(⟨d⟩)`: both are `⟨d⟩ ⊔ ⟨u⟩`, of order `8`
  have hd2 : orderOf (d * d) = 2 := by
    rw [show d * d = d ^ 2 from (pow_two d).symm, orderOf_pow, hd4]
    norm_num
  have hdd1 : (d * d) * (d * d) = 1 := by
    have hh := pow_orderOf_eq_one (d * d)
    rw [hd2] at hh
    rwa [pow_two] at hh
  have hddinv : (d * d)⁻¹ = d * d := inv_eq_of_mul_eq_one_right hdd1
  have hu_inv : u * d * u⁻¹ = d⁻¹ := huInv d (Subgroup.mem_zpowers d)
  have huC : u ∈ Subgroup.centralizer ({d * d} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc u * (d * d) = ((u * d * u⁻¹) * (u * d * u⁻¹)) * u := by group
      _ = (d⁻¹ * d⁻¹) * u := by rw [hu_inv]
      _ = (d * d) * u := by rw [← mul_inv_rev d d, hddinv]
  have hdC : d ∈ Subgroup.centralizer ({d * d} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    show d * (d * d) = (d * d) * d
    group
  have hDleCd2 : Subgroup.zpowers d ≤ Subgroup.centralizer ({d * d} : Set G) :=
    Subgroup.zpowers_le.mpr hdC
  have hCd2card : Nat.card ↥(Subgroup.centralizer ({d * d} : Set G)) = 8 :=
    card_centralizer_of_orderOf_eq_two h hK4 hd2
  have hNle : Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) ≤
      Subgroup.centralizer ({d * d} : Set G) := by
    rw [hNsup]
    exact sup_le hDleCd2 (Subgroup.zpowers_le.mpr huC)
  have hCd2le : Subgroup.centralizer ({d * d} : Set G) ≤
      Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) :=
    le_normalizer_of_two_mul_card hDleCd2 (by rw [hDcard4, hCd2card])
  have hNd2 : Subgroup.normalizer ((Subgroup.zpowers (d * d) : Subgroup G) : Set G) =
      Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    rw [normalizer_zpowers_eq_centralizer_of_orderOf_eq_two hd2]
    exact le_antisymm hCd2le hNle
  have hnorm : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ Subgroup.zpowers d →
      Subgroup.normalizer (X : Set G) =
        Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) := by
    intro X hXne hXle
    have hXcard : Nat.card ↥X ∣ 4 := by
      have h' : Nat.card ↥X ∣ Nat.card ↥(Subgroup.zpowers d) := Subgroup.card_dvd_of_le hXle
      rwa [hDcard4] at h'
    obtain ⟨i, hi, hXi⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 2)).mp (by simpa using hXcard)
    interval_cases i
    · exact absurd (eq_bot_of_card_eq_one (by simpa using hXi)) hXne
    · -- `|X| = 2`: then `X = ⟨d * d⟩` and `N_G(⟨d * d⟩) = N_G(⟨d⟩)`
      have hX2 : Nat.card ↥X = 2 := by simpa using hXi
      rw [eq_zpowers_sq_of_le_zpowers_of_card_two hd4 X hXle hX2]
      exact hNd2
    · -- `|X| = 4`: then `X = ⟨d⟩`
      have hX4 : Nat.card ↥X = 4 := by simpa using hXi
      have hXeq : X = Subgroup.zpowers d := by
        refine Subgroup.eq_of_le_of_card_ge hXle ?_
        rw [hDcard4, hX4]
      rw [hXeq]
  have hinv : ∃ u : G, orderOf u = 2 ∧ u ∉ Subgroup.zpowers d ∧
      Inverts u (Subgroup.zpowers d) ∧
      Subgroup.normalizer ((Subgroup.zpowers d : Subgroup G) : Set G) =
        Subgroup.zpowers d ⊔ Subgroup.zpowers u :=
    ⟨u, hu2, huD, huInv, hNsup⟩
  unfold Work.BSW.IsBSWData
  exact ⟨⟨3, 2, ⟨Nat.prime_three⟩, by norm_num, by norm_num⟩, by norm_num, (Q : Subgroup G),
    hQcard, hC_eq_Q, hTI, Subgroup.zpowers d, inferInstance, hDcard, hQD, hsup, hnorm, hinv,
    by rw [hG]⟩

/-- With `|K| = 4` and `|G| = 168` or `360`: Bender's conclusion (1)–(4) with `q = 7` (if
`|G| = 168`: the Sylow 7-subgroup, `N_G(Q) ≅ 7:3`, `D` of order `3` and `(q−1)/2 = 3`) or `q = 9`
(if `|G| = 360`: the Sylow 3-subgroup `Q` of order `9`, `N_G(Q) ≅ 3²:C₄`, `D` of order `4` and
`(q−1)/2 = 4`).  `IsBSWData G 7` respectively `IsBSWData G 9` records its own order equation
`|G| = q(q²−1)/2`, so exactly one of the two alternatives can hold for a given `G`. -/
theorem bswK4StructureProp : Work.BSW.BSWK4StructureProp := by
  intro G _ _ hS hnab t s K h hK4 hG
  haveI : IsSimpleGroup G := hS
  rcases hG with hG | hG
  · exact Or.inl (isBSWData_seven hnab h hK4 hG)
  · exact Or.inr (isBSWData_nine hnab h hK4 hG)

end Work.BSW.Cases
