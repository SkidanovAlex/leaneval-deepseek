import Mathlib
import Submission.Work.ThmF.ChV3.Step16Defs
import Submission.Work.ThmF.ChV3.Prove.S1_centralizerP_eq
import Submission.Work.PGroup.card_sup_mul_card_inf_of_le_normalizer

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThmF.ChV3.Prove

open Classical LeanEval.GroupTheory.Defs Submission.Blueprint
open Pointwise

variable {G : Type} [Group G] [Finite G]

/-- The centre of a subgroup `R1`, viewed as a subgroup of the ambient group `G`, is the
intersection `R1 ⊓ C_G(R1)`; as a subgroup of `↥R1` it is `Subgroup.center ↥R1`. -/
private lemma center_subgroupOf_inf_centralizer (R1 : Subgroup G) :
    (R1 ⊓ Subgroup.centralizer (R1 : Set G)).subgroupOf R1 = Subgroup.center ↥R1 := by
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf, Subgroup.mem_centralizer_iff,
    Subgroup.mem_center_iff]
  constructor
  · rintro ⟨-, hx⟩ g
    exact Subtype.ext (hx (g : G) g.2)
  · intro hx
    exact ⟨x.2, fun y hy => congrArg (fun z : ↥R1 => (z : G)) (hx ⟨y, hy⟩)⟩

/-- Conjugation by an element of `N_G(R1)` maps the centre of `R1` into itself. -/
private lemma map_conj_inf_centralizer_le (R1 : Subgroup G) {y : G}
    (hy : y ∈ Subgroup.normalizer (R1 : Set G)) :
    (R1 ⊓ Subgroup.centralizer (R1 : Set G)).map (MulAut.conj y).toMonoidHom
      ≤ R1 ⊓ Subgroup.centralizer (R1 : Set G) := by
  intro x hx
  rw [Subgroup.mem_map] at hx
  obtain ⟨z, hz, hzx⟩ := hx
  rw [← hzx]
  rw [Subgroup.mem_inf] at hz ⊢
  obtain ⟨hz1, hz2⟩ := hz
  rw [Subgroup.mem_centralizer_iff] at hz2 ⊢
  refine ⟨?_, ?_⟩
  · simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      using (Subgroup.mem_normalizer_iff.mp hy z).mp hz1
  · intro h hh
    have hh' : y⁻¹ * h * y ∈ R1 :=
      (Subgroup.mem_normalizer_iff.mp hy (y⁻¹ * h * y)).mpr (by simpa [mul_assoc] using hh)
    have hcomm := hz2 (y⁻¹ * h * y) hh'
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hcomm ⊢
    calc h * (y * z * y⁻¹)
        = y * (y⁻¹ * h * y) * z * y⁻¹ := by group
      _ = y * ((y⁻¹ * h * y) * z) * y⁻¹ := by group
      _ = y * (z * (y⁻¹ * h * y)) * y⁻¹ := by rw [hcomm]
      _ = (y * z * y⁻¹) * h := by group

/-- Conjugation by an element of `N_G(R1)` fixes the centre of `R1`. -/
private lemma map_conj_inf_centralizer_eq (R1 : Subgroup G) {y : G}
    (hy : y ∈ Subgroup.normalizer (R1 : Set G)) :
    (R1 ⊓ Subgroup.centralizer (R1 : Set G)).map (MulAut.conj y).toMonoidHom
      = R1 ⊓ Subgroup.centralizer (R1 : Set G) := by
  apply le_antisymm (map_conj_inf_centralizer_le R1 hy)
  have hy' : y⁻¹ ∈ Subgroup.normalizer (R1 : Set G) :=
    (Subgroup.normalizer (R1 : Set G)).inv_mem hy
  have h1 := map_conj_inf_centralizer_le R1 hy'
  have h2 := Subgroup.map_mono (f := (MulAut.conj y).toMonoidHom) h1
  rwa [Subgroup.map_map,
    show (MulAut.conj y).toMonoidHom.comp (MulAut.conj y⁻¹).toMonoidHom = MonoidHom.id G from
      MonoidHom.ext fun z => by simp [MulAut.conj_apply, mul_assoc],
    Subgroup.map_id] at h2

/-- **`Z(R₁) = T` in case (10-1) of Peterfalvi II Ch. V §3 step (12).**

With `m = 1` and `Σ = 1`, the group `R = T × P` of step (11) has order `p²`, and `R₁` is a
`p`-group of order `p³` normalised by `N_G(R)` and containing `R`.  The centre `Z(R₁)` lies in
`C_{R₁}(P) = R` (since `R₁ ≰ C_G(P)`: `|C_G(P)| = p²(p−1)` is not divisible by `p³`), has order
`p`, and is not `P`; it is invariant under `C_Q(P)` (characteristic in `R₁`, and `C_Q(P)` lies in
`N_G(R₁)`).  But `C_Q(P)` is sharply transitive on the order-`p` subgroups of `R` distinct from
`T` and `P` (`h11.reg`), so a `C_Q(P)`-invariant such subgroup can only be `T`; hence
`Z(R₁) = T`. -/
theorem Center_R1_101 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t s r : G} {P : Subgroup G}
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC4 : Submission.Blueprint.ChIIFourProp)
    (c : Work.ThmF.ChV3.CtxF H Q t s r P) (h15 : Work.ThmF.ChV3.Chain15 H Q t s r P)
    (h7 : Work.ThmF.ChV3.Ker H Q P t = P) (hpf : Nat.card P = orderOf (s * t))
    {T : Subgroup G} (h11 : Work.ThmF.ChV3.Step11Out H Q t P h15.R T)
    (hm1 : h15.m = 1) (hsig : Work.ThmF.ChV3.Sig H t P = ⊥)
    {R1 : Subgroup G} (hRR1 : h15.R ≤ R1) (hR1N : R1 ≤ Work.ThmF.ChV3.NG h15.R)
    (hR1n : Work.ThmF.ChV3.NG h15.R ≤ Work.ThmF.ChV3.NG R1)
    (hR1c : Nat.card R1 = Nat.card P ^ 3) :
    Subgroup.center ↥R1 = T.subgroupOf R1 ∧ Nat.card ↥T = Nat.card P := by
  classical
  set p : ℕ := Nat.card P with hp
  have hp_prime : p.Prime := c.P_prime
  -- `P ≤ D = twoPoint H t`, so `p` divides the odd number `|D|`: `p` is odd, hence `p ≥ 3`.
  have hP_twoPoint : P ≤ twoPoint H t := c.P_le.trans inf_le_left
  have hp_dvd : p ∣ Nat.card (twoPoint H t) := by
    rw [hp]; exact Subgroup.card_dvd_of_le hP_twoPoint
  have hodd_D : Odd (Nat.card (twoPoint H t)) := split_odd_card_twoPoint c.split
  have hp_ne_two : p ≠ 2 := by
    intro h2
    rw [h2] at hp_dvd
    exact (Nat.not_even_iff_odd.mpr hodd_D) (even_iff_two_dvd.mpr hp_dvd)
  have hp_ge3 : 3 ≤ p := by have := hp_prime.two_le; omega
  -- ## Basic cardinalities
  have hcardR : Nat.card h15.R = p ^ 2 := by
    have h := h15.hcardR
    rw [h7] at h
    rw [← hpf, hm1, pow_one] at h
    rw [← hp] at h
    rw [h, pow_two]
  have hT_le_R : T ≤ h15.R := by rw [← h11.TPR]; exact le_sup_left
  have hP_le_R : P ≤ h15.R := by rw [← h11.TPR]; exact le_sup_right
  have hP_le_R1 : P ≤ R1 := hP_le_R.trans hRR1
  -- `|T| = |P|`: `R = T ⊔ P` is a direct product since `R` is abelian.
  have hPnormT : P ≤ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro q hq t ht
    have hcomm := h11.comm.is_comm.comm ⟨q, hP_le_R hq⟩ ⟨t, hT_le_R ht⟩
    have hqt : q * t = t * q := congrArg Subtype.val hcomm
    rw [hqt, mul_assoc, mul_inv_cancel, mul_one]
    exact ht
  have hcardT : Nat.card ↥T = Nat.card P := by
    have h := Work.PGroup.card_sup_mul_card_inf_of_le_normalizer (G := G) (H := T) (K := P) hPnormT
    rw [h11.TPR, h11.TP, Subgroup.card_bot, mul_one] at h
    -- h : Nat.card h15.R = Nat.card ↥T * Nat.card ↥P
    rw [hcardR, show Nat.card ↥P = p from hp.symm] at h
    have h' : p * p = Nat.card ↥T * p := by rw [pow_two] at h; exact h
    have : Nat.card ↥T = p := Nat.eq_of_mul_eq_mul_right hp_prime.pos h'.symm
    rw [← hp]; exact this
  -- `|C_Q(P)| = p − 1`
  have hcardCQ : Nat.card ↥(CQ Q P) = p - 1 := by
    have h := h15.hcq
    rw [← hpf, hm1, pow_one] at h
    omega
  have hSig_bot : Nat.card ↥(Sig H t P) = 1 := by rw [hsig]; exact Subgroup.card_bot
  -- `|C_G(P)| = p²(p−1)`
  have hcardCGP : Nat.card ↥(Subgroup.centralizer (P : Set G)) = p ^ 2 * (p - 1) := by
    have h := (S1_centralizerP_eq hFT hC4 c h15 h7 hpf).2.2
    rw [hcardR, hcardCQ, hSig_bot, mul_one] at h
    exact h
  -- ## `R₁ ⊄ C_G(P)`: `p³ ∤ p²(p−1)`
  have hnotle : ¬ R1 ≤ Subgroup.centralizer (P : Set G) := by
    intro hle
    have hdvd : Nat.card ↥R1 ∣ Nat.card ↥(Subgroup.centralizer (P : Set G)) :=
      Subgroup.card_dvd_of_le hle
    rw [hR1c, hcardCGP] at hdvd
    rw [show Nat.card P ^ 3 = p ^ 2 * p by rw [← hp]; ring] at hdvd
    have hpdvd : p ∣ p - 1 :=
      (Nat.mul_dvd_mul_iff_left (pow_pos hp_prime.pos 2)).mp hdvd
    have hp1 : p ∣ 1 := by
      have h := Nat.dvd_sub (dvd_refl p) hpdvd
      rwa [show p - (p - 1) = 1 by omega] at h
    exact hp_prime.not_dvd_one hp1
  -- ## `C_{R₁}(P) = R`, i.e. `R₁ ⊓ C_G(P) = R`
  have hRinfCG : R1 ⊓ Subgroup.centralizer (P : Set G) = h15.R := by
    have hRle : h15.R ≤ R1 ⊓ Subgroup.centralizer (P : Set G) := le_inf hRR1 h15.hRc
    -- `|R₁ ⊓ C_G(P)|` divides `p³` and is a multiple of `p²`
    have hdvdM : Nat.card ↥(R1 ⊓ Subgroup.centralizer (P : Set G)) ∣ p ^ 3 := by
      have := Subgroup.card_dvd_of_le
        (show R1 ⊓ Subgroup.centralizer (P : Set G) ≤ R1 from inf_le_left)
      rwa [hR1c] at this
    obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow hp_prime).mp hdvdM
    have hge : 2 ≤ k := by
      by_contra hlt
      have hk1 : k ≤ 1 := by omega
      have hdvd2 : p ^ 2 ∣ Nat.card ↥(R1 ⊓ Subgroup.centralizer (P : Set G)) := by
        rw [← hcardR]; exact Subgroup.card_dvd_of_le hRle
      rw [hk] at hdvd2
      rw [Nat.pow_dvd_pow_iff_le_right hp_prime.one_lt] at hdvd2
      omega
    have hk_eq : k = 2 := by
      rcases (by omega : k = 2 ∨ k = 3) with hk2 | hk3
      · exact hk2
      · exfalso
        have hcardM : Nat.card ↥(R1 ⊓ Subgroup.centralizer (P : Set G)) = p ^ 3 := by
          rw [hk, hk3]
        have hMR1 : R1 ⊓ Subgroup.centralizer (P : Set G) = R1 := by
          apply Subgroup.eq_of_le_of_card_ge inf_le_left
          rw [hcardM, hR1c]
        exact hnotle (by rw [← hMR1]; exact inf_le_right)
    have hcardM : Nat.card ↥(R1 ⊓ Subgroup.centralizer (P : Set G)) = p ^ 2 := by rw [hk, hk_eq]
    have key : h15.R = R1 ⊓ Subgroup.centralizer (P : Set G) := by
      apply Subgroup.eq_of_le_of_card_ge hRle
      rw [hcardM, hcardR]
    exact key.symm
  -- ## The centre `Z(R₁) ≤ R₁ ⊓ C_G(P) = R`
  have hZg_le_CGP : (R1 ⊓ Subgroup.centralizer (R1 : Set G)) ≤
      Subgroup.centralizer (P : Set G) := by
    intro x hx
    rw [Subgroup.mem_inf] at hx
    rw [Subgroup.mem_centralizer_iff] at hx ⊢
    intro q hq
    exact hx.2 q (hP_le_R1 hq)
  have hZg_le_R : (R1 ⊓ Subgroup.centralizer (R1 : Set G)) ≤ h15.R :=
    (le_inf inf_le_left hZg_le_CGP).trans (le_of_eq hRinfCG)
  -- ## `|Z(R₁)| = p`
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hR1ne : R1 ≠ ⊥ := by
    intro hbot
    have hPbot : P = ⊥ := le_bot_iff.mp (hP_le_R1.trans (le_of_eq hbot))
    have h1 : 1 < Nat.card ↥P := by rw [show Nat.card ↥P = p from hp.symm]; exact hp_prime.one_lt
    rw [hPbot, Subgroup.card_bot] at h1
    exact lt_irrefl 1 h1
  have hR1nt : Nontrivial ↥R1 := (Subgroup.nontrivial_iff_ne_bot R1).mpr hR1ne
  haveI := hR1nt
  have hR1p : IsPGroup p ↥R1 := IsPGroup.of_card (n := 3) hR1c
  have hcenter_ne_bot : Subgroup.center ↥R1 ≠ ⊥ :=
    (Subgroup.nontrivial_iff_ne_bot _).mp
      (IsPGroup.center_nontrivial hR1p)
  have hZg_ne_bot : (R1 ⊓ Subgroup.centralizer (R1 : Set G)) ≠ ⊥ := by
    intro hbot
    apply hcenter_ne_bot
    rw [← center_subgroupOf_inf_centralizer R1, hbot, Subgroup.bot_subgroupOf]
  have hZg_gt1 : 1 < Nat.card ↥(R1 ⊓ Subgroup.centralizer (R1 : Set G)) :=
    (Subgroup.one_lt_card_iff_ne_bot _).mpr hZg_ne_bot
  have hZg_dvd : Nat.card ↥(R1 ⊓ Subgroup.centralizer (R1 : Set G)) ∣ p ^ 2 := by
    rw [← hcardR]; exact Subgroup.card_dvd_of_le hZg_le_R
  have hZg_card : Nat.card ↥(R1 ⊓ Subgroup.centralizer (R1 : Set G)) = p := by
    obtain ⟨k, hk_le, hk⟩ := (Nat.dvd_prime_pow hp_prime).mp hZg_dvd
    have hk_ge : 1 ≤ k := by
      by_contra h
      have hk0 : k = 0 := by omega
      rw [hk, hk0, pow_zero] at hZg_gt1
      exact lt_irrefl 1 hZg_gt1
    rcases (by omega : k = 1 ∨ k = 2) with hk1 | hk2
    · rw [hk, hk1, pow_one]
    · exfalso
      have hcardZg : Nat.card ↥(R1 ⊓ Subgroup.centralizer (R1 : Set G)) = p ^ 2 := by rw [hk, hk2]
      have hZg_eq_R : R1 ⊓ Subgroup.centralizer (R1 : Set G) = h15.R := by
        apply Subgroup.eq_of_le_of_card_ge hZg_le_R
        rw [hcardZg, hcardR]
      apply hnotle
      have hRleC : h15.R ≤ Subgroup.centralizer (R1 : Set G) :=
        (le_of_eq hZg_eq_R.symm).trans inf_le_right
      intro x hxR1
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact ((Subgroup.mem_centralizer_iff.mp (hRleC (hP_le_R hq))) x hxR1).symm
  have hZg_cardP : Nat.card ↥(R1 ⊓ Subgroup.centralizer (R1 : Set G)) = Nat.card P :=
    hZg_card.trans hp
  -- ## `Z(R₁) ≠ P`
  have hZg_ne_P : (R1 ⊓ Subgroup.centralizer (R1 : Set G)) ≠ P := by
    intro hZg_eq_P
    apply hnotle
    have hPleC : P ≤ Subgroup.centralizer (R1 : Set G) := by
      rw [← hZg_eq_P]; exact inf_le_right
    intro x hxR1
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact ((Subgroup.mem_centralizer_iff.mp (hPleC hq)) x hxR1).symm
  -- ## `C_Q(P)` normalises `R₁`
  have hCQ_le_NR1 : CQ Q P ≤ Subgroup.normalizer (R1 : Set G) :=
    (inf_le_right.trans h15.hRn).trans hR1n
  -- ## `Z(R₁) = T` by the sharp transitivity `h11.reg`
  have hZg_eq_T : (R1 ⊓ Subgroup.centralizer (R1 : Set G)) = T := by
    by_contra hZT
    have hZg_notle_T : ¬ (R1 ⊓ Subgroup.centralizer (R1 : Set G)) ≤ T := by
      intro hle
      exact hZT (Subgroup.eq_of_le_of_card_ge hle (by rw [hZg_card, hcardT, ← hp]))
    obtain ⟨y0, -, huniq⟩ := h11.reg _ _ hZg_le_R hZg_le_R hZg_cardP hZg_cardP
      hZg_notle_T hZg_notle_T hZg_ne_P hZg_ne_P
    -- a nontrivial `y1 ∈ C_Q(P)`
    have hCQ_ne_bot : CQ Q P ≠ ⊥ := by
      intro hbot
      have h : p - 1 = 1 := by
        have hc := hcardCQ
        rw [hbot, Subgroup.card_bot] at hc
        exact hc.symm
      omega
    obtain ⟨y1, hy1ne⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hCQ_ne_bot
    have hy1map : (R1 ⊓ Subgroup.centralizer (R1 : Set G)).map
        (MulAut.conj ((y1 : ↥(CQ Q P)) : G)).toMonoidHom
        = R1 ⊓ Subgroup.centralizer (R1 : Set G) :=
      map_conj_inf_centralizer_eq R1 (hCQ_le_NR1 y1.2)
    have h1map : (R1 ⊓ Subgroup.centralizer (R1 : Set G)).map
        (MulAut.conj (((1 : ↥(CQ Q P)) : G))).toMonoidHom
        = R1 ⊓ Subgroup.centralizer (R1 : Set G) := by
      rw [show ((1 : ↥(CQ Q P)) : G) = 1 from rfl]
      rw [show MulAut.conj (1 : G) = 1 from map_one MulAut.conj]
      convert Subgroup.map_id _ using 1
      ext z
      rfl
    have hy1_eq_one : y1 = 1 := (huniq y1 hy1map).trans (huniq 1 h1map).symm
    exact hy1ne hy1_eq_one
  exact ⟨by rw [← center_subgroupOf_inf_centralizer R1, hZg_eq_T], hcardT⟩

end Work.ThmF.ChV3.Prove
