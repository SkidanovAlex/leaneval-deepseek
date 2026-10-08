import Mathlib
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2b
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThmF.Bender.cardKsetEqInv
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3Sub.OddResidual
import Submission.Work.ThreePoints.P3Sub.Helpers
import Submission.Work.ThreePoints.P3Sub.App2Seven
import Submission.Work.ThreePoints.P3Sub.prop1a_fixes_three
import Submission.Work.ThreePoints.P3Sub.prop2c
import Submission.Work.ThreePoints.P3Sub.part1_b
import Submission.Work.ThreePoints.P3Sub.app3_1
import Submission.Work.ThreePoints.P3Sub.p3F_subgroupOf_normalizer_normal
import Submission.Work.ThreePoints.P3Sub.ch1s4_prop1
import Submission.Work.ThreePoints.P3Sub.p3pkg_of_subnormal
import Submission.Work.DoubleTransitivity.Action
import Submission.Work.DoubleTransitivity.App1.app1_1b

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.ThreePoints

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## 0. Monotonicity of `2`-transitivity in the acting subgroup -/

theorem IsTwoTransitiveOnSub.mono {E : Type} [MulAction G E] {A B : Subgroup G} {S : Set E}
    (h : Work.DoubleTransitivity.IsTwoTransitiveOnSub A S) (hAB : A ≤ B) :
    Work.DoubleTransitivity.IsTwoTransitiveOnSub B S :=
  fun c hc d hd hcd c' hc' d' hd' hcd' =>
    let ⟨g, hg, h1, h2⟩ := h c hc d hd hcd c' hc' d' hd' hcd'
    ⟨g, hAB hg, h1, h2⟩

/-! ## 1. Peterfalvi I Ch. II §4, Lemma 1 (the inclusion used below) -/

/-- **Peterfalvi I Ch. II §4, Lemma 1** (p. 169): `N_K(X) ⊆ ⟨Inv C_G(X)⟩`.

Every involution of `N_G(X)` centralises `X`: all involutions of `N_G(X)` are conjugate in
`N_G(X)` (Ch. I §2 Prop. 1 (b), applied to `N_G(X)` and its strongly embedded subgroup
`N_H(X)`), and `t ∈ C_G(X) ≤ N_G(X)` is one of them. -/
theorem nk_le_closure {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX : X ≤ centD H t)
    (hev : Even (Nat.card (Subgroup.normalizer (X : Set G) ⊓ H : Subgroup G))) :
    (invertedBy (twoPoint H t) t ∩ (Subgroup.normalizer (X : Set G) : Set G)) ⊆
      (Subgroup.closure (involutions (Subgroup.centralizer (X : Set G) : Set G)) : Set G) := by
  intro k hk
  obtain ⟨hkK, hkN⟩ := hk
  have hkH : k ∈ H := (mem_twoPoint.mp hkK.1).1
  have hkinv : t * k * t⁻¹ = k⁻¹ := hkK.2
  -- `t ∈ C_G(X) ⊆ N_G(X)`
  have htC : t ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp (p3sub_centralizer_of_le_centD hX hx)
  have htN : t ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.centralizer_le_normalizer _ htC
  have htinv : t⁻¹ = t := by
    have h2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
    exact inv_eq_of_mul_eq_one_right h2
  have htkN : t * k ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normalizer (X : Set G)).mul_mem htN hkN
  -- `t * k` is an involution
  have htk2 : (t * k) * (t * k) = 1 := by
    have h1 : t * k * t = k⁻¹ := by simpa [htinv] using hkinv
    calc (t * k) * (t * k) = ((t * k) * t) * k := by group
      _ = k⁻¹ * k := by rw [h1]
      _ = 1 := inv_mul_cancel k
  have htk_ne : t * k ≠ 1 := by
    intro hcon
    apply htH
    have h1 : t = k⁻¹ := by
      have h2 : t * k * k⁻¹ = k⁻¹ := by rw [hcon, one_mul]
      simpa using h2
    rw [h1]
    exact H.inv_mem hkH
  have htk2' : orderOf (t * k) = 2 := by
    have hdvd : orderOf (t * k) ∣ 2 :=
      orderOf_dvd_of_pow_eq_one (by rw [pow_two]; exact htk2)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) htk_ne
    · exact h1
  -- `N_H(X) = N_G(X) ∩ H` is strongly embedded in `N_G(X)`
  have hSE : IsStronglyEmbedded
      ((Subgroup.normalizer (X : Set G) ⊓ H).subgroupOf (Subgroup.normalizer (X : Set G))) := by
    refine IsStronglyEmbedded.subgroupOf_inf hH ?_ hev
    intro hcon
    rw [Subgroup.subgroupOf_eq_top] at hcon
    exact htH (Subgroup.mem_inf.mp (hcon htN)).2
  -- every involution of `N_G(X)` is conjugate to `t` in `N_G(X)`
  have hconj : IsConj (⟨t, htN⟩ : ↥(Subgroup.normalizer (X : Set G)))
      (⟨t * k, htkN⟩ : ↥(Subgroup.normalizer (X : Set G))) := by
    refine involutions_conj_of_stronglyEmbedded hSE ?_ ?_
    · have hco : orderOf (⟨t, htN⟩ : ↥(Subgroup.normalizer (X : Set G))) = orderOf t :=
        (Subgroup.orderOf_coe ⟨t, htN⟩).symm
      rw [hco, ht]
    · have hco : orderOf (⟨t * k, htkN⟩ : ↥(Subgroup.normalizer (X : Set G))) =
          orderOf (t * k) :=
        (Subgroup.orderOf_coe ⟨t * k, htkN⟩).symm
      rw [hco, htk2']
  obtain ⟨c, hc⟩ := isConj_iff.mp hconj
  -- hence `t * k` centralises `X`
  have htkC : t * k ∈ Subgroup.centralizer (X : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hcval : (c : G) * t * (c : G)⁻¹ = t * k := congrArg Subtype.val hc
    have hcN : (c : G) ∈ Subgroup.normalizer (X : Set G) := c.2
    have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp
      (p3sub_centralizer_of_le_centD hX hx)
    have hcinv : (c : G)⁻¹ ∈ Subgroup.normalizer (X : Set G) :=
      (Subgroup.normalizer (X : Set G)).inv_mem hcN
    have hxc : (c : G)⁻¹ * x * (c : G) ∈ X := by
      simpa using ((Subgroup.mem_set_normalizer_iff.mp hcinv) x).mp hx
    have hcom : ((c : G)⁻¹ * x * (c : G)) * t = t * ((c : G)⁻¹ * x * (c : G)) :=
      Subgroup.mem_centralizer_iff.mp htC _ hxc
    rw [← hcval]
    have hx1 : x = (c : G) * ((c : G)⁻¹ * x * (c : G)) * (c : G)⁻¹ := by group
    rw [hx1]
    have hgoals : (c : G) * ((c : G)⁻¹ * x * (c : G)) * (c : G)⁻¹ *
          ((c : G) * t * (c : G)⁻¹)
        = (c : G) * (((c : G)⁻¹ * x * (c : G)) * t) * (c : G)⁻¹ := by group
    rw [hgoals, hcom]
    group
  have htkInv : t * k ∈ (involutions (Subgroup.centralizer (X : Set G) : Set G)) :=
    ⟨htkC, htk2'⟩
  have htInv : t ∈ (involutions (Subgroup.centralizer (X : Set G) : Set G)) := ⟨htC, ht⟩
  have hk_eq : k = t⁻¹ * (t * k) := by group
  rw [hk_eq]
  exact (Subgroup.closure _).mul_mem ((Subgroup.closure _).inv_mem
    (Subgroup.subset_closure htInv)) (Subgroup.subset_closure htkInv)

/-! ## 2. Auxiliaries on the action on `Ω` -/

/-- An element of `N_G(X)` preserves `Ω_X`. -/
theorem smul_mem_fixedPts_of_mem_normalizer {H X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) {ω : G ⧸ H} (hω : ω ∈ fixedPts H X) :
    g • ω ∈ fixedPts H X := by
  rw [mem_fixedPts_iff_le_stabilizer] at hω ⊢
  intro x hx
  rw [MulAction.mem_stabilizer_iff]
  have hgx : g⁻¹ * x * g ∈ X := by
    have hmap : X.map (MulAut.conj g⁻¹).toMonoidHom = X :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.normalizer (X : Set G)).inv_mem hg)
    have hmem : MulAut.conj g⁻¹ x ∈ X := by
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hx
    simpa [MulAut.conj_apply] using hmem
  have hfix : (g⁻¹ * x * g) • ω = ω := by
    have h := hω hgx
    rwa [MulAction.mem_stabilizer_iff] at h
  calc x • (g • ω) = (x * g) • ω := by rw [smul_smul]
    _ = (g * (g⁻¹ * x * g)) • ω := by rw [show x * g = g * (g⁻¹ * x * g) from by group]
    _ = g • ((g⁻¹ * x * g) • ω) := by rw [smul_smul]
    _ = g • ω := by rw [hfix]

/-- The stabiliser of the point `H` of `Ω`. -/
theorem stabilizer_pt (H : Subgroup G) :
    MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) = H := by
  rw [stabilizer_mk H 1, conj_one]

/-- The points `H` and `H^t` of `Ω` are distinct when `t ∉ H`. -/
theorem mk_one_ne_mk_t {H : Subgroup G} {t : G} (htH : t ∉ H) :
    (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ QuotientGroup.mk t := by
  intro hcon
  rw [QuotientGroup.eq] at hcon
  exact htH (by simpa using hcon)

/-- `|D| = |H ⊓ H^t|` is odd. -/
theorem odd_card_twoPoint {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G} (htH : t ∉ H) :
    Odd (Nat.card (twoPoint H t : Subgroup G)) := by
  have hne : conj (1 : G) H ≠ conj t H := by
    intro hcon
    have hHconj : conj t H = H := by rw [← hcon, conj_one]
    have htN : t ∈ Subgroup.normalizer (H : Set G) :=
      (Work.DoubleTransitivity.conj_eq_self_iff_mem_normalizer t H).mp hHconj
    rw [IsStronglyEmbedded.normalizer_eq hH] at htN
    exact htH htN
  simpa [conj_one, twoPoint_eq] using card_inf_conj_odd hH hne

/-! ## 3. Prop. 3 (a): the equality `N_G(X) = F · N_V(X)` -/

/-- **Prop. 3 (a), first step.**  If `F = O^{2'}(C_G(X))` acts `2`-transitively on `Ω_X`, then
`N_G(X) = F · N_D(X)`: for `g ∈ N_G(X)` there is `f ∈ F` with `f g` fixing both `H` and `H^t`,
i.e. `f g ∈ D`. -/
theorem normalizer_eq_sup_twoPoint {H X : Subgroup G} {t : G} (htH : t ∉ H)
    (hX : X ≤ centD H t)
    (h2t : Work.DoubleTransitivity.IsTwoTransitiveOnSub (p3F X) (fixedPts H X)) :
    Subgroup.normalizer (X : Set G) =
      p3F X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) := by
  refine le_antisymm ?_ (sup_le (p3F_le_normalizer X) inf_le_right)
  intro g hg
  have ha : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ fixedPts H X := pt_mem_fixedPts_of_le_centD hX
  have hb : (QuotientGroup.mk t : G ⧸ H) ∈ fixedPts H X := mk_t_mem_fixedPts_of_le_centD hX
  have hga := smul_mem_fixedPts_of_mem_normalizer hg ha
  have hgb := smul_mem_fixedPts_of_mem_normalizer hg hb
  have hne : g • (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ g • (QuotientGroup.mk t : G ⧸ H) := by
    intro hcon
    exact mk_one_ne_mk_t htH (smul_left_cancel g hcon)
  obtain ⟨f, hf, hf1, hf2⟩ :=
    h2t _ hga _ hgb hne _ ha _ hb (mk_one_ne_mk_t htH)
  have hfg1 : f * g ∈ MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) := by
    rw [MulAction.mem_stabilizer_iff, mul_smul]
    exact hf1
  have hfg2 : f * g ∈ MulAction.stabilizer G (QuotientGroup.mk t : G ⧸ H) := by
    rw [MulAction.mem_stabilizer_iff, mul_smul]
    exact hf2
  have hfgH : f * g ∈ H := by
    rw [stabilizer_pt] at hfg1
    exact hfg1
  have hfgD : f * g ∈ twoPoint H t := by
    rw [twoPoint_eq, Subgroup.mem_inf]
    exact ⟨hfgH, by rwa [stabilizer_mk] at hfg2⟩
  have hfgN : f * g ∈ Subgroup.normalizer (X : Set G) :=
    (Subgroup.normalizer (X : Set G)).mul_mem (p3F_le_normalizer X hf) hg
  have hg_eq : g = f⁻¹ * (f * g) := by group
  rw [hg_eq]
  exact (p3F X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G))).mul_mem
    ((p3F X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G))).inv_mem
      (Subgroup.mem_sup_left hf))
    (Subgroup.mem_sup_right (Subgroup.mem_inf.mpr ⟨hfgD, hfgN⟩))

/-! ## 4. The case `N_K(X) ≠ 1` (source part 1) -/

/-- The group `p3F X ⊓ H` is strongly embedded in `p3F X`: an involution of `H ⊓ C_G(X)` (which
exists by Prop. 1 (a)) lies in `p3F X`, so the intersection has even order, and `t ∈ p3F X ∖ H`
makes it proper. -/
theorem p3sub_stronglyEmbedded_p3F_inf_H {H X : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) (hX : X ≤ centD H t)
    (heven : ∀ M : Subgroup G, (∃ g : G, M = conj g H) → X ≤ M →
      Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G))) :
    IsStronglyEmbedded ((p3F X ⊓ H).subgroupOf (p3F X)) := by
  obtain ⟨u, hu, hu2⟩ := exists_orderOf_two_of_even_card (heven H ⟨1, (conj_one H).symm⟩
    (le_of_le_centD hX).1)
  have huF : u ∈ p3F X := mem_p3F_of_involution (Subgroup.mem_inf.mp hu).2 hu2
  refine IsStronglyEmbedded.subgroupOf_inf hH ?_ (even_card_of_mem_involution ?_ hu2)
  · intro hcon
    rw [Subgroup.subgroupOf_eq_top] at hcon
    exact htH (Subgroup.mem_inf.mp (hcon (t_mem_p3F hX ht))).2
  · exact Subgroup.mem_inf.mpr ⟨huF, (Subgroup.mem_inf.mp hu).1⟩

theorem p3pkg_of_hasNonTrivialNK
    (hFT : FeitThompsonProp) (hC : ThmCProp) (hA : ThmAProp) (hZJ : GlaubermanZJProp)
    (hBrSz : BrauerSuzukiProp) (hMod : ModelFactsProp) (hS : Situation G)
    {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    {X : Subgroup G} (hX : X ≤ centD H t) (hXne : X ≠ ⊥) (hNX : HasNonTrivialNK H t X) :
    P3Pkg H t X := by
  have hX3 : 3 ≤ (fixedPts H X).ncard := three_le_ncard_fixedPts_of_le_centD hH ht htH hX
  have heven : ∀ M : Subgroup G, (∃ g : G, M = conj g H) → X ≤ M →
      Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
    fun M hM hXM => Work.ThreePoints.P3Sub.prop1a_fixes_three hFT hC hA hBrSz hS hH hX3 hM hXM
  have hptX : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ fixedPts H X :=
    pt_mem_fixedPts_of_le_centD hX
  have htF : t ∈ p3F X := t_mem_p3F hX ht
  have hInv : involutions (Subgroup.centralizer (X : Set G) : Set G) ⊆ p3F X :=
    fun u hu => mem_p3F_of_involution hu.1 hu.2
  -- `|N_G(X) ⊓ H|` is even, so Lemma 1 applies
  have hev_N : Even (Nat.card (Subgroup.normalizer (X : Set G) ⊓ H : Subgroup G)) := by
    obtain ⟨u, hu, hu2⟩ := exists_orderOf_two_of_even_card
      (heven H ⟨1, (conj_one H).symm⟩ (le_of_le_centD hX).1)
    exact even_card_of_mem_involution
      (Subgroup.mem_inf.mpr ⟨Subgroup.centralizer_le_normalizer _ (Subgroup.mem_inf.mp hu).2,
        (Subgroup.mem_inf.mp hu).1⟩) hu2
  have hNk : (invertedBy (twoPoint H t) t ∩ (Subgroup.normalizer (X : Set G) : Set G)) ⊆
      (p3F X : Set G) :=
    fun y hy => (Subgroup.closure_le (p3F X)).mpr hInv (nk_le_closure hH ht htH hX hev_N hy)
  -- the element `z ∈ K ∖ {1}` of prime order `p` normalising `X`
  obtain ⟨k, hkK, hk1, hkN⟩ := (show HasNonTrivialNK H t X from hNX)
  have hkF : k ∈ p3F X := hNk ⟨hkK, hkN⟩
  have hkpos : 0 < orderOf k := Nat.pos_of_dvd_of_pos (orderOf_dvd_natCard k) Nat.card_pos
  have hkodd : Odd (orderOf k) :=
    Work.ThreePoints.Odd.of_dvd (Subgroup.orderOf_dvd_natCard (twoPoint H t) hkK.1)
      (odd_card_twoPoint hH htH)
  have hkne1 : orderOf k ≠ 1 := fun h => hk1 (orderOf_eq_one_iff.mp h)
  obtain ⟨p, hpprime, hpdvd⟩ := Nat.exists_prime_and_dvd hkne1
  have hp2 : p ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.mpr hkodd) (even_iff_two_dvd.mpr hpdvd)
  have hnp : orderOf k / p ≠ 0 :=
    (Nat.div_pos (Nat.le_of_dvd hkpos hpdvd) hpprime.pos).ne'
  set z : G := k ^ (orderOf k / p) with hzdef
  have hzord : orderOf z = p := by
    have hdiv : orderOf k / p ∣ orderOf k := ⟨p, by
      obtain ⟨c, hc⟩ := hpdvd
      rw [hc, Nat.mul_div_right c hpprime.pos, mul_comm]⟩
    rw [hzdef, orderOf_pow_of_dvd hnp hdiv]
    obtain ⟨c, hc⟩ := hpdvd
    have hcpos : 0 < c := Nat.pos_of_ne_zero (fun h0 => by
      rw [h0, mul_zero] at hc; exact hkpos.ne' hc)
    rw [hc, Nat.mul_div_right c hpprime.pos, Nat.mul_div_left p hcpos]
  have hzK : z ∈ invertedBy (twoPoint H t) t := by
    refine ⟨?_, ?_⟩
    · exact (twoPoint H t).pow_mem hkK.1 _
    · have hconjk : MulAut.conj t k = k⁻¹ := by
        rw [MulAut.conj_apply]
        exact hkK.2
      show t * z * t⁻¹ = z⁻¹
      rw [show t * z * t⁻¹ = MulAut.conj t z from rfl, hzdef, map_pow, hconjk, inv_pow]
  have hz1 : z ≠ 1 := by
    intro h0
    have : orderOf z = 1 := by rw [h0]; exact orderOf_one
    rw [hzord] at this
    exact hpprime.ne_one this
  have hzF : z ∈ p3F X := Subgroup.pow_mem _ hkF _
  have hPp : IsPGroup p (Subgroup.zpowers z) := by
    haveI : Fact p.Prime := ⟨hpprime⟩
    rw [IsPGroup.iff_card]
    exact ⟨1, by rw [Nat.card_zpowers, hzord, pow_one]⟩
  have hfix : (fixedPts H (Subgroup.zpowers z) ∩ fixedPts H X).ncard = 2 := by
    have hz2pts : (fixedPts H (Subgroup.zpowers z)).ncard = 2 :=
      Work.ThreePoints.P3Sub.prop2c hFT hC hA hBrSz hS hH ht htH hzK hz1
    have hmem1 : (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers z) := by
      rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, conj_one, Subgroup.zpowers_le]
      exact (mem_twoPoint.mp hzK.1).1
    have hmemt : (QuotientGroup.mk t : G ⧸ H) ∈ fixedPts H (Subgroup.zpowers z) := by
      rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, Subgroup.zpowers_le]
      exact mem_conj_iff.mpr (mem_twoPoint.mp hzK.1).2
    have hne : (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ (QuotientGroup.mk t : G ⧸ H) :=
      mk_one_ne_mk_t htH
    have hpair : ({(QuotientGroup.mk (1 : G) : G ⧸ H), (QuotientGroup.mk t : G ⧸ H)} :
        Set (G ⧸ H)).ncard = 2 := Set.ncard_pair hne
    have hset : fixedPts H (Subgroup.zpowers z) =
        {(QuotientGroup.mk (1 : G) : G ⧸ H), (QuotientGroup.mk t : G ⧸ H)} := by
      have h1 : ({(QuotientGroup.mk (1 : G) : G ⧸ H), (QuotientGroup.mk t : G ⧸ H)} :
          Set (G ⧸ H)) ⊆ fixedPts H (Subgroup.zpowers z) := by
        intro ω hω
        have hω' : ω = (QuotientGroup.mk (1 : G) : G ⧸ H) ∨
            ω = (QuotientGroup.mk t : G ⧸ H) := by simpa using hω
        rcases hω' with h | h
        · rw [h]; exact hmem1
        · rw [h]; exact hmemt
      have h2 : (fixedPts H (Subgroup.zpowers z)).ncard ≤
          ({(QuotientGroup.mk (1 : G) : G ⧸ H), (QuotientGroup.mk t : G ⧸ H)} :
            Set (G ⧸ H)).ncard := by rw [hpair, hz2pts]
      exact (Set.eq_of_subset_of_ncard_le h1 h2).symm
    have hsub : fixedPts H (Subgroup.zpowers z) ⊆ fixedPts H X := by
      intro ω hω
      have hω' : ω ∈ ({(QuotientGroup.mk (1 : G) : G ⧸ H), (QuotientGroup.mk t : G ⧸ H)} :
          Set (G ⧸ H)) := hset ▸ hω
      rcases hω' with h | h
      · rw [h]; exact hptX
      · rw [h]; exact mk_t_mem_fixedPts_of_le_centD hX
    rw [Set.inter_eq_left.mpr hsub]
    exact hz2pts
  -- Ch. I §4 Prop. 1 gives the `2`-transitivity of `p3F X` on `Ω_X`
  have h2tF : Work.DoubleTransitivity.IsTwoTransitiveOnSub (p3F X) (fixedPts H X) :=
    Work.ThreePoints.P3Sub.ch1s4_prop1 hH hBrSz (le_of_le_centD hX).1 (p3F_le_normalizer X) hInv heven
      (p3sub_stronglyEmbedded_p3F_inf_H hH ht htH hX heven) hpprime hp2
      (Subgroup.zpowers_le.mpr hzF) hPp hfix
  have h2tN : Work.DoubleTransitivity.IsTwoTransitiveOnSub
      (Subgroup.normalizer (X : Set G)) (fixedPts H X) :=
    Work.ThreePoints.IsTwoTransitiveOnSub.mono h2tF (p3F_le_normalizer X)
  -- (a)
  have ha : Subgroup.normalizer (X : Set G) =
      p3F X ⊔ (centD H t ⊓ Subgroup.normalizer (X : Set G)) :=
    calc Subgroup.normalizer (X : Set G)
        = p3F X ⊔ (twoPoint H t ⊓ Subgroup.normalizer (X : Set G)) :=
          normalizer_eq_sup_twoPoint htH hX h2tF
      _ = p3F X ⊔ (centD H t ⊓ Subgroup.normalizer (X : Set G)) :=
          Work.ThreePoints.P3Sub.sup_twoPoint_eq_sup_centD hH ht htH hX hNk
  -- `p3F X` has `2`-rank `≥ 2` (source part 1 (c))
  have hfour : HasFourGroup (p3F X) := by
    by_contra hno
    have hmax : ∀ M : Subgroup G, p3F X ⊓ H ≤ M → M ≤ p3F X →
        M = p3F X ⊓ H ∨ M = p3F X := by
      intro M hHM hMF
      by_cases hM : M = p3F X
      · exact Or.inr hM
      refine Or.inl (le_antisymm ?_ hHM)
      by_contra hnotle
      obtain ⟨m, hmM, hmnot⟩ := Set.not_subset.mp hnotle
      have hmF : m ∈ p3F X := hMF hmM
      have hmN : m ∈ Subgroup.normalizer (X : Set G) := p3F_le_normalizer X hmF
      have hmp : m • (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ QuotientGroup.mk (1 : G) := by
        intro hcon
        apply hmnot
        exact Subgroup.mem_inf.mpr ⟨hmF, by
          have : m ∈ MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) := by
            rw [MulAction.mem_stabilizer_iff]; exact hcon
          rwa [stabilizer_pt] at this⟩
      have hmpt : m • (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ fixedPts H X :=
        smul_mem_fixedPts_of_mem_normalizer hmN hptX
      -- `F ≤ M`, so `M = F`, contradicting `hM`
      have hFM : p3F X ≤ M := by
        intro g hg
        by_cases hgpt : g • (QuotientGroup.mk (1 : G) : G ⧸ H) = QuotientGroup.mk (1 : G)
        · exact hHM (Subgroup.mem_inf.mpr ⟨hg, by
            have : g ∈ MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) := by
              rw [MulAction.mem_stabilizer_iff]; exact hgpt
            rwa [stabilizer_pt] at this⟩)
        · have hgptX : g • (QuotientGroup.mk (1 : G) : G ⧸ H) ∈ fixedPts H X :=
            smul_mem_fixedPts_of_mem_normalizer (p3F_le_normalizer X hg) hptX
          obtain ⟨f, hf, hf1, hf2⟩ := h2tF _ hptX _ hgptX (fun hcon => hgpt hcon.symm)
            _ hptX _ hmpt (fun hcon => hmp hcon.symm)
          have hfH : f ∈ H := by
            have : f ∈ MulAction.stabilizer G (QuotientGroup.mk (1 : G) : G ⧸ H) := by
              rw [MulAction.mem_stabilizer_iff]; exact hf1
            rwa [stabilizer_pt] at this
          have hfM : f ∈ M := hHM (Subgroup.mem_inf.mpr ⟨hf, hfH⟩)
          have hmem : m⁻¹ * (f * g) ∈ p3F X ⊓ H := by
            refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
            · exact (p3F X).mul_mem ((p3F X).inv_mem hmF) ((p3F X).mul_mem hf hg)
            · have : m⁻¹ * (f * g) ∈ MulAction.stabilizer G
                  (QuotientGroup.mk (1 : G) : G ⧸ H) := by
                rw [MulAction.mem_stabilizer_iff, mul_smul,
                  show (f * g) • (QuotientGroup.mk (1 : G) : G ⧸ H) =
                    m • (QuotientGroup.mk (1 : G) : G ⧸ H) from by rw [mul_smul, hf2]]
                exact inv_smul_smul m _
              rwa [stabilizer_pt] at this
          have hfgM : f * g ∈ M := by
            have := M.mul_mem hmM (hHM hmem)
            simpa using this
          have hg_eq : g = f⁻¹ * (f * g) := by group
          rw [hg_eq]
          exact M.mul_mem (M.inv_mem hfM) hfgM
      exact hM (le_antisymm hMF hFM)
    -- App. III (1): `p3F X ⊓ D` fixes the fixed point `ω` of `t`
    obtain ⟨g, hg⟩ := Work.ThreePoints.exists_conj_mem hH ht
    have hω : t • ((g : G) : G ⧸ H) = (g : G ⧸ H) := by
      rw [smul_mk, QuotientGroup.eq]
      have h1 : t⁻¹ ∈ conj g H := (conj g H).inv_mem hg
      have h2 : g⁻¹ * t⁻¹ * g ∈ H := mem_conj_iff.mp h1
      simpa using h2
    have h3fix := Work.ThreePoints.P3Sub.app3_1 hH hBrSz hFT (p3F_le_normalizer X) h2tF
      (p3sub_stronglyEmbedded_p3F_inf_H hH ht htH hX heven) hmax hno ht htF htH hω
    have hzFD : z ∈ p3F X ⊓ twoPoint H t := Subgroup.mem_inf.mpr ⟨hzF, hzK.1⟩
    have hne1ω : (QuotientGroup.mk (1 : G) : G ⧸ H) ≠ (g : G ⧸ H) := by
      intro hcon
      have h1 : t • (QuotientGroup.mk (1 : G) : G ⧸ H) = (QuotientGroup.mk (1 : G) : G ⧸ H) := by
        rw [hcon]; exact hω
      rw [smul_mk, QuotientGroup.eq] at h1
      exact htH (by simpa using h1)
    have hnetω : (QuotientGroup.mk t : G ⧸ H) ≠ (g : G ⧸ H) := by
      intro hcon
      have h1 : t • (QuotientGroup.mk t : G ⧸ H) = (QuotientGroup.mk t : G ⧸ H) := by
        rw [hcon]; exact hω
      rw [smul_mk, QuotientGroup.eq] at h1
      have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
      exact htH (by simpa [ht2] using h1)
    have hsub3 : ({(QuotientGroup.mk (1 : G) : G ⧸ H), (QuotientGroup.mk t : G ⧸ H),
        (g : G ⧸ H)} : Set (G ⧸ H)) ⊆ fixedPts H (Subgroup.zpowers z) := by
      intro ω hω'
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hω'
      rcases hω' with h | h | h
      · rw [h]
        rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, conj_one, Subgroup.zpowers_le]
        exact (mem_twoPoint.mp hzK.1).1
      · rw [h]
        rw [mem_fixedPts_iff_le_stabilizer, stabilizer_mk, Subgroup.zpowers_le]
        exact mem_conj_iff.mpr (mem_twoPoint.mp hzK.1).2
      · rw [h]
        rw [mem_fixedPts_iff_le_stabilizer]
        exact Subgroup.zpowers_le.mpr (h3fix hzFD)
    have h3 : 3 ≤ (fixedPts H (Subgroup.zpowers z)).ncard := by
      have hcard : ({(QuotientGroup.mk (1 : G) : G ⧸ H), (QuotientGroup.mk t : G ⧸ H),
          (g : G ⧸ H)} : Set (G ⧸ H)).ncard = 3 := by
        rw [Set.ncard_insert_of_notMem (by
              simp only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
              exact ⟨mk_one_ne_mk_t htH, hne1ω⟩),
          Set.ncard_insert_of_notMem (by
              simp only [Set.mem_singleton_iff]; exact hnetω),
          Set.ncard_singleton]
      calc 3 = _ := hcard.symm
        _ ≤ (fixedPts H (Subgroup.zpowers z)).ncard := Set.ncard_le_ncard hsub3
    have h2 := Work.ThreePoints.P3Sub.prop2c hFT hC hA hBrSz hS hH ht htH hzK hz1
    omega
  exact ⟨⟨ha, Work.ThreePoints.P3Sub.part1_b hFT hC hA hZJ hBrSz hMod hS hH ht htH hX hXne
      hNX hfour h2tF⟩, h2tN⟩

/-! ## 5. The induction on `|X|` -/

theorem p3pkg
    (hFT : FeitThompsonProp) (hC : ThmCProp) (hA : ThmAProp) (hZJ : GlaubermanZJProp)
    (hBrSz : BrauerSuzukiProp) (hMod : ModelFactsProp) (hS : Situation G)
    {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2) (htH : t ∉ H) :
    ∀ X : Subgroup G, X ≤ centD H t →
      (∃ Y : Subgroup G, Y ≠ ⊥ ∧ IsSubnormalIn Y X ∧ HasNonTrivialNK H t Y) →
      P3Pkg H t X := by
  intro X
  suffices ∀ n, ∀ X : Subgroup G, Nat.card ↥X = n → X ≤ centD H t →
      (∃ Y : Subgroup G, Y ≠ ⊥ ∧ IsSubnormalIn Y X ∧ HasNonTrivialNK H t Y) →
      P3Pkg H t X from
    fun hX hY => this _ X rfl hX hY
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro X hXn hX hY
    obtain ⟨Y, hYne, hsub, hNK⟩ := hY
    by_cases hYX : Y = X
    · subst hYX
      exact p3pkg_of_hasNonTrivialNK hFT hC hA hZJ hBrSz hMod hS hH ht htH hX
        (by rintro rfl; exact hYne (le_bot_iff.mp (IsSubnormalIn.le hsub))) hNK
    · refine Work.ThreePoints.P3Sub.p3pkg_of_subnormal hFT hC hA hZJ hBrSz hMod hS hH ht htH hX
        (fun X₀ hlt hX₀ hY₀ => ih (Nat.card ↥X₀) ?_ X₀ rfl hX₀ hY₀) hYne hsub hYX hNK
      rw [← hXn]; exact hlt

/-- Peterfalvi I Ch. II §4 Prop. 3 (a),(b) with a subnormal `Y` (p. 169–171; the blueprint's
`ChIIFourP3SubnormalProp`, added by the lead 2026-10-03): if `X ≤ V = C_D(t)`, `Y ≠ 1` is subnormal
in `X` and `N_K(Y) ≠ 1`, then with `F = O^{2'}(C_G(X))` one has `N_G(X) = F·N_V(X)` and
`N_H(X) = S ⋊ N_D(X)` with `S` a Sylow 2-subgroup of `F ⊓ H`.
Proved by the source's part 1) (the case `N_K(X) ≠ 1`) together with the induction on `|X|` of
part 2) driven by the subnormal `Y` (pp. 170–171). -/
theorem chIIFourP3Subnormal
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hMod : Submission.Blueprint.ModelFactsProp) :
    Submission.Blueprint.ChIIFourP3SubnormalProp := by
  intro G _ _ hSit H hH t ht htH X Y hX hYne hsub hNK
  have h := p3pkg hFT hC hA hZJ hBrSz hMod hSit hH ht htH X hX ⟨Y, hYne, hsub, hNK⟩
  exact ⟨h.1.1, h.1.2⟩



end Work.ThreePoints
