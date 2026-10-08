import Mathlib
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3NeBot.Basic
import Submission.Work.ThreePoints.P3NeBot.p3_lemma1
import Submission.Work.ThreePoints.P3NeBot.p3_twoTransitive
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Basic
import Submission.Work.ThreePoints.involutions_conj_of_stronglyEmbedded
import Submission.Work.ThreePoints.isStronglyEmbedded_map_quotient
import Submission.Work.ThreePoints.oddCore_le_of_stronglyEmbedded
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup
import Submission.Work.ThreePoints.even_card_normalizer_of_maximal_p_subgroup_nofour
import Submission.Work.DoubleTransitivity.Sec4.prop2
import Submission.Work.ThreePoints.stronglyEmbedded_subgroupOf_inf_conj
import Submission.Work.ThreePoints.Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz
import Submission.Work.ThreePoints.p3cd_oddCore_eq_center
import Submission.Work.ThreePoints.p3cd_hasFourGroup
import Submission.Work.ThreePoints.p3cd_transitive
import Submission.Work.ThreePoints.p3cd_gen_by_involutions
import Submission.Work.ThreePoints.involutions_commute_of_below
import Submission.Work.Reductions.OddResidual
import Submission.Work.Endgame.Defs

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1600000

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

/-!
# `Work.ThreePoints.p3cd_torus_cyclic`

Peterfalvi I Ch. II §4 Prop. 3 (d): with `X ≠ ⊥`, `X ≤ V = C_D(t)` (`D = H ⊓ H^t`, `H` strongly
embedded, `t ∉ H` an involution) and `N_K(X) ≠ 1` (`K = J(D,t) = invertedBy D t`), the group
`F ∩ K` (`F = O^{2'}(C_G(X))`) is a cyclic subgroup of `G`.

The strategy is the source's: `F/O_{2'}(F)` is one of the models, so `F ∩ K` sits inside the
preimage of the cyclic torus `K_Y = J(D_Y,t_Y)` of `F/O_{2'}(F)`; that preimage is commutative (a
cyclic quotient of a central kernel), and its `t`-inverted part intersected with `D` is exactly
`F ∩ K`.
-/

variable {G : Type} [Group G] [Finite G]

/-! ## 1. Ch. I §4 Prop. 2 -/

/-- **Ch. I §4 Prop. 2** (Peterfalvi, p. 156), in the form needed here: `K ≤ F` strongly embedded,
`p ≠ 2` a prime and `Q ≤ K` a `p`-subgroup maximal among the `p`-subgroups of `K` with at least
three fixed points.  Then `|N_K(Q)|` is even.

This is `Work.DoubleTransitivity.Sec4.prop2` (Ch. I §4 Prop. 1 (a),(b) and Lemma 2, with the
`𝓡_p`-analysis), transported along `|N_K(Q)| = |N_F(Q) ⊓ K|`.

Renamed from `s4prop2_brsz` on 2026-10-08 (audit D3 b): the name `s4prop2_brsz` is also declared in
`ThreePoints/sec4_prop2b.lean`, and the two cannot be imported into one module.  This is the
`ThmAProp`-carrying wrapper; the `sec4_prop2b` version keeps the name. -/
theorem s4prop2_brsz_of_thmA (hA : Submission.Blueprint.ThmAProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) :
    ∀ (F : Type) [Group F] [Finite F] {K : Subgroup F},
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded K →
      ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ Q : Subgroup F, Q ≤ K → IsPGroup p Q →
        3 ≤ (Submission.Blueprint.fixedPts K Q).ncard →
        (∀ R : Subgroup F, Q ≤ R → R ≤ K → IsPGroup p R →
          3 ≤ (Submission.Blueprint.fixedPts K R).ncard → R = Q) →
        Even (Nat.card (Subgroup.normalizer (Q.subgroupOf K : Set K) : Subgroup K)) := by
  intro F _ _ K hK p hp hp2 Q hQK hQp hQ3 hQmax
  have hmaxIn : Work.DoubleTransitivity.MaxFixesThreeIn p K Q :=
    ⟨hQp, hQK, hQ3, fun R hRp hRK hR3 hQR => (hQmax R hQR hRK hRp hR3).le⟩
  have h := (Work.DoubleTransitivity.Sec4.prop2 hBrSz hK hp hp2 hmaxIn).2
  rwa [card_normalizer_subgroupOf_eq_card_inf hQK, inf_comm]

/-! ## 2. Ch. II §4 Prop. 1 (a)–(b) and strong embeddedness of `F ⊓ M` in `F` -/

/-- **Ch. II §4 Prop. 1 (a)** at a fixed point `M = H^g ⊇ X`: `|M ⊓ C_G(X)|` is even. -/
theorem even_card_centralizer_brsz {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X M : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard)
    (hM : ∃ g : G, M = Submission.Blueprint.conj g H) (hXM : X ≤ M) :
    Even (Nat.card (M ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)) :=
  Prop1aBrSz.even_card_centralizer_of_fixes_three_brsz hFT hC (s4prop2_brsz_of_thmA hA hBrSz) hS hH
    hX3 hM hXM

/-- Every involution of `C_G(X)` lies in `p3F X = O^{2'}(C_G(X))`. -/
theorem involutions_le_p3F' (X : Subgroup G) :
    Submission.Blueprint.involutions (Subgroup.centralizer (X : Set G) : Set G) ⊆ p3F X := by
  rintro u ⟨hu, hu2⟩
  change u ∈ p3F X
  rw [mem_p3F]
  refine ⟨⟨u, hu⟩, ?_, rfl⟩
  exact involution_mem_oddResidual
    (x := (⟨u, hu⟩ : ↥(Subgroup.centralizer (X : Set G))))
    (Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hu2))

/-- **Ch. II §4 Prop. 1 (b)**, general form: for `X` fixing at least three points and a fixed point
`M = H^g ⊇ X`, the subgroup `F ⊓ M` is strongly embedded in `F = p3F X`. -/
theorem strongEmbedded_p3F_gen {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hBrSz : Submission.Blueprint.BrauerSuzukiProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {X : Subgroup G}
    (hX3 : 3 ≤ (Submission.Blueprint.fixedPts H X).ncard) :
    ∀ M : Subgroup G, X ≤ M → (∃ g : G, M = Submission.Blueprint.conj g H) →
      LeanEval.GroupTheory.Defs.IsStronglyEmbedded ((p3F X ⊓ M).subgroupOf (p3F X)) :=
  fun M hXM hM =>
    Prop1aBrSz.stronglyEmbedded_subgroupOf_inf_conj_of_even_card_at hH hX3
      (involutions_le_p3F' X) hXM hM
      (fun M' hM' hXM' => even_card_centralizer_brsz hFT hC hA hBrSz hS hH hX3 hM' hXM')

/-- `X ≤ H` for `X ≤ centD H t`. -/
theorem le_H_of_le_centD' {H : Subgroup G} {t : G} {X : Subgroup G} (hX : X ≤ centD H t) :
    X ≤ H :=
  hX.trans (by rw [centD_eq]; exact le_trans inf_le_left inf_le_left)

/-- The conclusion of Theorem B for `F`, when `O^{2'}(F) = F`: `F/O_{2'}(F)` is a simple Bender
group. -/
theorem benderConclusion_quotient' {F : Type} [Group F] [Finite F]
    (hBC : Submission.Blueprint.BenderConclusion F)
    (hres : Submission.Blueprint.oddResidual F = ⊤) :
    ∃ (Y : Type) (_ : Group Y) (φ : F →* Y), Function.Surjective φ ∧
      φ.ker = Submission.Blueprint.oddCore F ∧
      LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y := by
  obtain ⟨L, hLn, _hcore, hLidx, Y, hYgrp, φ, hφsurj, hφker, hY⟩ := hBC
  letI : Group Y := hYgrp
  have hLtop : L = ⊤ := by
    have hle : Submission.Blueprint.oddResidual F ≤ L :=
      (Work.Reductions.oddResidual_basic (G := F)).2.2.1 L hLn hLidx
    rw [hres] at hle
    exact top_le_iff.mp hle
  subst hLtop
  refine ⟨Y, hYgrp, φ.comp ((Subgroup.topEquiv (G := F)).symm : F →* ↥(⊤ : Subgroup F)),
    hφsurj.comp (Subgroup.topEquiv (G := F)).symm.surjective, ?_, hY⟩
  rw [← MonoidHom.comap_ker φ ((Subgroup.topEquiv (G := F)).symm : F →* ↥(⊤ : Subgroup F)),
    hφker]
  ext x
  show (((Subgroup.topEquiv (G := F)).symm x : ↥(⊤ : Subgroup F)) : F) ∈
    Submission.Blueprint.oddCore F ↔ x ∈ Submission.Blueprint.oddCore F
  rw [Subgroup.topEquiv_symm_apply_coe]

/-! ## 3. The `t`-torus of the model, lifted to `F = O^{2'}(C_G(X))` -/

theorem p3cd_torus_cyclic {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) (X : Subgroup G) (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    ∃ Kc : Subgroup G, (Kc : Set G) = (Work.ThreePoints.p3F X : Set G) ∩
        Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t ∧ IsCyclic Kc := by
  classical
  have hX3 : 3 ≤ (fixedPts H X).ncard :=
    P3NeBot.three_le_ncard_fixedPts_of_le_centD hH ht htH hX
  have hSE := strongEmbedded_p3F_gen hFT hC hA hBrSz hS hH hX3
  have hfour : Submission.Blueprint.HasFourGroup ↥(p3F X) :=
    p3cd_hasFourGroup hFT hC hA hZJ hBrSz hMod hS hH ht htH X hX0 hX hNX
  have htrans := p3cd_transitive hFT hC hA hZJ hBrSz hMod hS hH ht htH X hX0 hX hNX
  have hgen := p3cd_gen_by_involutions hFT hC hA hZJ hBrSz hMod hS hH ht htH X hX0 hX hNX
  have hXH : X ≤ H := le_H_of_le_centD' hX
  have hK : IsStronglyEmbedded ((p3F X ⊓ H).subgroupOf (p3F X)) := hSE H hXH ⟨1, (conj_one H).symm⟩
  have hBH : Submission.Blueprint.BenderHyp ↥(p3F X) := ⟨hfour, _, hK⟩
  have hBC : Submission.Blueprint.BenderConclusion ↥(p3F X) :=
    hS.2.1 ↥(p3F X) (gen_card_p3F_lt hS hH htH hX0 hX) hBH
  obtain ⟨Y, hYgrp, φ, hφsurj, hφker, hYbender⟩ :=
    benderConclusion_quotient' hBC (oddResidual_p3F_eq_top' X)
  letI : Group Y := hYgrp
  haveI : Finite Y := Finite.of_surjective φ hφsurj
  have hYsimple : IsSimpleGroup Y := (hMod Y hYbender).1
  have hOZ : Submission.Blueprint.oddCore ↥(p3F X) = Subgroup.center ↥(p3F X) :=
    p3cd_oddCore_eq_center hC hS hH ht htH X hX0 hX hfour hSE htrans hgen
      ⟨Y, hYgrp, φ, hφsurj, hφker, hYsimple⟩
  -- `t` in `F` and in `Y`
  have htF : t ∈ p3F X := gen_mem_p3F_t ht hX
  have htF2 : orderOf (⟨t, htF⟩ : ↥(p3F X)) = 2 :=
    (Subgroup.orderOf_coe (⟨t, htF⟩ : ↥(p3F X))).symm.trans ht
  have htFnotK : (⟨t, htF⟩ : ↥(p3F X)) ∉ (p3F X ⊓ H).subgroupOf (p3F X) := by
    intro hmem
    exact htH (Subgroup.mem_subgroupOf.mp hmem).2
  have hkerOdd : Odd (Nat.card ↥(φ.ker)) := by
    rw [hφker, hOZ]
    exact odd_card_center_of_isStronglyEmbedded hK
  have htY2 : orderOf (QuotientGroup.mk' φ.ker (⟨t, htF⟩ : ↥(p3F X))) = 2 :=
    orderOf_mk'_eq_two hkerOdd htF2
  have hkerLeH : φ.ker ≤ (p3F X ⊓ H).subgroupOf (p3F X) := by
    intro z hz
    by_contra hzK
    have hzc : z ∈ Subgroup.center ↥(p3F X) := by rw [← hOZ, ← hφker]; exact hz
    have hzN : z ∈ Subgroup.normalizer ((p3F X ⊓ H).subgroupOf (p3F X) : Set ↥(p3F X)) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have h : z * y * z⁻¹ = y := by
          rw [← Subgroup.mem_center_iff.mp hzc y]; group
        rwa [h]
      · intro hy
        have h : z * y * z⁻¹ = y := by
          rw [← Subgroup.mem_center_iff.mp hzc y]; group
        rwa [h] at hy
    have hconj : ((p3F X ⊓ H).subgroupOf (p3F X)).map (MulAut.conj z).toMonoidHom
        = (p3F X ⊓ H).subgroupOf (p3F X) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hzN
    have hodd := hK.2.2 z hzK
    rw [hconj, inf_idem] at hodd
    exact (Nat.not_odd_iff_even.mpr hK.2.1) hodd
  have hHY : IsStronglyEmbedded
      (((p3F X ⊓ H).subgroupOf (p3F X)).map (QuotientGroup.mk' φ.ker)) :=
    isStronglyEmbedded_map_quotient φ.ker hkerOdd hkerLeH hK
  have htYnot : (QuotientGroup.mk' φ.ker (⟨t, htF⟩ : ↥(p3F X))) ∉
      ((p3F X ⊓ H).subgroupOf (p3F X)).map (QuotientGroup.mk' φ.ker) := by
    intro hmem
    obtain ⟨x, hx, hxeq⟩ := Subgroup.mem_map.mp hmem
    have h1 : x⁻¹ * (⟨t, htF⟩ : ↥(p3F X)) ∈ φ.ker := by
      have h := QuotientGroup.eq.mp hxeq
      simpa using h
    have h3 : x⁻¹ * (⟨t, htF⟩ : ↥(p3F X)) ∈ (p3F X ⊓ H).subgroupOf (p3F X) := hkerLeH h1
    have h4 : x * (x⁻¹ * (⟨t, htF⟩ : ↥(p3F X))) ∈ (p3F X ⊓ H).subgroupOf (p3F X) :=
      Subgroup.mul_mem _ hx h3
    have h5 : x * (x⁻¹ * (⟨t, htF⟩ : ↥(p3F X))) = (⟨t, htF⟩ : ↥(p3F X)) := by group
    rw [h5] at h4
    exact htFnotK h4
  have hbender' : LeanEval.GroupTheory.Defs.IsSimpleBenderGroup (↥(p3F X) ⧸ φ.ker) :=
    Work.Endgame.IsSimpleBenderGroup.of_mulEquiv hYbender
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).symm
  obtain ⟨S, K₂, hS2, hSH, hSnorm, hSbot, hSup, hK₂set, hK₂cyc, hK₂card⟩ :=
    ((hMod (↥(p3F X) ⧸ φ.ker) hbender').2.2.2
        (((p3F X ⊓ H).subgroupOf (p3F X)).map (QuotientGroup.mk' φ.ker)) hHY).2
      (QuotientGroup.mk' φ.ker (⟨t, htF⟩ : ↥(p3F X))) htY2 htYnot
  haveI : IsCyclic ↥K₂ := hK₂cyc
  -- the preimage `L` of the torus in `F`, and its `t`-inverted part
  set L : Subgroup ↥(p3F X) := Subgroup.comap (QuotientGroup.mk' φ.ker) K₂ with hLdef
  set tF : ↥(p3F X) := ⟨t, htF⟩ with htFdef
  have hLcomm : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x := by
    let fL : ↥L →* ↥K₂ :=
      { toFun := fun x => ⟨QuotientGroup.mk' φ.ker ((x : ↥L) : ↥(p3F X)),
          Subgroup.mem_comap.mp x.2⟩
        map_one' := rfl
        map_mul' := fun x y => rfl }
    have hker : fL.ker ≤ Subgroup.center ↥L := by
      intro x hx
      rw [MonoidHom.mem_ker] at hx
      have hxker : ((x : ↥L) : ↥(p3F X)) ∈ φ.ker := by
        have h2 : ((fL x : ↥K₂) : ↥(p3F X) ⧸ φ.ker) = 1 := by rw [hx]; rfl
        exact (QuotientGroup.eq_one_iff _).mp h2
      have hxc : ((x : ↥L) : ↥(p3F X)) ∈ Subgroup.center ↥(p3F X) := by
        rw [← hOZ, ← hφker]; exact hxker
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (Subgroup.mem_center_iff.mp hxc ((y : ↥L) : ↥(p3F X)))
    haveI : IsMulCommutative ↥L := fL.isMulCommutative_of_isCyclic_of_ker_le_center hker
    intro x hx y hy
    exact congrArg (fun w : ↥L => ((w : ↥L) : ↥(p3F X)))
      (IsMulCommutative.is_comm.comm (⟨x, hx⟩ : ↥L) ⟨y, hy⟩)
  let J : Subgroup ↥(p3F X) :=
    { carrier := {x | x ∈ L ∧ tF * x * tF⁻¹ = x⁻¹}
      one_mem' := ⟨L.one_mem, by simp⟩
      mul_mem' := by
        rintro x y ⟨hxL, hx⟩ ⟨hyL, hy⟩
        refine ⟨L.mul_mem hxL hyL, ?_⟩
        have hcomm : x⁻¹ * y⁻¹ = y⁻¹ * x⁻¹ := hLcomm x⁻¹ (L.inv_mem hxL) y⁻¹ (L.inv_mem hyL)
        have h1 : tF * (x * y) * tF⁻¹ = (tF * x * tF⁻¹) * (tF * y * tF⁻¹) := by group
        rw [h1, hx, hy, mul_inv_rev, hcomm]
      inv_mem' := by
        rintro x ⟨hxL, hx⟩
        refine ⟨L.inv_mem hxL, ?_⟩
        have h1 : tF * x⁻¹ * tF⁻¹ = (tF * x * tF⁻¹)⁻¹ := by group
        rw [h1, hx, inv_inv] }
  have hJker : ∀ u : ↥J, QuotientGroup.mk' φ.ker ((u : ↥J) : ↥(p3F X)) = 1 → u = 1 := by
    intro u hu
    have huker : ((u : ↥J) : ↥(p3F X)) ∈ φ.ker := (QuotientGroup.eq_one_iff _).mp hu
    have hucen : ((u : ↥J) : ↥(p3F X)) ∈ Subgroup.center ↥(p3F X) := by
      rw [← hOZ, ← hφker]; exact huker
    have hunit : tF * ((u : ↥J) : ↥(p3F X)) * tF⁻¹ = ((u : ↥J) : ↥(p3F X)) := by
      have hcc : tF * ((u : ↥J) : ↥(p3F X)) = ((u : ↥J) : ↥(p3F X)) * tF :=
        Subgroup.mem_center_iff.mp hucen tF
      rw [hcc]; group
    have hinv : ((u : ↥J) : ↥(p3F X)) = (((u : ↥J) : ↥(p3F X)))⁻¹ :=
      hunit.symm.trans u.2.2
    have hsq : ((u : ↥J) : ↥(p3F X)) * ((u : ↥J) : ↥(p3F X)) = 1 :=
      mul_eq_one_iff_eq_inv.mpr hinv
    have h2 : orderOf (((u : ↥J) : ↥(p3F X))) ∣ 2 :=
      orderOf_dvd_iff_pow_eq_one.mpr (by rwa [pow_two])
    have h3 : orderOf (((u : ↥J) : ↥(p3F X))) ∣ Nat.card ↥(φ.ker) :=
      Subgroup.orderOf_dvd_natCard φ.ker huker
    have h4 : orderOf (((u : ↥J) : ↥(p3F X))) = 1 := by
      have h := Nat.dvd_gcd h2 h3
      rw [Nat.coprime_iff_gcd_eq_one.mp (Nat.coprime_two_left.mpr hkerOdd), Nat.dvd_one] at h
      exact h
    exact Subtype.ext (orderOf_eq_one_iff.mp h4)
  have hJcyc : IsCyclic ↥J := by
    let fJ : ↥J →* ↥K₂ :=
      { toFun := fun x => (⟨QuotientGroup.mk' φ.ker ((x : ↥J) : ↥(p3F X)),
          Subgroup.mem_comap.mp x.2.1⟩ : ↥K₂)
        map_one' := rfl
        map_mul' := fun x y => rfl }
    refine isCyclic_of_injective fJ ?_
    intro x y hxy
    have h1 : QuotientGroup.mk' φ.ker ((x : ↥J) : ↥(p3F X))
        = QuotientGroup.mk' φ.ker ((y : ↥J) : ↥(p3F X)) :=
      congrArg (fun z : ↥K₂ => (z : ↥(p3F X) ⧸ φ.ker)) hxy
    have hu : (⟨((x : ↥J) : ↥(p3F X))⁻¹ * ((y : ↥J) : ↥(p3F X)),
        J.mul_mem (J.inv_mem x.2) y.2⟩ : ↥J) = 1 := by
      apply hJker
      rw [map_mul, map_inv, h1, inv_mul_cancel]
    have h2 : ((x : ↥J) : ↥(p3F X))⁻¹ * ((y : ↥J) : ↥(p3F X)) = 1 :=
      congrArg (fun w : ↥J => ((w : ↥J) : ↥(p3F X))) hu
    exact Subtype.ext (inv_mul_eq_one.mp h2)
  -- conclusion
  refine ⟨J.map (p3F X).subtype ⊓ twoPoint H t, ?_, ?_⟩
  · ext x
    constructor
    · rintro ⟨hxJ, hxD⟩
      obtain ⟨y, hyJ, hyx⟩ := Subgroup.mem_map.mp hxJ
      have hxF : x ∈ p3F X := hyx ▸ y.2
      have hxinv : t * x * t⁻¹ = x⁻¹ := by
        have h2 : t * (y : G) * t⁻¹ = (y : G)⁻¹ := by
          simpa using congrArg (fun z : ↥(p3F X) => (z : G)) hyJ.2
        rw [← hyx]
        exact h2
      exact ⟨hxF, ⟨hxD, hxinv⟩⟩
    · rintro ⟨hxF, hxinv⟩
      have hxD : x ∈ twoPoint H t := hxinv.1
      have hxH : x ∈ H := hxD.1
      have hxinv' : t * x * t⁻¹ = x⁻¹ := hxinv.2
      have hinvt : t⁻¹ = t := inv_eq_of_mul_eq_one_right (mul_self_eq_one_of_orderOf_eq_two ht)
      have hzF : x⁻¹ ∈ p3F X := (p3F X).inv_mem hxF
      have hzK : (⟨x⁻¹, hzF⟩ : ↥(p3F X)) ∈ (p3F X ⊓ H).subgroupOf (p3F X) :=
        Subgroup.mem_subgroupOf.mpr ⟨hzF, H.inv_mem hxH⟩
      have hy_eq : tF * (⟨x⁻¹, hzF⟩ : ↥(p3F X)) * tF⁻¹ = (⟨x, hxF⟩ : ↥(p3F X)) := by
        apply Subtype.ext
        show t * x⁻¹ * t⁻¹ = x
        have h4 : t * x⁻¹ * t⁻¹ = (t * x * t⁻¹)⁻¹ := by group
        rw [h4, hxinv', inv_inv]
      have hy_eq' : (⟨x, hxF⟩ : ↥(p3F X)) = tF * (⟨x⁻¹, hzF⟩ : ↥(p3F X)) * tF⁻¹ := hy_eq.symm
      have hzY : QuotientGroup.mk' φ.ker (⟨x⁻¹, hzF⟩ : ↥(p3F X)) ∈
          ((p3F X ⊓ H).subgroupOf (p3F X)).map (QuotientGroup.mk' φ.ker) :=
        Subgroup.mem_map.mpr ⟨_, hzK, rfl⟩
      have htY_inv : (QuotientGroup.mk' φ.ker tF)⁻¹ = QuotientGroup.mk' φ.ker tF :=
        inv_eq_of_mul_eq_one_right (by
          have h := pow_orderOf_eq_one (QuotientGroup.mk' φ.ker tF)
          rw [htY2] at h
          simpa [pow_two] using h)
      refine ⟨Subgroup.mem_map.mpr ⟨(⟨x, hxF⟩ : ↥(p3F X)), ⟨?_, ?_⟩, rfl⟩, hxD⟩
      · rw [Subgroup.mem_comap]
        have hmem : ∀ y : ↥(p3F X) ⧸ φ.ker, y ∈ K₂ ↔ y ∈ Submission.Blueprint.invertedBy
            (Submission.Blueprint.twoPoint
              (((p3F X ⊓ H).subgroupOf (p3F X)).map (QuotientGroup.mk' φ.ker))
              (QuotientGroup.mk' φ.ker tF)) (QuotientGroup.mk' φ.ker tF) := by
          intro y; rw [← SetLike.mem_coe, hK₂set]
        rw [hmem]
        refine ⟨⟨?_, ?_⟩, ?_⟩
        · exact Subgroup.mem_map.mpr ⟨(⟨x, hxF⟩ : ↥(p3F X)),
            Subgroup.mem_subgroupOf.mpr ⟨hxF, hxH⟩, rfl⟩
        · refine Subgroup.mem_map.mpr ⟨QuotientGroup.mk' φ.ker (⟨x⁻¹, hzF⟩ : ↥(p3F X)), hzY, ?_⟩
          simpa only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_inv]
            using congrArg (QuotientGroup.mk' φ.ker) hy_eq
        · have hy : tF * (⟨x, hxF⟩ : ↥(p3F X)) * tF⁻¹ = (⟨x, hxF⟩ : ↥(p3F X))⁻¹ := by
            apply Subtype.ext
            show t * x * t⁻¹ = x⁻¹
            exact hxinv'
          simpa only [map_mul, map_inv] using congrArg (QuotientGroup.mk' φ.ker) hy
      · apply Subtype.ext
        change t * x * t⁻¹ = x⁻¹
        exact hxinv'
  · -- cyclicity of `J.map … ⊓ D`
    haveI hJinst : IsCyclic ↥J := hJcyc
    haveI : IsCyclic ↥(J.map (p3F X).subtype) :=
      isCyclic_of_injective
        (Subgroup.equivMapOfInjective J (p3F X).subtype (p3F X).subtype_injective).symm.toMonoidHom
        (Subgroup.equivMapOfInjective J (p3F X).subtype (p3F X).subtype_injective).symm.injective
    let g : ↥(J.map (p3F X).subtype ⊓ twoPoint H t) →* ↥(J.map (p3F X).subtype) :=
      { toFun := fun w => (⟨(w : G), (Subgroup.mem_inf.mp w.2).1⟩ : ↥(J.map (p3F X).subtype))
        map_one' := rfl
        map_mul' := fun a b => rfl }
    exact isCyclic_of_injective g
      (fun a b hab => Subtype.ext (congrArg (fun w : ↥(J.map (p3F X).subtype) => (w : G)) hab))

end Work.ThreePoints
