import Mathlib
import Submission.Blueprint.Interfaces
import Submission.Work.ThreePoints.Omega
import Submission.Work.ThreePoints.Sec2b
import Submission.Work.ThreePoints.TwoPointTransitive
import Submission.Work.ThreePoints.P3Sub.Basic
import Submission.Work.ThreePoints.P3NeBot.Basic
import Submission.Work.ThreePoints.P3NeBot.oddResidual_basic
import Submission.Work.ThreePoints.P3NeBot.p3_lemma1
import Submission.Work.Reductions.OddResidual
import Submission.Work.ThreePoints.centD_eq_centralizer_of_involution
import Submission.Work.ThreePoints.p3cd_hasFourGroup
import Submission.Work.ThreePoints.p3cd_strongEmbedded_gen
import Submission.Work.ThreePoints.p3cd_transitive
import Submission.Work.ThreePoints.p3cd_gen_by_involutions
import Submission.Work.ThreePoints.p3cd_oddCore_eq_center
import Submission.Work.ThreePoints.p3cd_torus_cyclic

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

open LeanEval.GroupTheory.Defs

namespace Work.ThreePoints

open Submission.Blueprint

variable {G : Type} [Group G] [Finite G]

/-! ## Elementary consequences of the hypotheses of Prop. 3 (c), (d)

We collect here the facts about `X ≤ V = centD H t` that the proof of Prop. 3 uses: `X ≤ H`,
`X ≤ D = H ⊓ H^t`, `|X|` odd, `X` fixes at least three points, the involutions of `C_G(X)`
lie in `F = O^{2'}(C_G(X))`, `t ∈ F`, and `|F| < |G|` (so that the induction hypothesis (B1)
of `Situation` applies to `F`). -/

/-- `X ≤ H` for `X ≤ centD H t`. -/
theorem p3cd_le_H_of_le_centD {H : Subgroup G} {t : G} {X : Subgroup G} (hX : X ≤ centD H t) :
    X ≤ H :=
  hX.trans (le_trans inf_le_left inf_le_left)

/-- `X ≤ H ⊓ H^t = twoPoint H t` for `X ≤ centD H t`. -/
theorem le_twoPoint_of_le_centD {H : Subgroup G} {t : G} {X : Subgroup G}
    (hX : X ≤ centD H t) : X ≤ twoPoint H t :=
  hX.trans inf_le_left

/-- `X` has odd order for `X ≤ centD H t` (`D = H ⊓ H^t` has odd order). -/
theorem odd_card_of_le_centD {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (htH : t ∉ H) {X : Subgroup G} (hX : X ≤ centD H t) : Odd (Nat.card X) :=
  Odd.of_dvd_nat (IsStronglyEmbedded.odd_card_inf_conj hH htH)
    (Subgroup.card_dvd_of_le (le_twoPoint_of_le_centD hX))

/-- `t` centralises `X` for `X ≤ centD H t`, hence lies in `C_G(X)`. -/
theorem mem_centralizer_of_le_centD {H : Subgroup G} {t : G} {X : Subgroup G}
    (hX : X ≤ centD H t) : t ∈ Subgroup.centralizer (X : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (mem_centD.mp (hX hx)).2.2

/-- Every involution of `C_G(X)` lies in `F = O^{2'}(C_G(X))` (an involution generates a
`2`-subgroup, and the quotient by `O^{2'}` has odd order). -/
theorem involutions_le_p3F (X : Subgroup G) :
    involutions (Subgroup.centralizer (X : Set G) : Set G) ⊆ p3F X := by
  rintro u ⟨hu, hu2⟩
  change u ∈ p3F X
  rw [mem_p3F]
  refine ⟨⟨u, hu⟩, ?_, rfl⟩
  exact involution_mem_oddResidual
    (x := (⟨u, hu⟩ : ↥(Subgroup.centralizer (X : Set G))))
    (Subtype.ext (mul_self_eq_one_of_orderOf_eq_two hu2))

/-- `t ∈ F = O^{2'}(C_G(X))` for `X ≤ centD H t` and `orderOf t = 2`. -/
theorem mem_p3F_t {H : Subgroup G} {t : G} (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X ≤ centD H t) : t ∈ p3F X :=
  involutions_le_p3F X ⟨mem_centralizer_of_le_centD hX, ht⟩

/-- `F = O^{2'}(C_G(X))` is non-trivial (it contains `t`). -/
theorem p3F_ne_bot {H : Subgroup G} {t : G} (ht : orderOf t = 2) {X : Subgroup G}
    (hX : X ≤ centD H t) : p3F X ≠ ⊥ := by
  intro hbot
  have htF : t ∈ p3F X := mem_p3F_t ht hX
  rw [hbot] at htF
  have h1 : t = 1 := Subgroup.mem_bot.mp htF
  rw [h1, orderOf_one] at ht
  exact absurd ht (by norm_num)

/-- `F = O^{2'}(C_G(X))` is contained in `N_G(X)`. -/
theorem p3cd_p3F_le_normalizer (X : Subgroup G) :
    p3F X ≤ Subgroup.normalizer (X : Set G) :=
  (p3F_le_centralizer X).trans (Subgroup.centralizer_le_normalizer (X : Set G))

/-- With `X ≠ ⊥`, `X ≤ centD H t` and `O_{2'}(G) = ⊥`, the centraliser `C_G(X)` is proper, so
`|F| = |O^{2'}(C_G(X))| < |G|`: this is what makes the induction hypothesis `(B1)` of
`Situation G` applicable to `F`. -/
theorem card_p3F_lt (hS : Situation G) {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (htH : t ∉ H) {X : Subgroup G} (hX0 : X ≠ ⊥) (hX : X ≤ centD H t) :
    Nat.card ↥(p3F X) < Nat.card G := by
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hCdef
  have hCne : C ≠ ⊤ := by
    intro hCt
    apply hX0
    have hXn : X.Normal := ⟨fun x hx g => by
      have hg : g ∈ C := hCt ▸ Subgroup.mem_top g
      have hc : x * g = g * x := Subgroup.mem_centralizer_iff.mp hg x hx
      rw [← hc, mul_inv_cancel_right]; exact hx⟩
    have hXD : X ≤ twoPoint H t := le_twoPoint_of_le_centD hX
    have hDodd : Odd (Nat.card (twoPoint H t)) := hH.2.2 t htH
    have hXodd : Odd (Nat.card X) :=
      Odd.of_dvd_nat hDodd (Subgroup.card_dvd_of_le hXD)
    have hXO : X ≤ oddCore G := le_sSup ⟨hXn, hXodd⟩
    rw [hS.2.2] at hXO
    exact le_bot_iff.mp hXO
  have hFC : p3F X ≤ C := p3F_le_centralizer X
  calc Nat.card ↥(p3F X) ≤ Nat.card C := Subgroup.card_le_of_le hFC
    _ < Nat.card G := by
      have h := Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hCne)
      simpa [Subgroup.card_top] using h

/-- `X ≤ V = centD H t` fixes at least the three points `H`, `H^t`, `H(t)` of `Ω = G ⧸ H`. -/
theorem three_le_fixedPts_of_le_centD {H : Subgroup G} (hH : IsStronglyEmbedded H) {t : G}
    (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G} (hX : X ≤ centD H t) :
    3 ≤ (fixedPts H X).ncard :=
  le_trans (three_le_ncard_fixedPts_centD hH ht htH)
    (Set.ncard_le_ncard (fixedPts_mono hX))

/-- `O^{2'}` is transported by a group isomorphism: `O^{2'}(B) = (O^{2'}(A)).map e`. -/
theorem map_oddResidual_mulEquiv {A B : Type} [Group A] [Finite A] [Group B] [Finite B]
    (e : A ≃* B) :
    (Submission.Blueprint.oddResidual A).map (e : A →* B) = Submission.Blueprint.oddResidual B := by
  apply le_antisymm
  · -- the preimage of `O^{2'}(B)` is a normal subgroup of odd index of `A`
    have hN : ((Submission.Blueprint.oddResidual B).comap (e : A →* B)).Normal :=
      (Work.Reductions.oddResidual_basic (G := B)).1.comap _
    have hidx : ((Submission.Blueprint.oddResidual B).comap (e : A →* B)).index =
        (Submission.Blueprint.oddResidual B).index :=
      Subgroup.index_comap_of_surjective _ e.surjective
    have hle : Submission.Blueprint.oddResidual A ≤
        (Submission.Blueprint.oddResidual B).comap (e : A →* B) :=
      (Work.Reductions.oddResidual_basic (G := A)).2.2.1 _
        hN (hidx ▸ (Work.Reductions.oddResidual_basic (G := B)).2.1)
    rintro _ ⟨a, ha, rfl⟩
    exact hle ha
  · -- the image of `O^{2'}(A)` is a normal subgroup of odd index of `B`
    have hN : ((Submission.Blueprint.oddResidual A).map (e : A →* B)).Normal :=
      (Work.Reductions.oddResidual_basic (G := A)).1.map (e : A →* B) e.surjective
    have hidx : ((Submission.Blueprint.oddResidual A).map (e : A →* B)).index =
        (Submission.Blueprint.oddResidual A).index := Subgroup.index_map_equiv _ e
    exact (Work.Reductions.oddResidual_basic (G := B)).2.2.1 _
      hN (hidx ▸ (Work.Reductions.oddResidual_basic (G := A)).2.1)

/-- **`O^{2'}` is idempotent on `O^{2'}(C_G(X))`.**  The group `F = O^{2'}(C_G(X))` of Prop. 3 has
no proper normal subgroup of odd index: `O^{2'}(F) = F`.  (This is what makes the `L` of
`BenderConclusion F`, which has odd index in `F`, equal to `F`.) -/
theorem oddResidual_p3F_eq_top (X : Subgroup G) :
    Submission.Blueprint.oddResidual ↥(p3F X) = ⊤ := by
  set C : Subgroup G := Subgroup.centralizer (X : Set G) with hCdef
  have he : ↥(Submission.Blueprint.oddResidual C) ≃*
      ↥((Submission.Blueprint.oddResidual C).map C.subtype) :=
    Subgroup.equivMapOfInjective _ C.subtype C.subtype_injective
  have key := map_oddResidual_mulEquiv he
  rw [Work.Reductions.oddResidual_self_eq_top (G := ↥C)] at key
  rw [Subgroup.map_top, MonoidHom.range_eq_top.mpr he.surjective] at key
  exact key.symm

/-- A group with `O^{2'}(G) = G` has no proper normal subgroup of odd index, so the `L` of
`BenderConclusion G` (which has odd index) is `G` itself: the conclusion of Theorem B then reads
`G/O_{2'}(G) ≅ Y` with `Y` a simple Bender group. -/
theorem benderConclusion_quotient_of_oddResidual_eq_top {F : Type} [Group F] [Finite F]
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

/-- The conclusion of Theorem B applied to `F = O^{2'}(C_G(X))` (a proper subgroup, by
`card_p3F_lt`): `F/O_{2'}(F) ≅ Y` with `Y` a simple Bender group — the second half of Prop. 3 (c)
once `O_{2'}(F) = Z(F)` is known. -/
theorem p3cd_quotient_of_benderConclusion (hS : Situation G) {H : Subgroup G}
    (hH : IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2) (htH : t ∉ H)
    (X : Subgroup G) (hX0 : X ≠ ⊥) (hX : X ≤ centD H t)
    (hBH : BenderHyp ↥(p3F X)) :
    ∃ (Y : Type) (_ : Group Y) (φ : ↥(p3F X) →* Y), Function.Surjective φ ∧
      φ.ker = oddCore ↥(p3F X) ∧
      LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y :=
  benderConclusion_quotient_of_oddResidual_eq_top
    (hS.2.1 _ (card_p3F_lt hS hH htH hX0 hX) hBH) (oddResidual_p3F_eq_top X)

/-- **Peterfalvi I Ch. I §1 (6) applied to `F ⊓ H`.**  `F ⊓ H` is a proper subgroup of `F`
(it does not contain `t`), so once `|F ⊓ H|` is even, `F ⊓ H` is strongly embedded in `F`.
The evenness `Even (Nat.card (p3F X ⊓ H))` is what Ch. II §4 Prop. 1 (a) supplies (via an
involution of `C_H(X)`), and is the Prop. 2 (a) input `V = C_D(u)`. -/
theorem stronglyEmbedded_p3F_inf_H_of_even {H : Subgroup G}
    (hH : IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2) (htH : t ∉ H) {X : Subgroup G}
    (hX : X ≤ centD H t) (hev : Even (Nat.card (p3F X ⊓ H : Subgroup G))) :
    IsStronglyEmbedded ((p3F X ⊓ H).subgroupOf (p3F X)) := by
  refine IsStronglyEmbedded.subgroupOf_inf hH ?_ hev
  intro htop
  have htF : t ∈ p3F X := mem_p3F_t ht hX
  have htH' : t ∈ H := by
    have hmem : (⟨t, htF⟩ : ↥(p3F X)) ∈ (p3F X ⊓ H).subgroupOf (p3F X) := by
      rw [htop]; trivial
    exact (Subgroup.mem_subgroupOf.mp hmem).2
  exact htH htH'

/-- **Peterfalvi I Ch. II §4 Lemma 1 (p. 169), set form.**  For `X ≤ V = C_D(t)`, the elements
of `K = J(D,t)` normalising `X` are exactly the elements of `F = O^{2'}(C_G(X))` lying in `K`:
both sides equal `N_K(X) = ⟨Inv C_G(X)⟩ ⊓ K` (`p3_lemma1`), and `F ⊇ ⟨Inv C_G(X)⟩` with
`F ≤ C_G(X) ≤ N_G(X)`. -/
theorem p3cd_lemma1 {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) (X : Subgroup G) (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    (Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t ∩
        (Subgroup.normalizer (X : Set G) : Set G)) =
      ((p3F X : Set G) ∩
        Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t) := by
  ext x
  constructor
  · rintro ⟨hxK, hxN⟩
    exact ⟨p3F1_le_p3F X
      (P3NeBot.p3_lemma1 hFT hC hA hBrSz hS hH ht htH hX hxK hxN), hxK⟩
  · rintro ⟨hxF, hxK⟩
    exact ⟨hxK, p3cd_p3F_le_normalizer X hxF⟩

/-- Peterfalvi I Ch. II §4 Prop. 3 (c), (d) in the source's case `X ≠ 1`: with `X ≠ ⊥`,
`X ≤ V = C_D(t)` and `N_K(X) ≠ 1`, setting `F = O^{2'}(C_G(X))`: `O_{2'}(F) = Z(F)`,
`F/Z(F)` is a simple Bender group, and `N_K(X) = C_K(X)` is a cyclic subgroup.
(`X ≠ ⊥` is what makes `|F| < |G|`, hence `(B1)` applicable to `F`.) -/
theorem sec4_prop3_cd_ne_bot {G : Type} [Group G] [Finite G]
    (hFT : Submission.Blueprint.FeitThompsonProp) (hC : Submission.Blueprint.ThmCProp)
    (hA : Submission.Blueprint.ThmAProp) (hZJ : Submission.Blueprint.GlaubermanZJProp)
    (hBrSz : Submission.Blueprint.BrauerSuzukiProp) (hMod : Submission.Blueprint.ModelFactsProp)
    (hS : Submission.Blueprint.Situation G) {H : Subgroup G}
    (hH : LeanEval.GroupTheory.Defs.IsStronglyEmbedded H) {t : G} (ht : orderOf t = 2)
    (htH : t ∉ H) (X : Subgroup G) (hX0 : X ≠ ⊥)
    (hX : X ≤ Submission.Blueprint.centD H t)
    (hNX : ∃ k ∈ Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t, k ≠ 1 ∧
      k ∈ Subgroup.normalizer (X : Set G)) :
    let C := Subgroup.centralizer (X : Set G)
    let F := (Submission.Blueprint.oddResidual C).map C.subtype
    (Submission.Blueprint.oddCore F = Subgroup.center F ∧
      ∃ (Y : Type) (_ : Group Y) (φ : F →* Y), Function.Surjective φ ∧
        φ.ker = Subgroup.center F ∧ LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y) ∧
    (∃ N : Subgroup G, (N : Set G) =
        Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t ∩
          (Subgroup.normalizer (X : Set G) : Set G) ∧
      N ≤ Subgroup.centralizer (X : Set G) ∧ IsCyclic N) := by
  have hfour := p3cd_hasFourGroup hFT hC hA hZJ hBrSz hMod hS hH ht htH X hX0 hX hNX
  have hSE := p3cd_strongEmbedded_gen hFT hC hA hZJ hBrSz hMod hS hH ht htH X hX0 hX hNX
  have htrans := p3cd_transitive hFT hC hA hZJ hBrSz hMod hS hH ht htH X hX0 hX hNX
  have hgen := p3cd_gen_by_involutions hFT hC hA hZJ hBrSz hMod hS hH ht htH X hX0 hX hNX
  have hBH : Submission.Blueprint.BenderHyp ↥(p3F X) :=
    ⟨hfour, (p3F X ⊓ H).subgroupOf (p3F X),
      hSE H (p3cd_le_H_of_le_centD hX) ⟨1, by rw [conj_one]⟩⟩
  obtain ⟨Y, hYgrp, φ, hφsurj, hφker, hY⟩ :=
    p3cd_quotient_of_benderConclusion hS hH ht htH X hX0 hX hBH
  haveI : Finite Y := Finite.of_surjective φ hφsurj
  have hYsimple : IsSimpleGroup Y := (hMod Y hY).1
  have hOZ := p3cd_oddCore_eq_center hC hS hH ht htH X hX0 hX hfour hSE htrans hgen
    ⟨Y, hYgrp, φ, hφsurj, hφker, hYsimple⟩
  have hd := p3cd_torus_cyclic hFT hC hA hZJ hBrSz hMod hS hH ht htH X hX0 hX hNX
  change (Submission.Blueprint.oddCore ↥(Work.ThreePoints.p3F X) =
        Subgroup.center ↥(Work.ThreePoints.p3F X) ∧
      ∃ (Y : Type) (_ : Group Y) (φ : ↥(Work.ThreePoints.p3F X) →* Y), Function.Surjective φ ∧
        φ.ker = Subgroup.center ↥(Work.ThreePoints.p3F X) ∧
          LeanEval.GroupTheory.Defs.IsSimpleBenderGroup Y) ∧
    (∃ N : Subgroup G, (N : Set G) =
        Submission.Blueprint.invertedBy (Submission.Blueprint.twoPoint H t) t ∩
          (Subgroup.normalizer (X : Set G) : Set G) ∧
      N ≤ Subgroup.centralizer (X : Set G) ∧ IsCyclic N)
  refine ⟨⟨hOZ, Y, hYgrp, φ, hφsurj, ?_, hY⟩, ?_⟩
  · rw [hφker, hOZ]
  · obtain ⟨Kc, hKcset, hKccyc⟩ := hd
    refine ⟨Kc, ?_, ?_, hKccyc⟩
    · rw [hKcset, p3cd_lemma1 hFT hC hA hZJ hBrSz hMod hS hH ht htH X hX0 hX hNX]
    · have hsub : (Kc : Set G) ⊆ (Work.ThreePoints.p3F X : Set G) := by
        rw [hKcset]; exact Set.inter_subset_left
      intro x hx
      exact p3F_le_centralizer X (hsub hx)

end Work.ThreePoints
