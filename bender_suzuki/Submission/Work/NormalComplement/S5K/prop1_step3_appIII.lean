/-
# `Submission.Work.NormalComplement.S5K.prop1_step3_appIII`

Appendix III applied to `N_G(P)/KKP`: the last clause of `AppIIIProp` gives that the image of the
`p`-subgroup `P₁ ≤ N_H(P)` in `F = N_G(P)/KKP` is cyclic, whence `P₁/P` is cyclic.
-/
import Mathlib
import Submission.Work.NormalComplement.S5K.prop1_step3_defs
import Submission.Work.NormalComplement.S5K.prop1_step3_ngp
import Submission.Work.NormalComplement.S5K.prop1_step3_aux3
import Submission.Work.NormalComplement.S5K.ca_coprime
import Submission.Work.NormalComplement.sec4_one_c
import Submission.Work.NormalComplement.sec5_setup

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option maxHeartbeats 1600000
open Classical
open scoped Pointwise
open Submission.Blueprint
open LeanEval.GroupTheory.Defs

namespace Work.NormalComplement.S5K

variable {G : Type} [Group G] [Finite G]
variable {H : Subgroup G} {t : G} {W : Subgroup G} {p : ℕ} {P A : Subgroup G}

theorem isCyclic_quotient_of_appIII
    (hFT : Submission.Blueprint.FeitThompsonProp)
    (hC4 : Submission.Blueprint.ChIIFourProp)
    (hIII : Work.NormalComplement.AppIIIProp)
    (h : Work.NormalComplement.Design.Setup45A G H t W p P A)
    (hPsyl : Work.NormalComplement.IsSylowIn p P (Submission.Blueprint.twoPoint H t))
    {P₁ : Subgroup G} (hPP₁ : P ≤ P₁)
    (hP₁H : P₁ ≤ H ⊓ NGP P)
    (hP₁p : IsPGroup p P₁) (hne : P₁ ≠ P) :
    ∃ (K : Type) (_ : Group K) (_ : Finite K) (φ : ↥P₁ →* K),
      Function.Surjective φ ∧ φ.ker = P.subgroupOf P₁ ∧ IsCyclic K ∧
      ∃ k : ℕ, 1 ≤ k ∧ Nat.card K = p ^ k := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hPt : P ≤ centD H t := h.P_le.trans inf_le_right
  have hpne2 : p ≠ 2 := setup5_p_ne_two h
  have hA : Submission.Blueprint.ThmAProp :=
    Work.DoubleTransitivity.Sec7.ThmA hFT Work.ThmF.ChV12.glaubermanZJ_free
      Work.BrauerSuzuki.brauerSuzuki
  set 𝒢 : Subgroup G := NGP P with h𝒢
  set KK : Subgroup ↥𝒢 := KKP H P with hKK
  haveI hKKN : KK.Normal := instKKPNormal H P
  have hkkOdd : Odd (Nat.card ↥KK) := odd_card_KKP h.se h.notMem hPt
  set X : Subgroup ↥𝒢 := (H ⊓ 𝒢).subgroupOf 𝒢 with hXdef
  set Y : Subgroup ↥𝒢 := (Submission.Blueprint.conj t H ⊓ 𝒢).subgroupOf 𝒢 with hYdef
  have hkkLeX : KK ≤ X := by rw [hXdef, hKK]; exact KKP_le_subgroupOf hPt
  have hkkLeY : KK ≤ Y := by
    rw [hYdef, hKK]
    intro y hy
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨(smul_pttP_eq_iff hPt).mp (KKP_fixes hy (pttP H P hPt)), y.2⟩
  -- the four hypotheses of `AppIIIProp`
  have h2tSub := normalizerTwoTransitive hA h hPsyl
  have h2t : MulAction.IsMultiplyPretransitive (↥𝒢 ⧸ KK) (OmP H P) 2 := by
    refine (MulAction.is_two_pretransitive_iff).mpr ?_
    intro a b c d hab hcd
    obtain ⟨g, hg𝒢, hg1, hg2⟩ := h2tSub (a : G ⧸ H) a.2 (b : G ⧸ H) b.2
      (fun hc => hab (Subtype.ext hc)) (c : G ⧸ H) c.2 (d : G ⧸ H) d.2
      (fun hc => hcd (Subtype.ext hc))
    refine ⟨QuotientGroup.mk' KK ⟨g, hg𝒢⟩, ?_, ?_⟩
    · exact Subtype.ext (by rw [quotient_smul_mk_OmP, coe_smul_OmP]; exact hg1)
    · exact Subtype.ext (by rw [quotient_smul_mk_OmP, coe_smul_OmP]; exact hg2)
  have hpre : MulAction.IsPretransitive (↥𝒢 ⧸ KK) (OmP H P) := by
    rw [MulAction.isPretransitive_iff]
    intro x y
    by_cases hxy : x = y
    · exact ⟨1, by rw [hxy, one_smul]⟩
    · obtain ⟨g, hg𝒢, hg1, -⟩ := h2tSub (x : G ⧸ H) x.2 (y : G ⧸ H) y.2
        (fun hc => hxy (Subtype.ext hc)) (y : G ⧸ H) y.2 (x : G ⧸ H) x.2
        (fun hc => hxy (Subtype.ext hc.symm))
      exact ⟨QuotientGroup.mk' KK ⟨g, hg𝒢⟩,
        Subtype.ext (by rw [quotient_smul_mk_OmP, coe_smul_OmP]; exact hg1)⟩
  have hfaith : ∀ g : ↥𝒢 ⧸ KK, (∀ x : OmP H P, g • x = x) → g = 1 := by
    intro g hg
    obtain ⟨γ, rfl⟩ := QuotientGroup.mk'_surjective KK g
    refine (QuotientGroup.eq_one_iff γ).mpr ?_
    rw [hKK, mem_KKP]
    exact hg
  have hfour : ¬ HasFourGroup (↥𝒢 ⧸ KK) :=
    Work.ThreePoints.P3NeBot.not_hasFourGroup_quotient KK hkkOdd
      (by rw [h𝒢]; exact not_hasFourGroup_normalizer hFT hC4 h)
  have hstabA : MulAction.stabilizer (↥𝒢 ⧸ KK) (ptP H P hPt) = X.map (QuotientGroup.mk' KK) := by
    exact stabilizer_ptP_quot hPt
  have hstabB : MulAction.stabilizer (↥𝒢 ⧸ KK) (pttP H P hPt) = Y.map (QuotientGroup.mk' KK) := by
    exact stabilizer_pttP_quot hPt
  have hse : IsStronglyEmbedded (MulAction.stabilizer (↥𝒢 ⧸ KK) (ptP H P hPt)) := by
    rw [hstabA]
    exact Work.NormalComplement.isStronglyEmbedded_map_of_surjective (QuotientGroup.mk' KK)
      (QuotientGroup.mk'_surjective KK) (QuotientGroup.ker_mk' KK) hkkOdd hkkLeX
      (by rw [hXdef, h𝒢]; exact stronglyEmbedded_normalizer hC4 h)
  have hcoatom : IsCoatom (MulAction.stabilizer (↥𝒢 ⧸ KK) (ptP H P hPt)) := by
    rw [hstabA]
    exact Commons.GroupTheory.Subgroup.isCoatom_map_of_ker_le (QuotientGroup.mk'_surjective KK)
      (by rw [hXdef, h𝒢]; exact isCoatom_normalizer hA h hPsyl)
      (by rw [QuotientGroup.ker_mk' KK]; exact hkkLeX)
  obtain ⟨appf, appQ, happf, happQn, happQne, happQc, happQe, happQinf, happQsup,
    happu, happmul, happinv, hlast⟩ :=
    hIII (↥𝒢 ⧸ KK) (OmP H P) (ptP H P hPt) hpre hfaith hfour hse hcoatom
  -- `¬ p ∣ |stab_a ⊓ stab_b|`
  have hbne : pttP H P hPt ≠ ptP H P hPt := by
    intro hc
    have h1 : (QuotientGroup.mk t : G ⧸ H) = (QuotientGroup.mk (1 : G) : G ⧸ H) := by
      have := congrArg (fun z : OmP H P => (z : G ⧸ H)) hc
      simpa using this
    have h2 : t⁻¹ * 1 ∈ H := QuotientGroup.eq.mp h1
    have h3 : t⁻¹ ∈ H := by simpa using h2
    exact h.notMem (by simpa using H.inv_mem h3)
  -- `X ⊓ Y = (D ⊓ 𝒢).subgroupOf 𝒢` and its image
  have hXY : X ⊓ Y = (Submission.Blueprint.twoPoint H t ⊓ 𝒢).subgroupOf 𝒢 := by
    rw [hXdef, hYdef]
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Submission.Blueprint.twoPoint]
    tauto
  have hZeq : Submission.Blueprint.twoPoint H t ⊓ 𝒢 =
      (A ⊓ Subgroup.centralizer (P : Set G)) ⊔ P := by
    rw [h𝒢]; exact (sec4_one_c hFT h).1
  have hZcard : Nat.card ↥(X ⊓ Y) = p * Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) := by
    have hnorm : (A ⊓ Subgroup.centralizer (P : Set G)) ≤ Subgroup.normalizer (P : Set G) :=
      inf_le_right.trans (Subgroup.centralizer_le_normalizer (P : Set G))
    have h2 : P ⊓ (A ⊓ Subgroup.centralizer (P : Set G)) = ⊥ := by
      have hle : P ⊓ (A ⊓ Subgroup.centralizer (P : Set G)) ≤ A ⊓ P :=
        le_inf (inf_le_right.trans inf_le_left) inf_le_left
      rw [h.A_inf] at hle
      exact le_antisymm hle bot_le
    have h1 := Work.NormalComplement.card_sup_mul_card_inf (H := P)
      (K := (A ⊓ Subgroup.centralizer (P : Set G))) hnorm
    rw [h2, Subgroup.card_bot, mul_one, h.P_card] at h1
    rw [hXY, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right)).toEquiv, hZeq, sup_comm]
    exact h1
  have hCcop : ¬ p ∣ Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) :=
    not_dvd_p_card_CA h hPsyl
  have hPleKK : P.subgroupOf 𝒢 ≤ KK := by
    rw [hKK]
    intro x hx
    rw [mem_KKP]
    intro ω
    exact Subtype.ext (ω.2 (x : G) (Subgroup.mem_subgroupOf.mp hx))
  have hKKleD : KK.map 𝒢.subtype ≤ Submission.Blueprint.twoPoint H t := by
    rw [hKK]; exact KKP_map_le_twoPoint hPt
  have hKcard : ∃ e, Nat.card ↥KK = p * e ∧ ¬ p ∣ e := by
    have h1 : Nat.card ↥(KK.map 𝒢.subtype) = Nat.card ↥KK :=
      Subgroup.card_map_of_injective (f := 𝒢.subtype) Subtype.coe_injective
    have hle : P ≤ KK.map 𝒢.subtype := by
      intro x hx
      exact Subgroup.mem_map.mpr ⟨⟨x, Subgroup.le_normalizer hx⟩,
        hPleKK (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have h2 : P.relIndex (KK.map 𝒢.subtype) * (KK.map 𝒢.subtype).relIndex
        (Submission.Blueprint.twoPoint H t) = P.relIndex (Submission.Blueprint.twoPoint H t) :=
      Subgroup.relIndex_mul_relIndex P _ (Submission.Blueprint.twoPoint H t) hle hKKleD
    have hpD : ¬ p ∣ P.relIndex (Submission.Blueprint.twoPoint H t) := hPsyl.2.2
    have h3 : ¬ p ∣ P.relIndex (KK.map 𝒢.subtype) := by
      intro hd
      exact hpD (h2 ▸ dvd_mul_of_dvd_left hd _)
    refine ⟨P.relIndex (KK.map 𝒢.subtype), ?_, h3⟩
    rw [← h1, ← Work.NormalComplement.relIndex_mul_card_of_le' hle, h.P_card, mul_comm]
  -- `p ∤ |stab_a ⊓ stab_b|`
  have hstabInf : (MulAction.stabilizer (↥𝒢 ⧸ KK) (ptP H P hPt)) ⊓
      (MulAction.stabilizer (↥𝒢 ⧸ KK) (pttP H P hPt)) =
      (X ⊓ Y).map (QuotientGroup.mk' KK) := by
    rw [hstabA, hstabB,
      ← Commons.GroupTheory.Subgroup.map_inf_eq_of_ker_le (QuotientGroup.mk' KK) X Y
        (by rw [QuotientGroup.ker_mk' KK]; exact hkkLeX)]
  have hrel : ¬ p ∣ KK.relIndex (X ⊓ Y) := by
    obtain ⟨e, hKc1, hKc2⟩ := hKcard
    have h1 : KK.relIndex (X ⊓ Y) * Nat.card ↥KK = Nat.card ↥(X ⊓ Y) :=
      Work.NormalComplement.relIndex_mul_card_of_le' (le_inf hkkLeX hkkLeY)
    rw [hZcard, hKc1] at h1
    have h2 : (KK.relIndex (X ⊓ Y) * e) * p =
        Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) * p := by
      rw [mul_comm (Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G))) p, ← h1]; ring
    have h3 : KK.relIndex (X ⊓ Y) * e = Nat.card ↥(A ⊓ Subgroup.centralizer (P : Set G)) :=
      Nat.mul_right_cancel h.prime.pos h2
    intro hd
    exact hCcop (h3 ▸ dvd_mul_of_dvd_left hd _)
  have hnotdvd : ¬ p ∣ Nat.card ↥((MulAction.stabilizer (↥𝒢 ⧸ KK) (ptP H P hPt)) ⊓
      (MulAction.stabilizer (↥𝒢 ⧸ KK) (pttP H P hPt))) := by
    rw [hstabInf]
    have h1 := Work.LocalPrelim.card_map_mul_card_inf_ker (QuotientGroup.mk' KK) (X ⊓ Y)
    rw [QuotientGroup.ker_mk' KK] at h1
    have h2 : (X ⊓ Y) ⊓ KK = KK := inf_eq_right.mpr (le_inf hkkLeX hkkLeY)
    rw [h2] at h1
    have h3 : KK.relIndex (X ⊓ Y) * Nat.card ↥KK = Nat.card ↥(X ⊓ Y) :=
      Work.NormalComplement.relIndex_mul_card_of_le' (le_inf hkkLeX hkkLeY)
    have h4 : Nat.card ↥((X ⊓ Y).map (QuotientGroup.mk' KK)) = KK.relIndex (X ⊓ Y) :=
      Nat.eq_of_mul_eq_mul_right Nat.card_pos (h1.trans h3.symm)
    rw [h4]
    exact hrel
  -- the image `R₀` of `P₁` is a `p`-subgroup of the point stabiliser
  have hP₁le𝒢 : P₁ ≤ 𝒢 := fun x hx => (hP₁H hx).2
  have hRle : (P₁.subgroupOf 𝒢).map (QuotientGroup.mk' KK) ≤
      MulAction.stabilizer (↥𝒢 ⧸ KK) (ptP H P hPt) := by
    rw [hstabA]
    exact Subgroup.map_mono (fun x hx =>
      Subgroup.mem_subgroupOf.mpr ⟨(hP₁H (Subgroup.mem_subgroupOf.mp hx)).1, x.2⟩)
  have hRp : IsPGroup p ↥((P₁.subgroupOf 𝒢).map (QuotientGroup.mk' KK)) :=
    ((hP₁p.of_injective (Subgroup.subgroupOfEquivOfLe hP₁le𝒢).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hP₁le𝒢).injective).map (QuotientGroup.mk' KK))
  have hcycR : IsCyclic ↥((P₁.subgroupOf 𝒢).map (QuotientGroup.mk' KK)) :=
    (hlast h2t p h.prime (pttP H P hPt) hbne hnotdvd _ hRle hRp).2 hpne2
  -- `P₁ ⊓ KKP = P`
  have hPleKKimg : P ≤ KK.map 𝒢.subtype := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨⟨x, Subgroup.le_normalizer hx⟩, ?_, rfl⟩
    rw [mem_KKP]
    intro ω
    exact Subtype.ext (ω.2 x hx)
  have hPKK : P₁ ⊓ (KK.map 𝒢.subtype) = P := by
    have hQp : IsPGroup p ↥(P₁ ⊓ (KK.map 𝒢.subtype)) := IsPGroup.to_le hP₁p inf_le_left
    have hle : P₁ ⊓ (KK.map 𝒢.subtype) ≤ Submission.Blueprint.twoPoint H t := by
      show P₁ ⊓ (KK.map 𝒢.subtype) ≤ H ⊓ Submission.Blueprint.conj t H
      exact le_inf (inf_le_left.trans (hP₁H.trans inf_le_left))
        (inf_le_right.trans (hKKleD.trans inf_le_right))
    have hmax := card_le_card_of_isSylowIn h.prime hPsyl.2.1 hPsyl.1 hPsyl.2.2
      hle hQp (le_inf hPP₁ hPleKKimg)
    exact (Subgroup.eq_of_le_of_card_ge (le_inf hPP₁ hPleKKimg) hmax).symm
  -- transport: `↥P₁ ⧸ P` is isomorphic to the image `R₀`
  have hPleKKP₁ : P.subgroupOf P₁ ≤ (KK.map 𝒢.subtype).subgroupOf P₁ := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hPleKKimg (Subgroup.mem_subgroupOf.mp hx))
  refine ⟨↥((P₁.subgroupOf 𝒢).map (QuotientGroup.mk' KK)), inferInstance, inferInstance,
    { toFun := fun x => ⟨QuotientGroup.mk' KK ⟨(x : G), hP₁le𝒢 x.2⟩,
        Subgroup.mem_map.mpr ⟨⟨(x : G), hP₁le𝒢 x.2⟩, Subgroup.mem_subgroupOf.mpr x.2, rfl⟩⟩
      map_one' := Subtype.ext (by
        show (QuotientGroup.mk' KK) (1 : ↥𝒢) = (1 : ↥𝒢 ⧸ KK)
        exact map_one (QuotientGroup.mk' KK))
      map_mul' := fun a b => Subtype.ext (by
        show (QuotientGroup.mk' KK) ((⟨(a : G), hP₁le𝒢 a.2⟩ : ↥𝒢) *
            ⟨(b : G), hP₁le𝒢 b.2⟩) =
          (QuotientGroup.mk' KK) ⟨(a : G), hP₁le𝒢 a.2⟩ *
            (QuotientGroup.mk' KK) ⟨(b : G), hP₁le𝒢 b.2⟩
        exact map_mul (QuotientGroup.mk' KK) _ _) }, ?_, ?_, ?_, ?_⟩
  · intro z
    obtain ⟨y, hy, hyz⟩ := Subgroup.mem_map.mp z.2
    have hyP₁ : (y : G) ∈ P₁ := Subgroup.mem_subgroupOf.mp hy
    refine ⟨⟨(y : G), hyP₁⟩, Subtype.ext ?_⟩
    rw [← hyz]; rfl
  · ext x
    constructor
    · intro hx
      rw [MonoidHom.mem_ker] at hx
      have h1 : (⟨(x : G), hP₁le𝒢 x.2⟩ : ↥𝒢) ∈ KK :=
        (QuotientGroup.eq_one_iff _).mp (Subtype.ext_iff.mp hx)
      have h3 : (x : G) ∈ P₁ ⊓ (KK.map 𝒢.subtype) :=
        ⟨x.2, Subgroup.mem_map.mpr ⟨_, h1, rfl⟩⟩
      rw [hPKK] at h3
      exact Subgroup.mem_subgroupOf.mpr h3
    · intro hx
      have hxp : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
      have h2 : (x : G) ∈ KK.map 𝒢.subtype :=
        ⟨⟨(x : G), hP₁le𝒢 x.2⟩, hPleKK (Subgroup.mem_subgroupOf.mpr hxp), rfl⟩
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp h2
      have h3 : (⟨(x : G), hP₁le𝒢 x.2⟩ : ↥𝒢) = y := Subtype.ext (by rw [← hyx]; rfl)
      rw [MonoidHom.mem_ker]
      refine Subtype.ext ?_
      show (QuotientGroup.mk' KK) (⟨(x : G), hP₁le𝒢 x.2⟩ : ↥𝒢) = (1 : ↥𝒢 ⧸ KK)
      rw [h3]
      exact (QuotientGroup.eq_one_iff _).mpr hy
  · exact hcycR
  · obtain ⟨j, hj⟩ := (IsPGroup.iff_card (p := p) (G := ↥P₁)).mp hP₁p
    have hcard1 : Nat.card ↥(P₁.subgroupOf 𝒢) = p ^ j := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hP₁le𝒢).toEquiv]; exact hj
    have hcardP : Nat.card ↥((P₁.subgroupOf 𝒢) ⊓ KK) = p := by
      have h1 : (P₁.subgroupOf 𝒢) ⊓ KK = P.subgroupOf 𝒢 := by
        ext y
        rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        constructor
        · rintro ⟨hy1, hy2⟩
          have h3 : (y : G) ∈ P₁ ⊓ (KK.map 𝒢.subtype) :=
            ⟨hy1, Subgroup.mem_map.mpr ⟨y, hy2, rfl⟩⟩
          rwa [hPKK] at h3
        · intro hy
          exact ⟨hPP₁ hy, hPleKK (Subgroup.mem_subgroupOf.mpr hy)⟩
      rw [h1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe
        (show P ≤ 𝒢 from fun x hx => Subgroup.le_normalizer hx)).toEquiv]
      exact h.P_card
    have hmul := Work.LocalPrelim.card_map_mul_card_inf_ker (QuotientGroup.mk' KK)
      (P₁.subgroupOf 𝒢)
    rw [QuotientGroup.ker_mk' KK, hcardP, hcard1] at hmul
    have hjge2 : 2 ≤ j := by
      have hlt : Nat.card ↥P < Nat.card ↥P₁ :=
        card_lt_card_of_lt (lt_of_le_of_ne hPP₁ (Ne.symm hne))
      rw [hj, h.P_card] at hlt
      by_contra hcon
      push_neg at hcon
      interval_cases j
      · rw [pow_zero] at hlt; have := h.prime.two_le; omega
      · rw [pow_one] at hlt; omega
    refine ⟨j - 1, by omega, ?_⟩
    have h2 : p ^ j = p * p ^ (j - 1) := by
      rw [← pow_succ', Nat.sub_add_cancel (by omega : 1 ≤ j)]
    rw [h2] at hmul
    rw [mul_comm (Nat.card ↥((P₁.subgroupOf 𝒢).map (QuotientGroup.mk' KK))) p] at hmul
    exact Nat.mul_left_cancel h.prime.pos hmul
end Work.NormalComplement.S5K
