import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.PSU3.StageB.NotFpfStep2.quot_isPSU3
import Submission.Work.PSU3.StageB.NotFpfStep2.isSplitRankOne_map_center
import Submission.Work.PSU3.StageB.NotFpfStep2.center_le_P
import Submission.Work.PSU3.StageB.NotFpfStep2.center_le_centD
import Submission.Work.PSU3.StageB.NotFpfStep2.eq_of_phi_eq_of_mem
import Submission.Work.PSU3.StageB.Canon
import Submission.Work.PSU3.StageB.NotFpfStep4.psu3_cor2_datum

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

namespace Work.PSU3.StageB.NotFpfStep4

open LeanEval.GroupTheory.Defs
open Submission.Blueprint

/-- The kernel of `e ∘ mk' Z` for an isomorphism `e : F ⧸ Z ≃* Y` is `Z`. -/
private lemma ker_comp_mk'_equiv {F Y : Type} [Group F] [Group Y] (Z : Subgroup F) [Z.Normal]
    (e : F ⧸ Z ≃* Y) :
    (e.toMonoidHom.comp (QuotientGroup.mk' Z)).ker = Z := by
  ext x
  rw [MonoidHom.mem_ker]
  constructor
  · intro hx
    have hq : (QuotientGroup.mk' Z) x = 1 := e.injective (by simpa using hx)
    rw [QuotientGroup.mk'_apply Z x] at hq
    exact (QuotientGroup.eq_one_iff x).mp hq
  · intro hx
    rw [MonoidHom.comp_apply]
    have : (QuotientGroup.mk' Z) x = 1 := by
      rw [QuotientGroup.mk'_apply Z x]; exact (QuotientGroup.eq_one_iff x).mpr hx
    rw [this, map_one]

/-- The map `e ∘ mk' Z` is surjective. -/
private lemma surj_comp_mk'_equiv {F Y : Type} [Group F] [Group Y] (Z : Subgroup F) [Z.Normal]
    (e : F ⧸ Z ≃* Y) :
    Function.Surjective (e.toMonoidHom.comp (QuotientGroup.mk' Z)) := by
  intro y
  obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective Z (e.symm y)
  exact ⟨x, by rw [MonoidHom.comp_apply, hx]; exact e.apply_symm_apply y⟩

/-- **Peterfalvi II Ch. VII §4 (2), the transfer half**: Cor. 2 of the §3 Proposition, transported
through `U/(P ∩ U) = U/Z(U) ≅ PSU(3,ℓ)` (with `U = O^{2'}(C_G(P))`) and lifted back to `G`.

`ζ₁` is the source's `ζ₁ ∈ (V ∩ U) − (P ∩ U)` (`V = centD H t`); the conclusion is the source's
`ω ∈ (Q − Q₀) ∩ U` with `f(ω) = ω^{−ζ₁} = ζ₁⁻¹ ω⁻¹ ζ₁` and `h(ω) ∈ ζ₁³ (P ∩ U)`. -/
theorem transfer_cor2_step4 {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp)
    (hQ3 : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3) (hW : Work.ThmF.W H t ≠ ⊥)
    {P : Subgroup G} (hPV : P ≤ Submission.Blueprint.centD H t) (hPp : (Nat.card P).Prime)
    (hPne : P ≠ ⊥) {y : G} (hyQ : y ∈ Q) (hy0 : y ∉ Work.ThmF.Q0sub H)
    (hyc : ∀ p ∈ P, p⁻¹ * y * p = y)
    (hZV : (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)).map
      (Work.PSU3.StageB.centralizerOddResidual P).subtype ≤ Submission.Blueprint.centD H t)
    {ζ₁ : G} (hζ₁V : ζ₁ ∈ Submission.Blueprint.centD H t)
    (hζ₁F : ζ₁ ∈ Work.PSU3.StageB.centralizerOddResidual P)
    (hζ₁nZ : ζ₁ ∉ (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)).map
      (Work.PSU3.StageB.centralizerOddResidual P).subtype) :
    ∃ ω : ↥Q, (ω : G) ∉ Work.ThmF.Q0sub H ∧
      (ω : G) ∈ Work.PSU3.StageB.centralizerOddResidual P ∧
      (Work.PSU3.StageB.fcan hS.split ω : G) = ζ₁⁻¹ * (ω : G)⁻¹ * ζ₁ ∧
      ∃ η₂ : G, η₂ ∈ P ∧ (Work.PSU3.StageB.hcan hS.split ω : G) = ζ₁ ^ 3 * η₂ := by
  classical
  -- ## 0. the model
  obtain ⟨n', hn'2, _hn'card, ⟨e⟩⟩ :=
    Work.PSU3.StageB.NotFpfStep2.quot_isPSU3 hS hC4 hHig hQ3 hW hPV hPp hPne hyQ hy0 hyc hZV
  let F : Subgroup G := Work.PSU3.StageB.centralizerOddResidual P
  have hF : t ∈ F := (Work.PSU3.StageB.t_mem_and_center_quotient hS hPV).1
  let ZF : Subgroup ↥F := Subgroup.center ↥F
  let φ : ↥F →* PSU3Model n' := e.toMonoidHom.comp (QuotientGroup.mk' ZF)
  have hφker : φ.ker = ZF := ker_comp_mk'_equiv ZF e
  have hφsurj : Function.Surjective φ := surj_comp_mk'_equiv ZF e
  let tF : ↥F := ⟨t, hF⟩
  let B : Subgroup (PSU3Model n') := ((H ⊓ F).subgroupOf F).map φ
  let Ub : Subgroup (PSU3Model n') := ((Q ⊓ F).subgroupOf F).map φ
  let w : PSU3Model n' := φ tF
  have hdatum : IsSplitRankOne B Ub w :=
    Work.PSU3.StageB.NotFpfStep2.isSplitRankOne_map_center hS hC4 hPV hPp hφsurj hφker
      (IsSimpleBenderGroup.isPSU3 n' hn'2 (MulEquiv.refl _))
  -- ## 1. the element `ζ₁` and its image `ζ = φ ζ₁`
  have hζ1tp : ζ₁ ∈ Submission.Blueprint.twoPoint H t := (Subgroup.mem_inf.mp hζ₁V).1
  have hζ1H : ζ₁ ∈ H := (Subgroup.mem_inf.mp hζ1tp).1
  have hζ1ct : ζ₁ * t = t * ζ₁ :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hζ₁V).2
  let ζF : ↥F := ⟨ζ₁, hζ₁F⟩
  have htFζF : tF⁻¹ * ζF * tF = ζF := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, tF, ζF]
    rw [mul_assoc, hζ1ct, ← mul_assoc, inv_mul_cancel, one_mul]
  have hζF_in : ζF ∈ (H ⊓ F).subgroupOf F :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hζ1H, hζ₁F⟩)
  have hζF_imgB : φ ζF ∈ B := Subgroup.mem_map_of_mem φ hζF_in
  have hζF_conj : w⁻¹ * φ ζF * w ∈ B := by
    have h1 : w⁻¹ * φ ζF * w = φ ζF := by
      rw [show w⁻¹ * φ ζF * w = φ (tF⁻¹ * ζF * tF) from by
        rw [← map_inv, ← map_mul, ← map_mul], htFζF]
    rw [h1]; exact hζF_imgB
  have hζF_cent : φ ζF ∈ Subgroup.centralizer ({w} : Set (PSU3Model n')) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : w⁻¹ * φ ζF * w = φ ζF := by
      rw [show w⁻¹ * φ ζF * w = φ (tF⁻¹ * ζF * tF) from by
        rw [← map_inv, ← map_mul, ← map_mul], htFζF]
    calc φ ζF * w = (w * w⁻¹) * (φ ζF * w) := by rw [mul_inv_cancel, one_mul]
      _ = w * (w⁻¹ * φ ζF * w) := by group
      _ = w * φ ζF := by rw [h1]
  have hζ : φ ζF ∈ Submission.Blueprint.centD B w :=
    Subgroup.mem_inf.mpr
      ⟨Subgroup.mem_inf.mpr
        ⟨hζF_imgB, (Work.Models.mem_conj_iff (H := B) (g := w) (x := φ ζF)).mpr hζF_conj⟩,
       hζF_cent⟩
  have hζne : φ ζF ≠ 1 := by
    intro h1
    apply hζ₁nZ
    have hmem : ζF ∈ φ.ker := by rw [MonoidHom.mem_ker]; exact h1
    rw [hφker] at hmem
    exact Subgroup.mem_map.mpr ⟨ζF, hmem, rfl⟩
  -- ## 2. the corollary in the model
  obtain ⟨ωbar, hωbar2, hfbar, hhbar⟩ := psu3_cor2_datum hn'2 hdatum hζ hζne
  -- ## 3. lift `ω̄` back to `G`
  obtain ⟨ωF, hωF_sub, hφω⟩ := Subgroup.mem_map.mp ωbar.2
  have hωF_int : (ωF : G) ∈ Q ⊓ F := Subgroup.mem_subgroupOf.mp hωF_sub
  have hωQ : (ωF : G) ∈ Q := (Subgroup.mem_inf.mp hωF_int).1
  have hωFmem : (ωF : G) ∈ F := (Subgroup.mem_inf.mp hωF_int).2
  let ωQ : ↥Q := ⟨(ωF : G), hωQ⟩
  have hωbar_ne : (ωbar : PSU3Model n') ≠ 1 :=
    fun h1 => hωbar2 (by rw [h1, one_mul])
  have hω2ne : (ωF : G) * (ωF : G) ≠ 1 := by
    intro h1
    apply hωbar2
    have h2 : (ωF * ωF : ↥F) = 1 := by
      apply Subtype.ext; simpa using h1
    calc (ωbar : PSU3Model n') * (ωbar : PSU3Model n')
        = φ ωF * φ ωF := by rw [hφω]
      _ = φ (ωF * ωF) := by rw [map_mul]
      _ = φ 1 := by rw [h2]
      _ = 1 := map_one φ
  have hωF_ne : (ωF : G) ≠ 1 := fun h => hω2ne (by rw [h, mul_one])
  have hωQ_ne : (ωQ : G) ≠ 1 := hωF_ne
  have hω0 : (ωQ : G) ∉ Work.ThmF.Q0sub H := by
    intro hmem
    have hsq : (ωQ : G) * (ωQ : G) = 1 := Work.PSU3.StageA.caseC_mem_Q0sub_iff hS hC4 _ hmem
    exact hω2ne (by rw [show (ωF : G) = (ωQ : G) from rfl, hsq])
  -- ## 4. the canonical relation in the model, lifted
  have hcanonY : w * (ωbar : PSU3Model n') * w =
      (↑(Work.PSU3.StageB.gcan hdatum ωbar) : PSU3Model n') *
        (↑(Work.PSU3.StageB.hcan hdatum ωbar) : PSU3Model n') * w *
        (↑(Work.PSU3.StageB.fcan hdatum ωbar) : PSU3Model n') :=
    Work.PSU3.StageB.canon_spec hdatum hωbar_ne
  obtain ⟨gF, hgF_sub, hφg⟩ := Subgroup.mem_map.mp (Work.PSU3.StageB.gcan hdatum ωbar).2
  obtain ⟨yF, hyF_sub, hφy⟩ := Subgroup.mem_map.mp (Work.PSU3.StageB.fcan hdatum ωbar).2
  have hgQ : (gF : G) ∈ Q := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hgF_sub)).1
  have hyQ' : (yF : G) ∈ Q := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hyF_sub)).1
  have hL : φ (tF * ωF * tF) = w * (ωbar : PSU3Model n') * w := by
    rw [show φ (tF * ωF * tF) = φ (tF * ωF) * φ tF from map_mul φ _ _,
      show φ (tF * ωF) = φ tF * φ ωF from map_mul φ _ _, hφω]
  have hR : φ (gF * ζF ^ 3 * tF * yF) = w * (ωbar : PSU3Model n') * w := by
    rw [show φ (gF * ζF ^ 3 * tF * yF) = φ (gF * ζF ^ 3 * tF) * φ yF from map_mul φ _ _,
      show φ (gF * ζF ^ 3 * tF) = φ (gF * ζF ^ 3) * φ tF from map_mul φ _ _,
      show φ (gF * ζF ^ 3) = φ gF * φ (ζF ^ 3) from map_mul φ _ _,
      map_pow φ ζF 3, hφg, hφy]
    rw [show (φ ζF : PSU3Model n') ^ 3 = (Work.PSU3.StageB.hcan hdatum ωbar : PSU3Model n')
      from hhbar.symm, ← hcanonY]
  have hφeq : φ (tF * ωF * tF) = φ (gF * ζF ^ 3 * tF * yF) := by rw [hL, hR]
  let zF : ↥F := (tF * ωF * tF) * (gF * ζF ^ 3 * tF * yF)⁻¹
  have hzF : zF ∈ ZF := by
    rw [← hφker, MonoidHom.mem_ker]
    show φ ((tF * ωF * tF) * (gF * ζF ^ 3 * tF * yF)⁻¹) = 1
    rw [map_mul, map_inv, hφeq, mul_inv_cancel]
  have hGeq : t * (ωF : G) * t = (zF : G) * (gF : G) * ζ₁ ^ 3 * t * (yF : G) := by
    have h1 : zF * (gF * ζF ^ 3 * tF * yF) = tF * ωF * tF := by
      dsimp only [zF]; group
    have h2 := congrArg (fun x : ↥F => (x : G)) h1
    simp only [Subgroup.coe_mul, Subgroup.coe_pow, tF, ζF] at h2
    rw [← h2]
    group
  have hcomm_zg : (zF : G) * (gF : G) = (gF : G) * (zF : G) := by
    have h := congrArg (fun x : ↥F => (x : G)) (Subgroup.mem_center_iff.mp hzF gF)
    simpa only [Subgroup.coe_mul] using h.symm
  have hcanonG : t * (ωF : G) * t = (gF : G) * ((zF : G) * ζ₁ ^ 3) * t * (yF : G) := by
    rw [hGeq, hcomm_zg]
    group
  -- ## 5. the canonical data in `G`
  have hd_mem : (zF : G) * ζ₁ ^ 3 ∈ Submission.Blueprint.twoPoint H t :=
    (Submission.Blueprint.twoPoint H t).mul_mem
      (Subgroup.mem_inf.mp (hZV (Subgroup.mem_map_of_mem F.subtype hzF)).1)
      ((Submission.Blueprint.twoPoint H t).pow_mem hζ1tp 3)
  obtain ⟨_hgcan_eq, hhcan_eq, hfcan_eq⟩ :=
    Work.PSU3.StageB.canon_unique'' hS.split (x := ωQ) hωQ_ne
      (g := ⟨(gF : G), hgQ⟩) (d := ⟨(zF : G) * ζ₁ ^ 3, hd_mem⟩)
      (y := ⟨(yF : G), hyQ'⟩) hcanonG
  -- ## 6. the `f`-part
  have hZtwo : ∀ z ∈ ZF, ((z : ↥F) : G) ∈ Submission.Blueprint.twoPoint H t :=
    fun z hz => Subgroup.mem_inf.mp (hZV (Subgroup.mem_map_of_mem F.subtype hz)).1
  have hbFmem : ζ₁⁻¹ * (ωF : G)⁻¹ * ζ₁ ∈ F :=
    F.mul_mem (F.mul_mem (F.inv_mem hζ₁F) (F.inv_mem hωFmem)) hζ₁F
  have hbQ : ζ₁⁻¹ * (ωF : G)⁻¹ * ζ₁ ∈ Q := by
    have := Work.RankOneUniqueness.conj_mem_of_mem hS.split (H.inv_mem hζ1H) (Q.inv_mem hωQ)
    simpa using this
  have hb_sub : (⟨ζ₁⁻¹ * (ωF : G)⁻¹ * ζ₁, hbFmem⟩ : ↥F) ∈ (Q ⊓ F).subgroupOf F :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨hbQ, hbFmem⟩)
  have hφb : φ (⟨ζ₁⁻¹ * (ωF : G)⁻¹ * ζ₁, hbFmem⟩ : ↥F) =
      (φ ζF)⁻¹ * (ωbar : PSU3Model n')⁻¹ * φ ζF := by
    rw [show (⟨ζ₁⁻¹ * (ωF : G)⁻¹ * ζ₁, hbFmem⟩ : ↥F) = ζF⁻¹ * ωF⁻¹ * ζF from by
      apply Subtype.ext; simp only [Subgroup.coe_mul, Subgroup.coe_inv, ζF]]
    rw [map_mul, map_mul, map_inv, map_inv, hφω]
  have hφy_eq : φ yF = φ (⟨ζ₁⁻¹ * (ωF : G)⁻¹ * ζ₁, hbFmem⟩ : ↥F) := by
    rw [hφy, hfbar, ← hφb]
  have hyF_eq : yF = ⟨ζ₁⁻¹ * (ωF : G)⁻¹ * ζ₁, hbFmem⟩ :=
    Work.PSU3.StageB.NotFpfStep2.eq_of_phi_eq_of_mem hS.split.inf_eq hφker hZtwo
      hyF_sub hb_sub hφy_eq
  have hfcan_final : (Work.PSU3.StageB.fcan hS.split ωQ : G) = ζ₁⁻¹ * (ωQ : G)⁻¹ * ζ₁ := by
    have h1 : (Work.PSU3.StageB.fcan hS.split ωQ : G) = (yF : G) := by
      rw [← hfcan_eq]
    rw [h1, congrArg Subtype.val hyF_eq]
  -- ## 7. the `h`-part
  have hzP : (zF : G) ∈ P :=
    Subgroup.mem_subgroupOf.mp
      (Work.PSU3.StageB.NotFpfStep2.center_le_P hS hC4 hHig hQ3 hW hPV hPp hyQ hy0 hyc hZV hzF)
  have hcz : (zF : G) * ζ₁ ^ 3 = ζ₁ ^ 3 * (zF : G) := by
    have h := congrArg (fun x : ↥F => (x : G)) (Subgroup.mem_center_iff.mp hzF (ζF ^ 3))
    simpa only [Subgroup.coe_mul, Subgroup.coe_pow, ζF] using h.symm
  have hhcan_final : ∃ η₂ : G, η₂ ∈ P ∧
      (Work.PSU3.StageB.hcan hS.split ωQ : G) = ζ₁ ^ 3 * η₂ :=
    ⟨(zF : G), hzP, hhcan_eq.symm.trans hcz⟩
  exact ⟨ωQ, hω0, hωFmem, hfcan_final, hhcan_final⟩

end Work.PSU3.StageB.NotFpfStep4
