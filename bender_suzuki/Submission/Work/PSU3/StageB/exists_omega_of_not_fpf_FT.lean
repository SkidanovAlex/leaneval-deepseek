import Mathlib
import Submission.Work.PSU3.Defs
import Submission.Work.ThmF.Setup
import Submission.Work.Higman.Main
import Submission.Work.PSU3.StageB.Step1
import Submission.Work.PSU3.StageB.NotFpfAux
import Submission.Work.PSU3.StageB.Frame
import Submission.Work.PSU3.StageA.coarseFrame_exists
import Submission.Work.PSU3.Model.psu3_cor2
import Submission.Work.PSU3.StageA.caseC_data
import Submission.Work.PSU3.StageA.caseC_setup
import Submission.Work.PSU3.StageA.caseC_general
import Submission.Work.PSU3.StageA.caseC_st_structure
import Submission.Work.PSU3.StageA.distinguished_exists
import Submission.Work.PSU3.StageB.NotFpfStep2.cW_ne_bot
import Submission.Work.PSU3.StageB.NotFpfStep2.center_le_P
import Submission.Work.PSU3.StageB.NotFpfStep2.center_le_centD
import Submission.Work.PSU3.StageB.NotFpfStep2.quot_isPSU3
import Submission.Work.PSU3.StageB.NotFpfStep2.relative_splitRankOne
import Submission.Work.PSU3.StageB.NotFpfStep4.exists_good_zeta_PSU3
import Submission.Work.PSU3.Model.psu3_datum
import Submission.Work.PSU3.StageB.NotFpfStep4.hcan_mem_W_of_step4
import Submission.Work.PSU3.StageB.NotFpfStep4.transfer_cor2_step4
import Submission.Work.PSU3.StageB.NotFpfStep4.coarseFrame_bar_renorm
import Submission.Work.PSU3.StageB.NotFpfStep4.card_Q0sub_eq_two_pow_of_frame
import Submission.Work.PSU3.StageB.Omega.omegaHyp_of_sq
import Submission.Work.PSU3.StageB.Omega.exists_zcQF_eq_of_mem_Q0
import Submission.Work.PSU3.RankOne.canon_transport
import Submission.Work.PSU3.RankOne.canon_conj
import Submission.Work.Models.Abstract.exists_conj_eq
import Submission.Work.PSU3.StageB.isSplitRankOne_map_of_surjective
import Submission.Work.PSU3.StageA.caseC_frame_core
import Submission.Work.PSU3.StageB.Wiring
import Submission.Work.ThmF.ChV12.KsubSubgroupOfNormal

-- ftport:v435-opts-begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- ftport:v435-opts-end

set_option autoImplicit false
set_option linter.unusedVariables false

namespace Work.PSU3.StageB

open LeanEval.GroupTheory.Defs

/-
# Stage B, node **B2** in the `ft` form (`exists_omega_of_not_fpf_FT`)

Peterfalvi II, Ch. VII §4 (pp. 278–280), the `V ≠ W` case.

## The route

1. **Step 1** (`Work.PSU3.StageB.exists_prime_order_le_centD_centralizing`): `¬ DFpfBar H Q t`
   yields a prime-order `P ≤ V = centD H t` and `y ∈ Q ∖ Q₀` centralised by `P`.
2. **Case (c)**: a coarse frame gives `W H t ≠ ⊥`, whence `orderOf (s * t) = 3`,
   `t s t = s t s` and `|Q| = |Q₀sub H|³`.
3. **`Z(U) ≤ V`** for `U = O^{2'}(C_G(P))` (`NotFpfStep2.center_le_centD`, `center_le_P`).
4. **§4 (1)** (`NotFpfStep2.quot_isPSU3`): `U/Z(U) ≅ PSU(3, 2ⁿ')`, `n' ≥ 2`.
5. **§4 (2), first half** (`NotFpfStep2.exists_good_zeta_rel`): `ζ₁ ∈ (V ∩ U) ∖ P`,
   `ζ ∈ C_W(P)^#` with `ζ⁻¹ ζ₁ ∈ P`.
6. **§4 (2), second half** (`NotFpfStep4.transfer_cor2_step4`, via
   `NotFpfStep4.psu3_cor2_datum`): `ω ∈ (Q ∖ Q₀) ∩ U` with `f(ω) = ζ₁⁻¹ ω⁻¹ ζ₁` and
   `h(ω) ∈ ζ₁³ P`.
7. **The frame**: `coarseFrame_exists` at `ζ`, renormalised (`NotFpfStep4.coarseFrame_bar_renorm`)
   so that `bar y = ofAdd 1`; this is the `hη1` input of `etaAction_semilinear`, with `s := y`.
8. **§4 (3)–(10)** (`NotFpfStep4.hcan_mem_W_of_step4`): `h(ω) ∈ W H t`.
9. **`OmegaHyp`**: `Work.PSU3.StageB.Omega.omegaHyp_of_sq`.
-/

/-! ## Auxiliary facts about case (c) -/

/-- In case (c) (`|Q| = |Q₀sub H|³`), every square in `Q` lies in `Q₀sub H`: `Q` is a Suzuki
`2`-group (`caseC_isSuzuki2Grp`), Higman's theorem makes every square central, and the centre of
`Q` is `Q₀sub H` (`caseC_center_subgroupOf`). -/
theorem sq_mem_Q0sub_of_caseC {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) (hWne : Work.ThmF.W H t ≠ ⊥) :
    ∀ x : ↥Q, ((x * x : ↥Q) : G) ∈ Work.ThmF.Q0sub H := by
  have hnab : ¬ Submission.Blueprint.IsAbelianSubgroup Q :=
    Work.PSU3.StageA.not_abelian_of_W_ne_bot hS hC4 hWne
  have hZ : ∀ x : ↥Q, (x : G) ∈ Work.ThmF.Q0sub H ↔ x * x = 1 :=
    Work.PSU3.StageA.caseC_Q0sub_subgroupOf_iff_sq hS hC4
  have hSuz2 : Work.Higman.IsSuzuki2Grp ↥Q :=
    Work.PSU3.StageA.caseC_isSuzuki2Grp hS hC4 hnab hZ hWne
  have hSuz : Submission.Blueprint.IsSuzukiTwoGroup ↥Q :=
    Work.Higman.isSuzukiTwoGroup_iff_nonempty_isSuzuki2Grp.mpr ⟨hSuz2⟩
  have hsq : ∀ x : ↥Q, x ^ 2 ∈ Subgroup.center ↥Q := (hHig ↥Q hSuz).2.1
  have hc : Subgroup.center ↥Q = (Work.ThmF.Q0sub H).subgroupOf Q :=
    Work.PSU3.StageA.caseC_center_subgroupOf hS hHig hZ hSuz2
  intro x
  have h : x ^ 2 ∈ (Work.ThmF.Q0sub H).subgroupOf Q := by rw [← hc]; exact hsq x
  have h2 := Subgroup.mem_subgroupOf.mp h
  simpa [Subgroup.coe_pow, pow_two] using h2

/-- For a coarse frame, `KW = Ksub H t · ⟨ζ⟩`: this is `KW_gen` (every `d ∈ KW` is `k · ζ^j` with
`(k : G) ∈ Ksub H t`) together with `K_le` (`Ksub ≤ KW`) and `ζ ∈ KW`. -/
theorem KW_eq_Ksub_sup {G : Type} [Group G] {H Q : Subgroup G} {t : G} {n : ℕ}
    (fr : CoarseFrame H Q t n) :
    fr.KW = Work.ThmF.Ksub H t ⊔ Subgroup.zpowers (fr.ζ : G) := by
  refine le_antisymm ?_ (sup_le fr.K_le (Subgroup.zpowers_le.mpr fr.ζ.2))
  intro d hd
  obtain ⟨k, hk, j, hdj⟩ := fr.KW_gen ⟨d, hd⟩
  have hval : d = (k : G) * (fr.ζ : G) ^ j := by
    have h := congrArg (fun z : fr.KW => (z : G)) hdj
    simpa using h
  rw [hval]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk)
    (Subgroup.mem_sup_right ((Subgroup.zpowers (fr.ζ : G)).pow_mem
      (Subgroup.mem_zpowers (fr.ζ : G)) j))

/-- `KW` is invariant under conjugation by `η ∈ V = centD H t` provided `η` centralises `ζ`:
`KW = Ksub ⊔ ⟨ζ⟩`, `Ksub ◁ D = twoPoint H t` (case (c): `Ksub H t = Kset H t`,
`ChV12.KsubSubgroupOfNormal`) and `⟨ζ⟩` is invariant. -/
theorem conj_mem_KW_of_mem_centD {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    {n : ℕ} (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (fr : CoarseFrame H Q t n) {η : G} (hηV : η ∈ Submission.Blueprint.centD H t)
    (hηζ : η⁻¹ * (fr.ζ : G) * η = (fr.ζ : G)) :
    ∀ d : fr.KW, ∃ e : fr.KW, (e : G) = η⁻¹ * (d : G) * η := by
  have hWne : Work.ThmF.W H t ≠ ⊥ := by
    intro h
    exact fr.ζ_ne_one (Subtype.coe_injective (Subgroup.mem_bot.mp (by rw [← h]; exact fr.ζ_mem_W)))
  have hKsub : (Work.ThmF.Ksub H t : Set G) = Work.ThmF.Kset H t :=
    (Work.PSU3.StageA.caseC_Ksub_cyc hS hC4 hWne).1
  have hKn : ((Work.ThmF.Ksub H t).subgroupOf (Submission.Blueprint.twoPoint H t)).Normal :=
    Work.ThmF.ChV12.KsubSubgroupOfNormal hS.split hKsub
  have hηD : η ∈ Submission.Blueprint.twoPoint H t :=
    Work.ThmF.centD_le_twoPoint (H := H) t hηV
  intro d
  obtain ⟨k, hk, j, hdj⟩ := fr.KW_gen d
  have hkD : (k : G) ∈ Submission.Blueprint.twoPoint H t :=
    Work.ThmF.Ksub_le_twoPoint (H := H) t hk
  have hconj : (⟨η, hηD⟩ : ↥(Submission.Blueprint.twoPoint H t))⁻¹ * ⟨(k : G), hkD⟩ *
      ⟨η, hηD⟩ ∈ (Work.ThmF.Ksub H t).subgroupOf (Submission.Blueprint.twoPoint H t) := by
    simpa using hKn.conj_mem (⟨(k : G), hkD⟩ : ↥(Submission.Blueprint.twoPoint H t))
      (Subgroup.mem_subgroupOf.mpr hk) (⟨η, hηD⟩ : ↥(Submission.Blueprint.twoPoint H t))⁻¹
  have hk'K : (η⁻¹ * (k : G) * η) ∈ Work.ThmF.Ksub H t := by
    have h := Subgroup.mem_subgroupOf.mp hconj
    simpa using h
  have hval : d = (k : G) * (fr.ζ : G) ^ j := by
    have h := congrArg (fun z : fr.KW => (z : G)) hdj
    simpa using h
  refine ⟨⟨η⁻¹ * (k : G) * η, fr.K_le hk'K⟩ * fr.ζ ^ j, ?_⟩
  have hcoe : ((⟨η⁻¹ * (k : G) * η, fr.K_le hk'K⟩ * fr.ζ ^ j : fr.KW) : G)
      = (η⁻¹ * (k : G) * η) * (fr.ζ : G) ^ j := by
    simp only [Subgroup.coe_mul, Subgroup.coe_pow]
  have hζcomm : η * (fr.ζ : G) = (fr.ζ : G) * η := by
    have h1 : (fr.ζ : G) = η * (fr.ζ : G) * η⁻¹ := by
      calc (fr.ζ : G) = η * (η⁻¹ * (fr.ζ : G) * η) * η⁻¹ := by group
        _ = η * (fr.ζ : G) * η⁻¹ := by rw [hηζ]
    calc η * (fr.ζ : G) = (η * (fr.ζ : G) * η⁻¹) * η := by group
      _ = (fr.ζ : G) * η := by rw [← h1]
  have hpow : ∀ m : ℕ, η * (fr.ζ : G) ^ m = (fr.ζ : G) ^ m * η :=
    fun m => (show Commute η (fr.ζ : G) from hζcomm).pow_right m
  rw [hcoe, hval]
  calc (η⁻¹ * (k : G) * η) * (fr.ζ : G) ^ j
      = η⁻¹ * (k : G) * (η * (fr.ζ : G) ^ j) := by group
    _ = η⁻¹ * (k : G) * ((fr.ζ : G) ^ j * η) := by rw [hpow j]
    _ = η⁻¹ * ((k : G) * (fr.ζ : G) ^ j) * η := by group

/-! ## The main theorem -/

/-- **Stage B, node B2** (Peterfalvi II Ch. VII §4): in the non-fixed-point-free case there is a
coarse frame `fr'` at the *same* index `n` and an `ω` with `OmegaHyp fr' ω`. -/
theorem exists_omega_of_not_fpf_FT {G : Type} [Group G] [Finite G] {H Q : Subgroup G} {t : G}
    (hS : Work.PSU3.PSU3Hyp H Q t) (hC4 : Submission.Blueprint.ChIIFourProp)
    (hHig : Submission.Blueprint.HigmanProp) {n : ℕ} (fr : Work.PSU3.CoarseFrame H Q t n)
    (hnfpf : ¬ Work.PSU3.DFpfBar H Q t) :
    ∃ fr' : Work.PSU3.CoarseFrame H Q t n, ∃ ω : G, Work.PSU3.OmegaHyp fr' ω := by
  -- ## Step 1: a prime-order `P ≤ V` centralising some `y ∈ Q ∖ Q₀`
  obtain ⟨P, hPV, hPp, y, hyQ, hy0, hyc⟩ :=
    Work.PSU3.StageB.exists_prime_order_le_centD_centralizing hS hC4 fr hnfpf
  have hPne : P ≠ ⊥ := fun hb => by
    rw [hb, Subgroup.card_bot] at hPp
    exact Nat.not_prime_one hPp
  have hy0sub : y ∉ Work.ThmF.Q0sub H := by
    rwa [← Work.PSU3.StageB.frameQ0_eq_Q0sub hS fr]
  -- ## case (c)
  have hWne : Work.ThmF.W H t ≠ ⊥ := Work.PSU3.StageB.NotFpfStep2.W_ne_bot_of_frame hS fr
  obtain ⟨s, hsQ, hs2, r, hrQ, hsr⟩ := Work.PSU3.StageA.distinguished_exists hS
  have hQ3 : Nat.card Q = Nat.card (Work.ThmF.Q0sub H) ^ 3 :=
    (Work.PSU3.StageA.caseC_data_of_W_ne_bot hS hC4 hHig hsQ hs2 hrQ hsr hWne).1
  have hst : t * s * t = s * t * s :=
    Work.PSU3.StageA.caseC_st_structure hS hC4 hHig hsQ hs2 hrQ hsr hWne hQ3
  -- ## `Z(U) ≤ V` for `U = O^{2'}(C_G(P))`
  have hZV := Work.PSU3.StageB.NotFpfStep2.center_le_centD hS hC4 hPV hPp hyQ hy0sub hyc
  -- ## §4 (2), first half: `ζ₁ ∈ (V ∩ U) ∖ P` and `ζ ∈ C_W(P)^#` with `ζ⁻¹ ζ₁ ∈ P`
  obtain ⟨ζ₁, hζ₁V, hζ₁U, hζ₁cent, hζ₁notP, ζ, hζW, hζ1, hζcent, hζζ₁P⟩ :=
    Work.PSU3.StageB.NotFpfStep4.exists_good_zeta_PSU3 hS hC4 hHig hQ3 hWne hPV hPp hPne hyQ
      hy0sub hyc hZV
  have hZP : (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)).map
      (Work.PSU3.StageB.centralizerOddResidual P).subtype ≤ P := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hz
    exact Subgroup.mem_subgroupOf.mp
      (Work.PSU3.StageB.NotFpfStep2.center_le_P hS hC4 hHig hQ3 hWne hPV hPp hyQ hy0sub hyc hZV hw)
  have hζ₁nZ : ζ₁ ∉ (Subgroup.center ↥(Work.PSU3.StageB.centralizerOddResidual P)).map
      (Work.PSU3.StageB.centralizerOddResidual P).subtype := fun h => hζ₁notP (hZP h)
  -- ## §4 (2), second half: Cor. 2 of the §3 Proposition, transported and lifted
  obtain ⟨ω, hω0, hωF, hfcan, η₂, hη₂P, hhcan⟩ :=
    Work.PSU3.StageB.NotFpfStep4.transfer_cor2_step4 hS hC4 hHig hQ3 hWne hPV hPp hPne hyQ hy0sub
      hyc hZV hζ₁V hζ₁U hζ₁nZ
  -- ## `ζ₁ = ζ p` with `p ∈ P`
  obtain ⟨p, hpP, hp_eq⟩ : ∃ p : G, p ∈ P ∧ ζ⁻¹ * ζ₁ = p := ⟨ζ⁻¹ * ζ₁, hζζ₁P, rfl⟩
  have hζ₁_eq : ζ₁ = ζ * p := by rw [← hp_eq]; group
  have hpζ : p * ζ = ζ * p := by
    have h : p * (p⁻¹ * ζ * p) = p * ζ := congrArg (fun z : G => p * z) (hζcent p hpP)
    have h2 : ζ * p = p * ζ := by rw [← h]; group
    exact h2.symm
  have hpω : p * (ω : G) = (ω : G) * p := by
    have hωC : (ω : G) ∈ Subgroup.centralizer (P : Set G) :=
      Work.PSU3.StageB.NotFpfStep2.centralizerOddResidual_le_centralizer P hωF
    exact Subgroup.mem_centralizer_iff.mp hωC p hpP
  set η : G := (p ^ 3 * η₂)⁻¹ with hηdef
  have hηP : η ∈ P := P.inv_mem (P.mul_mem (P.pow_mem hpP 3) hη₂P)
  have hηV : η ∈ Submission.Blueprint.centD H t := hPV hηP
  -- ## the new frame at `ζ`
  obtain ⟨n'', hn''2, hcard'', fr₀, hfr₀zc, hfr₀ζ⟩ :=
    Work.PSU3.StageA.coarseFrame_exists hS hC4 hHig hsQ hs2 hrQ hsr hst hQ3 hζW hζ1
  have hcardn : Nat.card (Work.ThmF.Q0sub H) = 2 ^ n :=
    Work.PSU3.StageB.NotFpfStep4.card_Q0sub_eq_two_pow_of_frame hS fr
  have hn'' : n'' = n := Nat.pow_right_injective (le_refl 2) (hcard''.symm.trans hcardn)
  subst n''
  -- renormalise `bar` so that `bar y = ofAdd 1`
  have hy0fr : y ∉ fr₀.Q0 := by
    rw [Work.PSU3.StageB.frameQ0_eq_Q0sub hS fr₀]; exact hy0sub
  have hbarne : fr₀.bar ⟨y, hyQ⟩ ≠ 1 :=
    Work.PSU3.StageB.bar_ne_one_of_not_mem_Q0 fr₀ hy0fr
  have hnonzero : Multiplicative.toAdd (fr₀.bar ⟨y, hyQ⟩) ≠ 0 := fun h =>
    hbarne (Multiplicative.toAdd.injective (by rw [h, toAdd_one]))
  set c : (Work.PSU3.E n)ˣ :=
    Units.mk0 (Multiplicative.toAdd (fr₀.bar ⟨y, hyQ⟩))⁻¹ (inv_ne_zero hnonzero) with hcdef
  obtain ⟨fr', hbar', hQ0', hKW', hζ'⟩ :=
    Work.PSU3.StageB.NotFpfStep4.coarseFrame_bar_renorm H Q t fr₀ c
  have hfr'ζ : (fr'.ζ : G) = ζ := by rw [hζ', hfr₀ζ]
  have hh : (Work.PSU3.StageB.hcan hS.split ω : G) = (fr'.ζ : G) ^ 3 * η⁻¹ := by
    rw [hfr'ζ]
    rw [hhcan, hζ₁_eq]
    have h3 : (ζ * p) ^ 3 = ζ ^ 3 * p ^ 3 := (show Commute ζ p from hpζ.symm).mul_pow 3
    have hηinv : η⁻¹ = p ^ 3 * η₂ := by rw [hηdef, inv_inv]
    rw [h3, hηinv]
    group
  have hfr'Q0 : fr'.Q0 = Work.ThmF.Q0sub H := by
    rw [hQ0', Work.PSU3.StageB.frameQ0_eq_Q0sub hS fr₀]
  have hbary : Multiplicative.toAdd (fr'.bar ⟨y, hyQ⟩) = 1 := by
    rw [hbar']
    show ((Units.mk0 (Multiplicative.toAdd (fr₀.bar ⟨y, hyQ⟩))⁻¹
      (inv_ne_zero hnonzero) : (Work.PSU3.E n)ˣ) : Work.PSU3.E n) *
        Multiplicative.toAdd (fr₀.bar ⟨y, hyQ⟩) = 1
    rw [Units.val_mk0, inv_mul_cancel₀ hnonzero]
  have hω' : (ω : G) ∉ fr'.Q0 := by rw [hfr'Q0]; exact hω0
  -- ## `α` with `ω * ω = zcQF fr' α`
  have hsqmem : ((ω * ω : ↥Q) : G) ∈ fr'.Q0 := by
    rw [hfr'Q0]; exact sq_mem_Q0sub_of_caseC hS hC4 hHig hWne ω
  obtain ⟨yy, hyyfix, hyyzc⟩ := fr'.zc_surj ((ω * ω : ↥Q) : G) hsqmem
  have hyy0 : yy ≠ 0 := by
    intro h0
    refine hω0 ?_
    refine (Work.PSU3.StageA.caseC_Q0sub_subgroupOf_iff_sq hS hC4 ω).mpr ?_
    have h1 : fr'.zc yy = 1 := by rw [h0, Work.PSU3.StageB.zc_zero]
    rw [hyyzc] at h1
    exact Subtype.ext h1
  set α : ↥(Work.PSU3.StageB.FX n) := ⟨Units.mk0 yy hyy0, hyyfix⟩ with hαdef
  have hαval : Work.PSU3.StageB.fval α = yy := rfl
  have hzc : ((Work.PSU3.StageB.zcQF fr' α : ↥Q) : G) = (ω : G) * (ω : G) := by
    rw [Work.PSU3.StageB.zcQF_coe, hαval, hyyzc, Subgroup.coe_mul]
  have hsq : ω * ω = Work.PSU3.StageB.zcQF fr' α := by
    apply Subtype.ext
    rw [hzc, Subgroup.coe_mul]
  -- ## `hf`: the good form of `f(ω)`
  have hf : Work.PSU3.StageB.fcan hS.split ω =
      Work.PSU3.StageB.qconj hS.split (Work.PSU3.StageB.zetaD fr')
        (ω * Work.PSU3.StageB.zcQF fr' α) := by
    apply Subtype.ext
    rw [Work.PSU3.StageB.qconj_coe]
    have hzetaD : ((Work.PSU3.StageB.zetaD fr' :
        ↥(Submission.Blueprint.twoPoint H t)) : G) = ζ := hfr'ζ
    have hinv : (ω : G) * ((Work.PSU3.StageB.zcQF fr' α : ↥Q) : G) = (ω : G)⁻¹ :=
      (Work.PSU3.StageB.Omega.inv_eq_mul_zcQF_of_sq fr' hsq).symm
    have hcomm : ζ₁⁻¹ * (ω : G)⁻¹ * ζ₁ = ζ⁻¹ * (ω : G)⁻¹ * ζ := by
      have hp_inv_mul : p⁻¹ * (ω : G)⁻¹ = (ω : G)⁻¹ * p⁻¹ := by
        rw [← mul_inv_rev, ← hpω, mul_inv_rev]
      have hpζ_inv : p⁻¹ * ζ⁻¹ = ζ⁻¹ * p⁻¹ := by
        rw [← mul_inv_rev, ← hpζ, mul_inv_rev]
      rw [hζ₁_eq, mul_inv_rev]
      calc (p⁻¹ * ζ⁻¹) * (ω : G)⁻¹ * (ζ * p)
          = ζ⁻¹ * (p⁻¹ * (ω : G)⁻¹) * (ζ * p) := by rw [hpζ_inv]; simp only [mul_assoc]
        _ = ζ⁻¹ * ((ω : G)⁻¹ * p⁻¹) * (ζ * p) := by rw [hp_inv_mul]
        _ = ζ⁻¹ * (ω : G)⁻¹ * (p⁻¹ * ζ * p) := by simp only [mul_assoc]
        _ = ζ⁻¹ * (ω : G)⁻¹ * ζ := by rw [hζcent p hpP]
    rw [hzetaD, Subgroup.coe_mul, hinv, hfcan, hcomm]
  -- ## the `η`-clauses
  have hcentω : η * (ω : G) = (ω : G) * η := by
    have hωC : (ω : G) ∈ Subgroup.centralizer (P : Set G) :=
      Work.PSU3.StageB.NotFpfStep2.centralizerOddResidual_le_centralizer P hωF
    exact Subgroup.mem_centralizer_iff.mp hωC η hηP
  have hcentζ : η * (fr'.ζ : G) = (fr'.ζ : G) * η := by
    rw [hfr'ζ]
    have h := hζcent η hηP
    have h2 : ζ = η * ζ * η⁻¹ := by
      calc ζ = η * (η⁻¹ * ζ * η) * η⁻¹ := by group
        _ = η * ζ * η⁻¹ := by rw [h]
    calc η * ζ = (η * ζ * η⁻¹) * η := by group
      _ = ζ * η := by rw [← h2]
  have hηN := conj_mem_KW_of_mem_centD hS hC4 fr' hηV (by
    calc η⁻¹ * (fr'.ζ : G) * η = η⁻¹ * ((fr'.ζ : G) * η) := by rw [mul_assoc]
      _ = η⁻¹ * (η * (fr'.ζ : G)) := by rw [hcentζ]
      _ = (fr'.ζ : G) := by group)
  have hη1 : ∃ s : ↥Q, (s : G) ∉ fr'.Q0 ∧ Multiplicative.toAdd (fr'.bar s) = 1 ∧
      ((Work.PSU3.StageB.qconj hS.split
          (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ :
            ↥(Submission.Blueprint.twoPoint H t)) s * s⁻¹ : ↥Q) : G) ∈ fr'.Q0 := by
    refine ⟨⟨y, hyQ⟩, ?_, hbary, ?_⟩
    · rw [hfr'Q0]; exact hy0sub
    · have hconj : Work.PSU3.StageB.qconj hS.split
          (⟨η, Work.ThmF.centD_le_twoPoint (H := H) t hηV⟩ :
            ↥(Submission.Blueprint.twoPoint H t)) ⟨y, hyQ⟩ = ⟨y, hyQ⟩ := by
        apply Subtype.ext
        rw [Work.PSU3.StageB.qconj_coe]
        exact hyc η hηP
      rw [hconj, mul_inv_cancel, hfr'Q0]
      exact Work.ThmF.Q0_le_Q0sub H (Work.ThmF.one_mem_Q0 H)
  -- ## §4 (3)–(10) and `OmegaHyp`
  have hhW := Work.PSU3.StageB.NotFpfStep4.hcan_mem_W_of_step4 hS fr' hPV hω' hf hsq hηP hηV
    hh hcentω hcentζ hηN hη1
  exact ⟨fr', (ω : G), Work.PSU3.StageB.Omega.omegaHyp_of_sq hS fr' hω' hf hsq hhW⟩

end Work.PSU3.StageB
