import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE3.Case1aSetup
import Submission.Work.DSTR.M110.PiCoreFacts
import Submission.OddOrder.Isaacs.Ch03_SplitExtensions.Theorem315

namespace Work.CORE3

open scoped Pointwise
open Subgroup
open Work.GW2

/-! ## Support lemmas for `Work.CORE3.Case1aBFpf`

Elementary group theory needed by the Bender p. 223 fixed-point-freeness argument: the
`π`-part of the Fitting subgroup, the Sylow `p`-subgroup of a subgroup, and the fact that a
proper subgroup lies in a coatom. -/

/-- `F_π(K) ≤ F(K)`. -/
theorem bfpf_fittingPiIn_le_fittingIn {G : Type} [Group G] (π : Set ℕ) (K : Subgroup G) :
    Work.GW2.fittingPiIn π K ≤ Work.GW2.fittingIn K := by
  show ((Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)).map (Work.GW2.fitting ↥K).subtype).map
      K.subtype ≤ (Work.GW2.fitting ↥K).map K.subtype
  refine Subgroup.map_mono ?_
  have h := Subgroup.map_mono (f := (Work.GW2.fitting ↥K).subtype)
    (le_top : Work.GW2.piCore π ↥(Work.GW2.fitting ↥K) ≤ ⊤)
  rwa [Subgroup.map_top, Subgroup.range_subtype] at h

/-- The relative index of a subgroup of `B`, pushed into the ambient group, is its index in `B`. -/
theorem bfpf_relIndex_map_subtype_eq_index {G : Type} [Group G] (B : Subgroup G)
    (Q : Subgroup ↥B) : (Q.map B.subtype).relIndex B = Q.index := by
  have h1 : (Subgroup.comap B.subtype (Q.map B.subtype)).index
      = (Q.map B.subtype).relIndex B := by
    rw [Subgroup.index_comap, Subgroup.range_subtype]
  rw [Subgroup.comap_map_eq_self_of_injective B.subtype_injective Q] at h1
  exact h1.symm

/-- Every proper subgroup of a finite group is contained in a coatom. -/
theorem bfpf_exists_isCoatom_le_of_ne_top {G : Type} [Group G] [Finite G] (N : Subgroup G)
    (h : N ≠ ⊤) : ∃ M : Subgroup G, IsCoatom M ∧ N ≤ M := by
  rcases eq_top_or_exists_le_coatom N with h1 | ⟨M, hM, hN⟩
  · exact absurd h1 h
  · exact ⟨M, hM, hN⟩

/-- A Sylow `p`-subgroup of a subgroup, realized as a subgroup of the ambient group. -/
theorem bfpf_exists_pSubgroup_le_of_dvd {G : Type} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (B : Subgroup G) (h : p ∣ Nat.card B) :
    ∃ P2 : Subgroup G, P2 ≤ B ∧ IsPGroup p P2 ∧ ¬ p ∣ P2.relIndex B := by
  obtain ⟨Q⟩ := Sylow.nonempty (p := p) (G := ↥B)
  exact ⟨(Q : Subgroup ↥B).map B.subtype, Subgroup.map_subtype_le _, Q.isPGroup'.map B.subtype,
    by rw [bfpf_relIndex_map_subtype_eq_index]; exact Sylow.not_dvd_index Q⟩

/-- The image of a `π`-subgroup under an injective homomorphism is a `π`-subgroup. -/
theorem bfpf_isPiSubgroup_map_of_injective {G H : Type} [Group G] [Group H] {f : G →* H}
    (hf : Function.Injective f) {π : Set ℕ} {N : Subgroup G}
    (h : Subgroup.IsPiSubgroup π N) : Subgroup.IsPiSubgroup π (N.map f) := by
  intro p hp
  rw [Subgroup.card_map_of_injective hf] at hp
  exact h p hp

/-- `F_π(K) = O_π(F(K))` is a `π`-subgroup. -/
theorem bfpf_isPiSubgroup_fittingPiIn {G : Type} [Group G] [Finite G] (π : Set ℕ)
    (K : Subgroup G) : Subgroup.IsPiSubgroup π (Work.GW2.fittingPiIn π K) := by
  show Subgroup.IsPiSubgroup π
    (Subgroup.map K.subtype (Subgroup.map (Work.GW2.fitting ↥K).subtype
      (Work.GW2.piCore π ↥(Work.GW2.fitting ↥K))))
  rw [show Work.GW2.piCore π ↥(Work.GW2.fitting ↥K)
      = OddOrder.Isaacs.Ch03.oPiCore π ↥(Work.GW2.fitting ↥K)
      from Work.GW2.piCore_eq_oPiCore π]
  exact bfpf_isPiSubgroup_map_of_injective K.subtype_injective
    (bfpf_isPiSubgroup_map_of_injective (Work.GW2.fitting ↥K).subtype_injective
      (OddOrder.Isaacs.Ch03.oPiCore.isPiGroup π))

/-- A `π`-subgroup meets a `p`-subgroup (`p ∉ π`) trivially. -/
theorem bfpf_inf_eq_bot (π : Set ℕ) {G : Type} [Group G] [Finite G] {K M : Subgroup G}
    {p : ℕ} [Fact p.Prime] (hK : Subgroup.IsPiSubgroup π K) (hM : IsPGroup p M)
    (hp : p ∉ π) : K ⊓ M = ⊥ :=
  OddOrder.Isaacs.Ch03.Subgroup.IsPiGroup.inf_eq_bot_of_isPGroup_not_mem hK hM hp

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- Design pass 6 §3(a), `Work.CORE3.Case1aBFpfProp` (Bender 1981 p. 223): in the subcase
`Ĥ = H`, `B = C_U(S)` is fixed-point-free on `F_{3'}(U)`.  Deliverable
`Work.CORE3.Case1aBFpfProp`.

Route (`NOTES_LEAD_gw_design6.md` §3(a), step 3): for `b ∈ B#`, `N_G(⟨b⟩) ≤ M` (the last
conjunct of `hMD : Case1aMDataProp`, Bender's "`E(N_G(X))` contains and hence equals `E`
whenever `1 ≠ X ⊆ B ∩ M`", via `I.h29` and maximality of `M`); so
`C_{F_{3'}(U)}(b) ≤ F(U) ∩ M ≤ U ∩ M = P₀ × (B ∩ M)` (`hMD`), and its `3'`-part lies in
`B ∩ F(U) = 1` (`hFit : Case1aBFittingProp`).

The only `M` available in this leaf is the maximal `M ⊇ N_G(P₂)` of the §3 `M`-analysis, so
`M` and a Sylow `p`-subgroup `P₂ ≤ C_U(S)` have to be produced here: `p ∣ |C_U(S)|` follows
from `Case1aFrattiniProp` (with `P₂ = ⊥`), Sylow's theorem gives such a `P₂`, and `N_G(P₂)`
is proper because `G` is simple, so a coatom `M ⊇ N_G(P₂)` exists. -/
theorem Case1aBFpf (I : Case1Inputs) (hSetup : Case1aSetupProp) (hFr : Case1aFrattiniProp)
    (hAb : Case1aAbelianProp) (hA7 : Case1aA7Prop) (hBleM : Case1aBleMProp)
    (hFit : Case1aBFittingProp) (hMD : Case1aMDataProp) : Case1aBFpfProp := by
  intro G _instG _finG hFT hCtx B hCase hHhat b hb hbne
  classical
  obtain ⟨D⟩ := hSetup G hFT hCtx B hCase hHhat
  haveI : Fact D.p.Prime := ⟨D.hp⟩
  set Bc : Subgroup G := B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) with hBcdef
  -- ## Step 1: `p ∣ |B|`
  have hpB : D.p ∣ Nat.card (Bc : Subgroup G) := by
    by_contra hpdvd
    have hrel : ¬ D.p ∣ (⊥ : Subgroup G).relIndex Bc := by
      rwa [Subgroup.relIndex_bot_left]
    exact (hFr G hFT hCtx B hCase hHhat D ⊥ bot_le IsPGroup.of_bot hrel).2.2 rfl
  -- ## Step 2: a Sylow `p`-subgroup of `B`
  obtain ⟨P2, hP2le, hP2grp, hP2ndvd⟩ := bfpf_exists_pSubgroup_le_of_dvd D.p Bc hpB
  have hP2ne : P2 ≠ ⊥ := (hFr G hFT hCtx B hCase hHhat D P2 hP2le hP2grp hP2ndvd).2.2
  -- ## Step 3: a coatom `M ⊇ N_G(P₂)`
  haveI : IsSimpleGroup G := hCtx.simple
  have hP2Hhat : P2 ≤ B.Hhat :=
    hP2le.trans (le_trans inf_le_left (Work.CORE2A.bSetup_U_le_Hhat B))
  have hNHat_ne : Subgroup.normalizer (P2 : Set G) ≠ ⊤ := by
    intro htop
    haveI : P2.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal P2 with h | h
    · exact hP2ne h
    · rw [h] at hP2Hhat
      exact B.Hhat_coatom.ne_top (top_le_iff.mp hP2Hhat)
  obtain ⟨M, hMcoat, hNM⟩ := bfpf_exists_isCoatom_le_of_ne_top _ hNHat_ne
  -- ## Step 4: the `M`-data and the `A₇` data
  obtain ⟨hBM, _hBM', hUM, hNX⟩ :=
    hMD G hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  have hP0card : Nat.card ((Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G)) = 3 :=
    (hA7 G hFT hCtx B hCase hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM).2.2.2.2
  -- ## Step 5: `M ⊇ B` normalizes `P₀ = O_p(U) ⊓ M`, so `B ⊔ P₀ = P₀ * B` as sets
  have hSnormP0 : B.U ⊓ M ≤ Subgroup.normalizer
      ((Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    intro s hs y hy
    obtain ⟨hsU, hsM⟩ := Subgroup.mem_inf.mp hs
    obtain ⟨hyP, hyM⟩ := Subgroup.mem_inf.mp hy
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.le_normalizer_iff.mp
          ((Subgroup.le_normalizer (H := B.U)).trans (c1aLe_normalizer_pCoreIn D.p B.U))
          s hsU) y hyP,
       (Subgroup.le_normalizer_iff.mp (Subgroup.le_normalizer (H := M)) s hsM) y hyM⟩
  have hBcleP0 : Bc ≤ Subgroup.normalizer
      ((Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) : Set G) :=
    le_trans (le_inf inf_le_left hBM) hSnormP0
  -- ## Step 6: the fixed-point-freeness
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨hxF, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxFit : x ∈ Work.GW2.fittingIn B.U := bfpf_fittingPiIn_le_fittingIn _ _ hxF
  have hxU : x ∈ B.U := c1aFittingIn_le B.U hxFit
  -- `x` commutes with `b`, hence normalizes `⟨b⟩`, hence lies in `M`
  have hxb : x * b * x⁻¹ = b := by
    have h := (Subgroup.mem_centralizer_iff.mp hxC) b (Set.mem_singleton b)
    rw [← h]
    group
  have hxN : x ∈ Subgroup.normalizer ((Subgroup.zpowers b : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
    exact congrArg Subgroup.zpowers hxb
  have hzbne : Subgroup.zpowers b ≠ ⊥ :=
    fun hc => hbne (Subgroup.zpowers_eq_bot.mp hc)
  have hxM : x ∈ M := hNX _ hzbne (Subgroup.zpowers_le.mpr hb) hxN
  -- `x ∈ U ∩ M = P₀ ⊔ B`, and `P₀` is normal in `U ∩ M`, so `x = p * c` with `p ∈ P₀`, `c ∈ B`
  have hxP0B : x ∈ (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) ⊔ Bc := by
    rw [← hUM]
    exact ⟨hxU, hxM⟩
  have hxprod : x ∈ ((Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) : Set G) * (Bc : Set G) := by
    rw [← Subgroup.coe_mul_of_right_le_normalizer_left
      (Work.GW2.pCoreIn D.p B.U ⊓ M) Bc hBcleP0]
    exact hxP0B
  obtain ⟨xu, hxu, xv, hxv, hxuv⟩ := Set.mem_mul.mp hxprod
  -- `c ∈ B ∩ F(U) = 1`
  have hxuFit : xu ∈ Work.GW2.fittingIn B.U :=
    c1aPcoreIn_le_fittingIn D.p B.U (Subgroup.mem_inf.mp hxu).1
  have hxvFit : xv ∈ Work.GW2.fittingIn B.U := by
    have h : xv = xu⁻¹ * x := by rw [← hxuv]; group
    rw [h]
    exact (Work.GW2.fittingIn B.U).mul_mem ((Work.GW2.fittingIn B.U).inv_mem hxuFit) hxFit
  have hxv1 : xv = 1 := by
    have hmem : xv ∈ Bc ⊓ Work.GW2.fittingIn B.U := ⟨hxv, hxvFit⟩
    rw [show Bc ⊓ Work.GW2.fittingIn B.U = ⊥ from by
      rw [hBcdef]; exact hFit G hFT hCtx B hCase hHhat] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hxP0 : x ∈ (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) := by
    have h : x = xu := by rw [← hxuv, hxv1, mul_one]
    rw [h]
    exact hxu
  -- `P₀` has order `3` and `F_{3'}(U)` is a `3'`-group, so `P₀ ⊓ F_{3'}(U) = ⊥`
  have hP0isP : IsPGroup 3 ((Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [hP0card]
    norm_num
  have hinf := bfpf_inf_eq_bot ({3}ᶜ : Set ℕ)
    (K := Work.GW2.fittingPiIn ({3}ᶜ : Set ℕ) B.U)
    (M := (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G)) (p := 3)
    (bfpf_isPiSubgroup_fittingPiIn _ _) hP0isP (by decide)
  have hbot : x ∈ (⊥ : Subgroup G) := by
    rw [← hinf]
    exact ⟨hxF, hxP0⟩
  exact Subgroup.mem_bot.mp hbot

end Work.CORE3

open Work.GW2

/-- The same lemma, mirrored at the namespace of the file path, so that it can be cited both as
`Work.CORE3.Case1aBFpf` (the name the area requests) and as
`Work.CORE3.Work.CORE3.Case1aBFpf` (the skeleton's namespace layout). -/
theorem Case1aBFpf (I : Case1Inputs) (hSetup : Case1aSetupProp) (hFr : Case1aFrattiniProp)
    (hAb : Case1aAbelianProp) (hA7 : Case1aA7Prop) (hBleM : Case1aBleMProp)
    (hFit : Case1aBFittingProp) (hMD : Case1aMDataProp) : Case1aBFpfProp :=
  _root_.Work.CORE3.Work.CORE3.Case1aBFpf I hSetup hFr hAb hA7 hBleM hFit hMD

end Work.CORE3
