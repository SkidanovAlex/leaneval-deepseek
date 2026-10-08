import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE2A.Basic
import Submission.Work.CORE2A.dihOrCycSylow_subgroup
import Submission.Work.CORE3.Case1aBFpf
import Submission.Work.CORE3.QuasisimpleCentralizesOddNormal
import Submission.Work.ASM.oddCore_odd

namespace Work.CORE3

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- Design pass 6 §3(a), `Work.CORE3.Case1aBFittingProp` (Bender 1981 p. 223): in the subcase
`Ĥ = H`, `B ∩ F(U) = 1` for `B = C_U(S)`.  Deliverable `Work.CORE3.Case1aBFittingProp`.

Route: `O(M) = B ∩ M` centralizes `E = E(M)` (`E ∩ O(M)` is a proper normal subgroup of the
quasisimple `E`, hence central; the three-subgroup argument with `E = E'` gives `[E, O(M)] = 1`).
If `1 ≠ Y := B ∩ F(U)`, then `Y ≤ B ≤ M` is odd, so `Y ≤ O(M)`, and
`E ≤ C_G(Y) ≤ N_G(Y) ≤ H` (Case (1), since `Y ≤ F(U)`); but `t ∈ E` and `E ≤ H = C(t)` force
`t ∈ Z(E)`, contradicting `Z(E)` odd (`I.T.lay : LayerProp` applied to the D-group `M`, which is
a coatom, using `BenderCtx.ih`).

Inputs: `hSetup` (for `D`), `hFr`, `hAb`, `hA7`, and `hMD : Case1aMDataProp` (the §3
`M`-analysis `B ≤ M`, `B ∩ M = O(M)`, `U ∩ M = P₀ ⊔ (B ∩ M)`, `N_G(X) ≤ M` for `1 ≠ X ≤ B`). -/
theorem Case1aBFitting (I : Case1Inputs) (hSetup : Case1aSetupProp) (hFr : Case1aFrattiniProp)
    (hAb : Case1aAbelianProp) (hA7 : Case1aA7Prop) (hMD : Case1aMDataProp) :
    Case1aBFittingProp := by
  intro G _instG _finG hFT hCtx B hCase hH
  classical
  -- ## Step 1: the §3 setup: `D : Case1aData B`, a Sylow `p`-subgroup `P₂ ≤ B = C_U(S)`, and a
  -- maximal subgroup `M ⊇ N_G(P₂)`.
  obtain ⟨D⟩ := hSetup G hFT hCtx B hCase hH
  haveI : Fact D.p.Prime := ⟨D.hp⟩
  set Bc : Subgroup G := B.U ⊓ Subgroup.centralizer ((B.S : Subgroup G) : Set G) with hBcdef
  have hpB : D.p ∣ Nat.card Bc := by
    by_contra hpdvd
    have hrel : ¬ D.p ∣ (⊥ : Subgroup G).relIndex Bc := by
      rwa [Subgroup.relIndex_bot_left]
    exact (hFr G hFT hCtx B hCase hH D ⊥ bot_le IsPGroup.of_bot hrel).2.2 rfl
  obtain ⟨P2, hP2le, hP2grp, hP2ndvd⟩ := bfpf_exists_pSubgroup_le_of_dvd D.p Bc hpB
  have hP2ne : P2 ≠ ⊥ := (hFr G hFT hCtx B hCase hH D P2 hP2le hP2grp hP2ndvd).2.2
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
  -- ## Step 2: the §3 `M`-data (`hMD`) and the `A₇`-data (`hA7`)
  obtain ⟨hBM, hBcM, hUM, hNX⟩ :=
    hMD G hFT hCtx B hCase hH D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  obtain ⟨hSM, ht_layer_sup, hEiso, hScard, hP0card⟩ :=
    hA7 G hFT hCtx B hCase hH D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  -- ## Step 3: `M` is a `D`-group (a coatom, so `BenderCtx.ih` applies), and `E(M) ≠ 1`
  have hdihM : DihOrCycSylow ↥M := Work.CORE2A.dihOrCycSylow_subgroup hCtx.sylow M
  have hDM : IsDGroup ↥M :=
    hCtx.ih ↥M (Subgroup.card_lt_card_of_ne_top hMcoat.ne_top) hdihM
  have hmem_sup : B.t ∈ (Subgroup.zpowers B.t ⊔ Subgroup.zpowers D.t2 : Subgroup G) :=
    (le_sup_left : Subgroup.zpowers B.t ≤
      Subgroup.zpowers B.t ⊔ Subgroup.zpowers D.t2) (Subgroup.mem_zpowers B.t)
  have ht_layer : B.t ∈ Work.GW2.layerIn M := ht_layer_sup hmem_sup
  have hlayerIn_ne : Work.GW2.layerIn M ≠ ⊥ := by
    intro hbot
    rw [hbot] at ht_layer
    exact Work.CORE2A.bSetup_t_ne_one B (Subgroup.mem_bot.mp ht_layer)
  have hlayer_ne : Work.GW2.layer ↥M ≠ ⊥ := by
    intro hbot
    refine hlayerIn_ne ?_
    show (Work.GW2.layer ↥M).map M.subtype = ⊥
    rw [hbot, Subgroup.map_bot]
  -- a normal quasisimple subgroup `E₀ ≤ M` exists
  have hex : ∃ E₀ : Subgroup ↥M, E₀.Normal ∧ IsQuasisimple E₀ := by
    by_contra h
    push_neg at h
    refine hlayer_ne ?_
    rw [Work.GW2.layer]
    exact le_antisymm (sSup_le fun E hE => (h E hE.1 hE.2).elim) bot_le
  obtain ⟨E₀, hE₀n, hE₀q⟩ := hex
  -- `LayerProp` for the `D`-group `M`: `E(M) = E₀` and `Z(E₀)` is odd
  obtain ⟨hlayer_eq, hZodd₀, -⟩ := I.T.lay ↥M hFT hdihM hDM E₀ hE₀n hE₀q
  have hEeq : Work.GW2.layerIn M = E₀.map M.subtype := by
    show (Work.GW2.layer ↥M).map M.subtype = E₀.map M.subtype
    rw [hlayer_eq]
  have htE' : B.t ∈ E₀.map M.subtype := by
    rw [← hEeq]
    exact ht_layer
  -- ## Step 4: transport the layer data along `M ↪ G`
  set he : ↥E₀ ≃* ↥(E₀.map M.subtype) :=
    Subgroup.equivMapOfInjective E₀ M.subtype M.subtype_injective with hedef
  have hmapcen : Subgroup.map he (Subgroup.center ↥E₀) = Subgroup.center ↥(E₀.map M.subtype) :=
    Subgroup.map_center_eq he
  have hcardcen : Nat.card (Subgroup.center ↥(E₀.map M.subtype)) =
      Nat.card (Subgroup.center ↥E₀) := by
    rw [← hmapcen]
    exact Subgroup.card_map_of_injective he.injective
  have hcodd : Odd (Nat.card (Subgroup.center ↥(E₀.map M.subtype))) := hcardcen ▸ hZodd₀
  have hqcard : Nat.card (↥E₀ ⧸ Subgroup.center ↥E₀) =
      Nat.card (↥(E₀.map M.subtype) ⧸ Subgroup.center ↥(E₀.map M.subtype)) :=
    Nat.card_congr (QuotientGroup.congr (Subgroup.center ↥E₀)
      (Subgroup.center ↥(E₀.map M.subtype)) he hmapcen).toEquiv
  -- `E/Z(E)` has even order: it is isomorphic to `A₇`
  have hEeven : Even (Nat.card (↥E₀ ⧸ Subgroup.center ↥E₀)) := by
    rw [hqcard, ← hEeq]
    obtain ⟨e⟩ := hEiso
    rw [Nat.card_congr e.toEquiv, I.T.a7.1]
    norm_num
  -- ## Step 5: `E(M)` centralizes `O(M)`
  have hcomm0 : ⁅E₀, Work.GW2.oddCore ↥M⁆ = ⊥ :=
    QuasisimpleCentralizesOddNormal hE₀n hE₀q (Work.GW2.oddCore_normal ↥M)
      (Work.ASM.oddCore_odd ↥M) hEeven
  have hcomm : ⁅E₀.map M.subtype, Work.GW2.oddCoreIn M⁆ = ⊥ := by
    show ⁅E₀.map M.subtype, (Work.GW2.oddCore ↥M).map M.subtype⁆ = ⊥
    rw [← Subgroup.map_commutator E₀ (Work.GW2.oddCore ↥M) M.subtype, hcomm0,
      Subgroup.map_bot]
  -- ## Step 6: `B ∩ F(U) = 1`
  have hYbot : Bc ⊓ Work.GW2.fittingIn B.U = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    have hYne : Bc ⊓ Work.GW2.fittingIn B.U ≠ ⊥ := by
      intro hbot
      rw [hbot] at hx
      exact hx1 (Subgroup.mem_bot.mp hx)
    -- Case (1) applied to `Y = B ∩ F(U)`
    have hNY : Subgroup.normalizer ((Bc ⊓ Work.GW2.fittingIn B.U : Subgroup G) : Set G) ≤ B.H := by
      rw [← hH]
      exact hCase.2 (Bc ⊓ Work.GW2.fittingIn B.U) hYne inf_le_right
    -- `Y ≤ O(M)`
    have hYO : Bc ⊓ Work.GW2.fittingIn B.U ≤ Work.GW2.oddCoreIn M :=
      calc Bc ⊓ Work.GW2.fittingIn B.U ≤ Bc ⊓ M :=
            le_inf inf_le_left (le_trans inf_le_left hBM)
        _ = Work.GW2.oddCoreIn M := hBcM
    -- `E(M) ≤ N_G(Y)`, since `E(M)` centralizes `O(M) ⊇ Y`
    have hEnorm : E₀.map M.subtype ≤
        Subgroup.normalizer ((Bc ⊓ Work.GW2.fittingIn B.U : Subgroup G) : Set G) := by
      rw [Subgroup.le_normalizer_iff]
      intro e he y hy
      have hcent : E₀.map M.subtype ≤
          Subgroup.centralizer ((Work.GW2.oddCoreIn M : Subgroup G) : Set G) :=
        Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
      have hcm : y * e = e * y := (Subgroup.mem_centralizer_iff.mp (hcent he)) y (hYO hy)
      rw [show e * y * e⁻¹ = y from by rw [← hcm]; group]
      exact hy
    have hEH : E₀.map M.subtype ≤ B.H := hEnorm.trans hNY
    -- hence `t ∈ Z(E(M))`, contradicting `Z(E(M))` odd
    set tE : ↥(E₀.map M.subtype) := ⟨B.t, htE'⟩ with htEdef
    have htZ : tE ∈ Subgroup.center ↥(E₀.map M.subtype) := by
      rw [Subgroup.mem_center_iff]
      intro g
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp (hEH g.2) B.t (by simp)).symm
    have hord : orderOf tE = 2 := by
      show orderOf (⟨B.t, htE'⟩ : ↥(E₀.map M.subtype)) = 2
      rw [orderOf_mk, B.t_order]
    have h2dvd : 2 ∣ Nat.card (Subgroup.center ↥(E₀.map M.subtype)) := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥(E₀.map M.subtype)) htZ
      rwa [hord] at h
    exact absurd (even_iff_two_dvd.mpr h2dvd) (Nat.not_even_iff_odd.mpr hcodd)
  have hmain := hYbot
  rw [hBcdef] at hmain
  exact hmain

end Work.CORE3

open Work.GW2

/-- The same lemma, mirrored at the namespace of the file path, so that it can be cited both as
`Work.CORE3.Case1aBFitting` (the name the area requests) and as
`Work.CORE3.Work.CORE3.Case1aBFitting` (the skeleton's namespace layout). -/
theorem Case1aBFitting (I : Case1Inputs) (hSetup : Case1aSetupProp) (hFr : Case1aFrattiniProp)
    (hAb : Case1aAbelianProp) (hA7 : Case1aA7Prop) (hMD : Case1aMDataProp) :
    Case1aBFittingProp :=
  _root_.Work.CORE3.Work.CORE3.Case1aBFitting I hSetup hFr hAb hA7 hMD

end Work.CORE3
