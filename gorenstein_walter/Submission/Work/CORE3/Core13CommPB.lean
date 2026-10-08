import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.MDataAux
import Submission.Work.CORE3.Case1aA7
import Submission.Work.CORE3.Core13PcoreLeM
import Submission.Work.CORE3.Core13LeOfInverted

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- Design pass 13 §1, D5: `[O_p(U), C_U(S)] = 1` in the §3a `M`-analysis.

Route: `Work.CORE3.Core13PcoreLeM` (import `Submission.Work.CORE3.Core13PcoreLeM`) gives
`P := O_p(U) ≤ M`; `hA7` gives `zpowers B.t ⊔ zpowers D.t2 ≤ layerIn M`, so `t₂ ∈ E(M)`; the
layer is normal in `M` (`Work.CORE3.mdata_layer_normal`); `D.inv` says `t₂` inverts `P`; the pure
result `Work.CORE3.Core13LeOfInverted` (import `Submission.Work.CORE3.Core13LeOfInverted`) gives
`P ≤ layerIn M` (oddness of `P` from `B.U = oddCoreIn B.H`).  Then `layer ↥M ≠ ⊥` (it contains
`t₂ ≠ 1`), so `Work.CORE3.mdata_layer_quasisimple` gives `IsQuasisimple (layer ↥M)` and
`Work.CORE3.mdata_oddCore_le_centralizer_layer` gives `O(M) ≤ C_G(E(M))`.  Finally
`B = B ⊓ M = O(M)` (first two conjuncts of `hMD`), so `B` centralizes `P`. -/
theorem Core13CommPB (G : Type) [Group G] [Finite G] (I : Case1Inputs)
    (hAb : Case1aAbelianProp) (hA7 : Case1aA7Prop) (hMD : Case1aMDataProp)
    (hFT : FeitThompsonProp) (hCtx : BenderCtx G) (B : BenderSetup G) (hCase1 : Case1 B)
    (hHhat : B.Hhat = B.H) (D : Case1aData B) (P2 M : Subgroup G)
    (hP2le : P2 ≤ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) (hP2grp : IsPGroup D.p P2)
    (hP2ndvd : ¬ D.p ∣ P2.relIndex (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)))
    (hMcoat : IsCoatom M) (hNM : normalizer (P2 : Set G) ≤ M) :
    ∀ a ∈ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G), ∀ b ∈ pCoreIn D.p B.U,
      a * b = b * a := by
  intro a ha b hb
  -- D3: `P = O_p(U) ≤ M`
  have hPleM : pCoreIn D.p B.U ≤ M :=
    Core13PcoreLeM G I hAb hMD hFT hCtx B hCase1 hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  -- `hA7` puts `t₂` in `E(M) = layerIn M`
  obtain ⟨_, ht2E, -, -, -⟩ :=
    hA7 G hFT hCtx B hCase1 hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  have ht2ne : D.t2 ≠ 1 := by
    intro h
    have h1 : orderOf D.t2 = 1 := orderOf_eq_one_iff.mpr h
    rw [D.t2_order] at h1
    omega
  have ht2layer : D.t2 ∈ layerIn M :=
    ht2E (Subgroup.mem_sup_right (Subgroup.mem_zpowers D.t2))
  -- the layer is nontrivial (it contains `t₂ ≠ 1`)
  have hlayer_ne : Work.GW2.layer ↥M ≠ ⊥ := by
    intro hbot
    have hbot' : layerIn M = ⊥ := by rw [Work.GW2.layerIn, hbot, Subgroup.map_bot]
    rw [hbot'] at ht2layer
    exact ht2ne (by simpa using ht2layer)
  have hQuasi : IsQuasisimple (Work.GW2.layer ↥M) :=
    (mdata_layer_quasisimple I hCtx B hMcoat hlayer_ne).1
  -- `O(M) ≤ C_G(E(M))`
  have hOcleL : oddCoreIn M ≤ centralizer ((layerIn M : Subgroup G) : Set G) :=
    mdata_oddCore_le_centralizer_layer M hFT hQuasi
  -- `B = B ⊓ M = O(M)` (first two conjuncts of `hMD`)
  have hBleM : B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) ≤ M :=
    (hMD G hFT hCtx B hCase1 hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM).1
  have hBeqB : B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) = oddCoreIn M := by
    have h := (hMD G hFT hCtx B hCase1 hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM).2.1
    rwa [inf_eq_left.mpr hBleM] at h
  -- `M` normalizes `layerIn M` (the layer is normal in `↥M`)
  have hLn : ∀ m ∈ M, ∀ l ∈ layerIn M, m * l * m⁻¹ ∈ layerIn M := by
    intro m hm l hl
    rw [Work.GW2.layerIn] at hl ⊢
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hl
    refine Subgroup.mem_map.mpr ⟨⟨m, hm⟩ * x * ⟨m, hm⟩⁻¹, ?_, ?_⟩
    · exact (mdata_layer_normal M).conj_mem x hx ⟨m, hm⟩
    · simp
  -- `P` is odd, since `P ≤ U = O(H)`
  have hoddP : Odd (Nat.card (pCoreIn D.p B.U)) :=
    Odd.of_dvd_nat (Work.CORE2A.bSetup_U_odd B)
      (Subgroup.card_dvd_of_le (pCoreIn_le_self D.p B.U))
  -- D4: `P ≤ layerIn M`
  have hPleL : pCoreIn D.p B.U ≤ layerIn M :=
    Core13LeOfInverted G (Subgroup.map_subtype_le (Work.GW2.layer ↥M)) hLn ht2layer hPleM hoddP
      D.inv
  have hbL : b ∈ layerIn M := hPleL hb
  have haO : a ∈ oddCoreIn M := hBeqB ▸ ha
  exact ((Subgroup.mem_centralizer_iff.mp (hOcleL haO)) b hbL).symm

end Work.CORE3
