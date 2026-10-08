import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1aFrattini
import Submission.Work.CORE3.Case1aAbelian
import Submission.Work.CORE3.MDataAux
import Submission.Work.CORE3.A7V18.P0ne
import Submission.Work.CORE3.A7V18.NP2NotH
import Submission.Work.CORE3.A7V18.V2LayerMne
import Submission.Work.CORE3.A7V18.A7QuotientD
import Submission.Work.CORE3.A7V18.SylowEight
import Submission.Work.CORE3.A7V18.P0Card

namespace Work.CORE3

open Subgroup
open Work.GW2

/-- Bender 1981 §3, p. 222, the `M`-step of the subcase `Ĥ = H`.  Deliverable
`Work.GW2.Case1aA7Prop` (`Submission/Work/CORE3/Defs.lean`), which the file
`Submission/Work/CORE3/Case1aA7.lean` currently leaves as a stub.

For a maximal `M ⊇ N_G(P₂)` (with `P₂ ∈ Syl_p(C_U(S))`): `S ≤ M`, `⟨t,t₂⟩ ≤ E(M)`,
`E(M)/Z(E(M)) ≅ A₇`, `|S| = 8` and `|O_p(U) ∩ M| = 3`.

Route (Bender pp. 222–223): `t₂` inverts `P₀ = O_p(U) ∩ M ≠ 1` (`hFr`), so `V₂ = ⟨t,t₂⟩ ⊄ O₂(M)`
and Lemma 2.9 (`I.h29`, `M` coatom, `G` simple) puts `V₂` in `E := E(M)`; then
`P₀ ≤ C_E(V₂)`, and `E/Z(E)` is neither `L₂(q)` nor `PGL₂(q)` because four-groups are
self-centralizing there (`I.T.l2four`), so `LayerProp` (`I.T.lay`, applied to the D-group `M`,
proper by `BenderCtx.ih`) gives `E/Z(E) ≅ A₇`; `|S| = 8` from `S ≤ M` with `E ∩ S ∈ Syl₂(E)`, and
`|P₀| = 3` by the `p`-part count in `A₇`.  `hAb` supplies `P ∩ P^g = ⊥` and the abelianness of
`P P^g` used in the same paragraph.  Available in-tree: `Case1aFrattini` (`P₂ ≠ 1`,
`N_G(P₁) ⊄ H`), `MDataAux` (`mdata_layer_quasisimple`, `mdata_layer_normal`,
`mdata_oddCore_le_centralizer_layer`), `MData/A7*`, `Case1aFrattiniApi` (`P1SylowIn`,
`PpartProp`, `SActsTriviallyModFitting`, `Case1aP1Sylow`, `Case1aPpart`), `SylowDihedral`,
`NormalizerPcoreEqHhat`.

The five conjuncts are assembled from the sub-results of the area `Work.CORE3.A7V18`:

* `P0ne` — `O_p(U) ∩ M ≠ ⊥`: the `p`-group `P₂` acts on the nontrivial `p`-group `O_p(U)` and
  hence has a nontrivial fixed point `x`; then `C_G(P₂) ≤ N_G(P₂) ≤ M` gives `x ∈ M`.
* `NP2NotH` — `N_G(P₂) ⋬ C_G(t)`: the `(t₂, P₂)`-twin of Bender's Frattini argument, which also
  yields `M ≠ C_G(t)` because `N_G(P₂) ≤ M`.
* `V2LayerMne` — `⟨t,t₂⟩ ≤ E(M)` (Lemma 2.9 plus the exclusion of its `O₂(M)` branch).
* `A7Quotient` — `E(M)/Z(E(M)) ≅ A₇` (`I.T.lay` applied to the `D`-group `M`, with the
  `L₂(q)`/`PGL₂(q)` shapes excluded by `I.T.l2four`).
* `SylowEight` — `|S| = 8`, and `P0Card` — `|O_p(U) ∩ M| = 3`. -/
theorem Case1aA7V18 (I : Case1Inputs) (hFr : Case1aFrattiniProp) (hAb : Case1aAbelianProp) :
    Case1aA7Prop := by
  intro G _instG _finG hFT hCtx B hCase1 hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM
  -- ### `S ≤ M`: `P₂ ≤ C_G(S)` gives `S ≤ C_G(P₂) ≤ N_G(P₂) ≤ M`.
  have hSle : (B.S : Subgroup G) ≤ M := by
    intro s hs
    have hcs : s ∈ Subgroup.centralizer (P2 : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact ((Subgroup.mem_centralizer_iff.mp (hP2le hy).2) s hs).symm
    exact hNM (Subgroup.centralizer_le_normalizer (P2 : Set G) hcs)
  -- ### `O_p(U) ∩ M ≠ ⊥`
  have hP0ne : (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) ≠ ⊥ :=
    Work.CORE3.A7V18.P0ne I hFr hAb G hFT hCtx B hCase1 hHhat D P2 M
      hP2le hP2grp hP2ndvd hMcoat hNM
  -- ### `M ≠ C_G(t) = B.H`
  have hMne : M ≠ B.H := by
    obtain ⟨n, hn, hnt⟩ :=
      Work.CORE3.A7V18.NP2NotH I hFr hAb G hFT hCtx B hCase1 hHhat D P2
        hP2le hP2grp hP2ndvd
    intro hMBH
    exact hnt (hMBH ▸ hNM hn)
  -- ### `V₂ = ⟨t,t₂⟩ ≤ E(M)`
  have hV2E : (Subgroup.zpowers B.t ⊔ Subgroup.zpowers D.t2 : Subgroup G) ≤
      Work.GW2.layerIn M :=
    Work.CORE3.A7V18.V2LayerMne I hFr hAb G hFT hCtx B hCase1 hHhat D P2 M
      hP2le hP2grp hP2ndvd hMcoat hNM hMne hP0ne
  -- ### `E(M)/Z(E(M)) ≅ A₇`
  have hQuot : Nonempty ((↥(Work.GW2.layerIn M) ⧸ Subgroup.center ↥(Work.GW2.layerIn M)) ≃*
      alternatingGroup (Fin 7)) :=
    Work.CORE3.A7V18.A7QuotientD I hFr hAb G hFT hCtx B hCase1 hHhat D P2 M
      hP2le hP2grp hP2ndvd hMcoat hNM hP0ne hV2E
  -- ### `|S| = 8` and `|O_p(U) ∩ M| = 3`
  have hS8 : Nat.card (B.S : Subgroup G) = 8 :=
    Work.CORE3.A7V18.SylowEight I hFr hAb G hFT hCtx B hCase1 hHhat D P2 M
      hP2le hP2grp hP2ndvd hMcoat hNM hV2E hQuot
  have hP03 : Nat.card (Work.GW2.pCoreIn D.p B.U ⊓ M : Subgroup G) = 3 :=
    Work.CORE3.A7V18.P0Card I hFr hAb G hFT hCtx B hCase1 hHhat D P2 M
      hP2le hP2grp hP2ndvd hMcoat hNM hP0ne hV2E hQuot
  exact ⟨hSle, hV2E, hQuot, hS8, hP03⟩

end Work.CORE3
