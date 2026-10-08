import Mathlib
import Submission.Work.CORE3.Defs
import Submission.Work.CORE3.Case1aFrattiniApi
import Submission.Work.CORE3.Case1aFrattiniConj
import Submission.Work.CORE3.Case1aFrattiniConjV
import Submission.Work.CORE3.Case1aP1Sylow
import Submission.Work.CORE3.Case1aPpart
import Submission.Work.CORE3.Case1aFrattiniSAct
import Submission.Work.CORE3.Case1aP_ne_bot
import Submission.Work.CORE3.Core13InfNeBot
import Submission.Work.CORE3.MDataAux

/-!
# GW design pass 18, item B, step B1: `P = O_p(U) ≤ M` WITHOUT `Case1aMDataProp`

`Work.CORE3.Core13PcoreLeM` used only the fourth conjunct of `hMD : Case1aMDataProp`
(`N_G(X) ≤ M` for `1 ≠ X ≤ B`), at `X = (P ⊔ P^n) ⊓ P₂`.  But this `X` already lies in
`B ∩ M`, because `X ≤ P₂ ≤ N_G(P₂) ≤ M`.  So Bender's *own* local-control clause
("`N_G(X) ≤ M` whenever `1 ≠ X ⊆ B ∩ M`", p. 223), i.e. `MData.LocalControlOfOddCore`
together with the proved `MData.BcInfMLeOddCore` (`B ∩ M ≤ O(M)`), suffices.  This removes the
cycle `BcLeM → Core13PcoreLeM → Case1aMDataProp → BcLeM`.

Proof = `Core13PcoreLeM`'s proof with the `hNX` line replaced (no `sorry`).
-/

namespace Work.CORE3

open Subgroup
open Work.GW2 Work.CORE3

set_option linter.style.haveILetI false
set_option linter.dupNamespace false

/-- Design pass 13 §1, D3: `P = O_p(U) ≤ M` in the §3a `M`-analysis (Bender 1981 p. 223, via
the subgroup `X = B ∩ PP^g` of the paper, here `(P ⊔ P^n) ⊓ P₂`).

Route: take `n` from `Work.CORE3.Case1aFrattiniConjV` (import
`Submission.Work.CORE3.Case1aFrattiniConjV`; with `P1SylowIn` from
`Work.CORE3.Case1aP1Sylow`, whose inputs `PpartProp`/`SActsTriviallyModFitting` come from
`Case1aPpart`/`Case1aFrattiniSAct`); `n ∉ H` because `n * B.t * n⁻¹ = D.t1 ≠ B.t`.
`hAb` at `g := n` gives `P ⊓ P^n = ⊥` and `P ⊔ P^n` commutative.  Since `n ∈ N_G(P₁)` and
`P^n ≤ P₁ = P ⊔ P₂`, `Work.CORE3.Core13InfNeBot` (import
`Submission.Work.CORE3.Core13InfNeBot`) with `Y := P^n` (`≠ ⊥`, from
`Work.CORE3.Case1aP_ne_bot`) gives `X := (P ⊔ P^n) ⊓ P₂ ≠ ⊥`.  `X ≤ P₂ ≤ B` and
`X ≤ P₂ ≤ N_G(P₂) ≤ M`, so `X ≤ B ∩ M ≤ O(M)` (`hBM`) and local control `hLC` gives
`N_G(X) ≤ M`; `P` centralizes `X` (both inside the commutative
`P ⊔ P^n`), hence `P ≤ C_G(X) ≤ N_G(X) ≤ M`. -/
theorem Core18PcoreLeM (G : Type) [Group G] [Finite G] (I : Case1Inputs)
    (hAb : Case1aAbelianProp) (hFT : FeitThompsonProp)
    (hCtx : BenderCtx G) (B : BenderSetup G) (hCase1 : Case1 B) (hHhat : B.Hhat = B.H)
    (D : Case1aData B) (P2 M : Subgroup G)
    (hP2le : P2 ≤ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) (hP2grp : IsPGroup D.p P2)
    (hP2ndvd : ¬ D.p ∣ P2.relIndex (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)))
    (hMcoat : IsCoatom M) (hNM : normalizer (P2 : Set G) ≤ M)
    (hBM : (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) ⊓ M ≤ oddCoreIn M)
    (hLC : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ oddCoreIn M → normalizer (X : Set G) ≤ M) :
    pCoreIn D.p B.U ≤ M := by
  classical
  haveI hpFact : Fact D.p.Prime := ⟨D.hp⟩
  -- ## `P₁ = O_p(U)·P₂` is a Sylow `p`-subgroup of `C_G(V₁)`
  have hSAct : SActsTriviallyModFitting B := Case1aFrattiniSAct G hFT I.T hCtx B hCase1
  have hPpart : PpartProp B D := Case1aPpart G hFT I.T hCtx B D hSAct
  have hsyl : P1SylowIn B D P2 :=
    Case1aP1Sylow G hFT I.T hCtx B D P2 hP2le hP2grp hP2ndvd hPpart
  -- ## the conjugating element `n ∈ N_G(V₁)` with `n B.t n⁻¹ = D.t1`
  obtain ⟨n, hnN, hnV1, hnt⟩ := Case1aFrattiniConjV G I.T hCtx B D P2 hsyl
  -- ## `n ∉ H = C_G(t)`, since `t₁ ∉ S₀` whereas `t ∈ S₀`
  have hnH : n ∉ B.H := by
    intro hn
    have hk : B.t * n = n * B.t := (Subgroup.mem_centralizer_iff.mp hn) B.t (by simp)
    have h1 : n * B.t * n⁻¹ = B.t := by rw [← hk]; group
    refine D.t1_nmem ?_
    have h2 : D.t1 = B.t := by rw [← hnt, h1]
    rw [h2]; exact B.t_mem
  -- ## `hAb` at `g = n`: `P ⊓ P^n = ⊥` and `P ⊔ P^n` is commutative
  have hAbn := hAb G hFT hCtx B hCase1 hHhat D n (by simpa [V1] using hnV1) hnH
  obtain ⟨hinf0, hcomm0⟩ := hAbn
  -- ## `P₂ ≤ N_G(P)`
  have hPn : P2 ≤ Subgroup.normalizer ((pCoreIn D.p B.U : Subgroup G) : Set G) :=
    (hP2le.trans inf_le_left).trans
      ((Subgroup.le_normalizer).trans (c1aLe_normalizer_pCoreIn D.p B.U))
  -- ## `Y := P^n ≤ P ⊔ P₂` (because `n` normalizes `P₁ = P ⊔ P₂`)
  have hYle : conjSub n (pCoreIn D.p B.U) ≤ pCoreIn D.p B.U ⊔ P2 := by
    have hconjP1 : conjSub n (pCoreIn D.p B.U ⊔ P2) = pCoreIn D.p B.U ⊔ P2 := by
      simpa [Work.CORE2A.conjSub_eq_map] using
        (Subgroup.mem_normalizer_iff_map_conj_eq).mp hnN
    calc conjSub n (pCoreIn D.p B.U)
        ≤ conjSub n (pCoreIn D.p B.U ⊔ P2) := Work.CORE2A.conjSub_mono le_sup_left n
      _ = pCoreIn D.p B.U ⊔ P2 := hconjP1
  have hYP : conjSub n (pCoreIn D.p B.U) ⊓ pCoreIn D.p B.U = ⊥ := by
    rw [inf_comm]; exact hinf0
  have hYne : conjSub n (pCoreIn D.p B.U) ≠ ⊥ := by
    intro hc
    refine Case1aP_ne_bot G B D ?_
    have h2 : conjSub n⁻¹ (conjSub n (pCoreIn D.p B.U)) = conjSub n⁻¹ (⊥ : Subgroup G) := by
      rw [hc]
    rw [Work.CORE2A.conjSub_inv_conjSub, Work.CORE2A.conjSub_bot] at h2
    exact h2
  -- ## `X := (P ⊔ P^n) ⊓ P₂ ≠ ⊥`
  have hXne : (pCoreIn D.p B.U ⊔ conjSub n (pCoreIn D.p B.U)) ⊓ P2 ≠ ⊥ :=
    Core13InfNeBot G hPn hYle hYP hYne
  have hXle : ((pCoreIn D.p B.U ⊔ conjSub n (pCoreIn D.p B.U)) ⊓ P2 : Subgroup G)
      ≤ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) :=
    inf_le_right.trans hP2le
  -- ## local control at `X ≤ B ∩ M = O(M)`: `X ≤ P₂ ≤ N_G(P₂) ≤ M`, so no `P ≤ M` is needed
  have hXM : ((pCoreIn D.p B.U ⊔ conjSub n (pCoreIn D.p B.U)) ⊓ P2 : Subgroup G) ≤ M :=
    inf_le_right.trans (Subgroup.le_normalizer.trans hNM)
  have hNX := hLC (((pCoreIn D.p B.U ⊔ conjSub n (pCoreIn D.p B.U)) ⊓ P2 : Subgroup G)) hXne
    ((le_inf hXle hXM).trans hBM)
  -- ## `P` centralizes `X`, both lying in the commutative `P ⊔ P^n`
  have hPcent : pCoreIn D.p B.U ≤ Subgroup.centralizer
      (((pCoreIn D.p B.U ⊔ conjSub n (pCoreIn D.p B.U)) ⊓ P2 : Subgroup G) : Set G) := by
    intro p hp
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy1 : y ∈ pCoreIn D.p B.U ⊔ conjSub n (pCoreIn D.p B.U) := hy.1
    exact congrArg (fun z : ↥(pCoreIn D.p B.U ⊔ conjSub n (pCoreIn D.p B.U)) => (z : G))
      (isMulCommutative_iff.mp hcomm0 ⟨y, hy1⟩ ⟨p, Subgroup.mem_sup_left hp⟩)
  exact (hPcent.trans (Subgroup.centralizer_le_normalizer _)).trans hNX

end Work.CORE3
