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
import Submission.Work.CORE3.Core18PcoreLeM
import Submission.Work.CORE3.Core18BcNormalizesInf

/-!
# GW design pass 18, item B, step B2: `B = C_U(S) ≤ M` (closes `MData/BcLeM`), no cycle

Bender p. 223, in the paper's order: local control on `B ∩ M` (`hLC`, `hBM`) ⟹ `P ≤ M`
(`Core18PcoreLeM`) ⟹ `PP^n ≤ P P₂ ≤ M` ⟹ `X' := PP^n ∩ B` is a nontrivial subgroup of
`B ∩ M ≤ O(M)` ⟹ `N_G(X') ≤ M` (`hLC`); and `B` normalizes `X'` because `B ≤ C_G(V₁)`
normalizes both `P ⊴ C_G(V₁)` and `P^n ⊴ C_G(V₁)^n = C_G(V₁)` (`n ∈ N_G(V₁)`) — leaf
`Core18BcNormalizesInf`.  Hence `B ≤ N_G(X') ≤ M`.  (Bender: "Applying this to the normal
subgroup `X = B ∩ PP^g` of `C_U(t₁)` … we see that `B ⊆ M`.")
-/

namespace Work.CORE3

open Subgroup
open Work.GW2 Work.CORE3

set_option linter.style.haveILetI false
set_option linter.dupNamespace false

theorem Core18BcLeM (G : Type) [Group G] [Finite G] (I : Case1Inputs)
    (hAb : Case1aAbelianProp) (hFT : FeitThompsonProp)
    (hCtx : BenderCtx G) (B : BenderSetup G) (hCase1 : Case1 B) (hHhat : B.Hhat = B.H)
    (D : Case1aData B) (P2 M : Subgroup G)
    (hP2le : P2 ≤ B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) (hP2grp : IsPGroup D.p P2)
    (hP2ndvd : ¬ D.p ∣ P2.relIndex (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)))
    (hMcoat : IsCoatom M) (hNM : normalizer (P2 : Set G) ≤ M)
    (hBM : (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) ⊓ M ≤ oddCoreIn M)
    (hLC : ∀ X : Subgroup G, X ≠ ⊥ → X ≤ oddCoreIn M → normalizer (X : Set G) ≤ M) :
    B.U ⊓ centralizer ((B.S : Subgroup G) : Set G) ≤ M := by
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
  -- ## `P ≤ M` (step B1)
  have hPM : pCoreIn D.p B.U ≤ M :=
    Core18PcoreLeM G I hAb hFT hCtx B hCase1 hHhat D P2 M hP2le hP2grp hP2ndvd hMcoat hNM hBM hLC
  have hP2M : P2 ≤ M := Subgroup.le_normalizer.trans hNM
  have hYM : (pCoreIn D.p B.U ⊔ conjSub n (pCoreIn D.p B.U) : Subgroup G) ≤ M :=
    sup_le hPM (hYle.trans (sup_le hPM hP2M))
  -- ## `X' := (P ⊔ P^n) ⊓ B`
  have hX'ne : ((pCoreIn D.p B.U ⊔ conjSub n (pCoreIn D.p B.U)) ⊓
      (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) : Subgroup G) ≠ ⊥ := fun h =>
    hXne (le_bot_iff.mp (h ▸ inf_le_inf_left _ hP2le))
  have hX'le : ((pCoreIn D.p B.U ⊔ conjSub n (pCoreIn D.p B.U)) ⊓
      (B.U ⊓ centralizer ((B.S : Subgroup G) : Set G)) : Subgroup G) ≤ oddCoreIn M :=
    (le_inf inf_le_right (inf_le_left.trans hYM)).trans hBM
  have hNX' := hLC _ hX'ne hX'le
  exact (Core18BcNormalizesInf G B D n hnV1).trans hNX'

end Work.CORE3
