import Mathlib
import Submission.Work.Pi6.MSS.e2PsiCanonN
import Submission.Work.Pi6.MSS.e2Psi_pairing
import Submission.Work.Pi6.MSS.mixedEvaluation
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The pairing computation `⟨Ψ(β ⊗ f), [W_σ]⟩` in every filtration degree

`Submission/Work/Pi6/MSS/e2Psi_pairing.lean` proves the mixed-product computation
`Work.Pi6.MSS.e2Psi_pairing` only for base classes in degree `s = k + 1`, i.e. for total filtration
degree `≥ 1`.  Here we reproduce the *same* proof with the degree `n : ℕ` of the base class as the
parameter, using the degree-general vocabulary of `Submission/Work/Pi6/MSS/e2PsiCanonN.lean`
(`nIndexSigma`, `pairWchainN`, `pairWn`, `pairRHSn`).

Nothing in the argument is specific to `n ≥ 1`: every ingredient
(`evZ_apply`, `Kgπ_grSecX_apply`, `ker_Kgπ_inclL_eq_zero`, `inclL`/`sCCMap` compatibility,
`pairElemOne_val`, `eval_cup_pbC_crux`, `mixedEvaluation_cruxEps`) is already stated and proved for
an arbitrary filtration degree, so the transcription below covers `n = 0` as well.

* `pairLiftN` — the lift of the Eilenberg–Zilber chain to the `(n+1)`-st Serre subcomplex, whose
  class in `Kg 𝕜 p n` is the generator cycle `pairWchainN`;
* `pairWn_valN` — `pairWn` is that class (definitional);
* `inclL_pairLiftN` — its image in the chains of `E` is the Eilenberg–Zilber chain `cruxChain`;
* `cochainFun_grSecX_pairWn` — any lift of the class may be used in the evaluation.
-/

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

set_option maxHeartbeats 4000000

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The lift of the Eilenberg–Zilber chain over `σ` in the `(n+1)`-st Serre subcomplex, whose class
in `Kg 𝕜 p n` is the generator cycle `pairWchainN`. -/
abbrev pairLiftN (𝕜 : Type) [Field 𝕜] (p : C(E, B))
    (hfib : Work.StemsB.IsSerreFibration p) (n q : ℕ)
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).X q) :
    (Cc 𝕜 p (n + 1)).X (n + q) :=
  (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
    (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f (n + q)))
    (cruxIota 𝕜 p hfib n q (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z)

set_option backward.isDefEq.respectTransparency false in
theorem pairWn_valN (𝕜 : Type) [Field 𝕜] (p : C(E, B))
    (hfib : Work.StemsB.IsSerreFibration p) (n q : ℕ)
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).X q)
    (hc : (ModuleCat.Hom.hom ((Kg 𝕜 p n).d (n + q) ((n + q) - 1)))
      (pairWchainN 𝕜 p hfib n q σ z) = 0) :
    (pairWn 𝕜 p hfib n q σ z hc).1
      = (ModuleCat.Hom.hom ((Kgπ 𝕜 p n).f (n + q))) (pairLiftN 𝕜 p hfib n q σ z) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `inclL`-image of the lift is the Eilenberg–Zilber chain `cruxChain` of the mixed
evaluation. -/
theorem inclL_pairLiftN (𝕜 : Type) [Field 𝕜] (p : C(E, B))
    (hfib : Work.StemsB.IsSerreFibration p) (n q : ℕ)
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).X q) :
    (ModuleCat.Hom.hom ((inclL 𝕜 p (n + 1)).f (n + q))) (pairLiftN 𝕜 p hfib n q σ z)
      = cruxChain 𝕜 p hfib n q (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z := by
  change (ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜 (sserInc (p := p) (n + 1))).f (n + q)))
      ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
        (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f (n + q)))
        (cruxIota 𝕜 p hfib n q (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z))
    = cruxChain 𝕜 p hfib n q (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z
  rw [Work.Pi6.MSS.sCCMap_apply_comp, Work.SSSR.sndToR_ι]
  rfl

set_option backward.isDefEq.respectTransparency false in
/-- The `grSecX`-lift of the class `pairWn` can be replaced by the canonical lift `pairLiftN`: the
difference is killed by any cochain of `F^n`. -/
theorem cochainFun_grSecX_pairWn (𝕜 : Type) [Field 𝕜] (p : C(E, B))
    (hfib : Work.StemsB.IsSerreFibration p) (n q : ℕ) (β : ↥(ZB 𝕜 B n))
    (y : ↥(pZ 𝕜 (Wc 𝕜 p) 2 0 q))
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).X q)
    (hc : (ModuleCat.Hom.hom ((Kg 𝕜 p n).d (n + q) ((n + q) - 1)))
      (pairWchainN 𝕜 p hfib n q σ z) = 0) :
    cochainFun 𝕜 p (n + q) (pairElemOne 𝕜 p n q β y).1
        ((inclL 𝕜 p (n + 1)).f (n + q)
          (grSecX 𝕜 p n (n + q) (pairWn 𝕜 p hfib n q σ z hc)))
      = cochainFun 𝕜 p (n + q) (pairElemOne 𝕜 p n q β y).1
        ((inclL 𝕜 p (n + 1)).f (n + q) (pairLiftN 𝕜 p hfib n q σ z)) := by
  rw [pairWn_valN 𝕜 p hfib n q σ z hc]
  have hCπ : ((Kgπ 𝕜 p n).f (n + q)).hom
      (grSecX 𝕜 p n (n + q)
          ((ModuleCat.Hom.hom ((Kgπ 𝕜 p n).f (n + q)))
            (pairLiftN 𝕜 p hfib n q σ z))
        - pairLiftN 𝕜 p hfib n q σ z) = 0 := by
    simp only [map_sub, Kgπ_grSecX_apply, sub_self]
  have h0 := ker_Kgπ_inclL_eq_zero 𝕜 p n (n + q) (coFiltAnn 𝕜 (sF p))
    (cochainFun 𝕜 p (n + q) (pairElemOne 𝕜 p n q β y).1)
    (pairElemOne_mem_F 𝕜 p n q β y)
    (grSecX 𝕜 p n (n + q)
        ((ModuleCat.Hom.hom ((Kgπ 𝕜 p n).f (n + q)))
          (pairLiftN 𝕜 p hfib n q σ z))
      - pairLiftN 𝕜 p hfib n q σ z) hCπ
  have hsum : grSecX 𝕜 p n (n + q)
        ((ModuleCat.Hom.hom ((Kgπ 𝕜 p n).f (n + q)))
          (pairLiftN 𝕜 p hfib n q σ z))
      = (grSecX 𝕜 p n (n + q)
            ((ModuleCat.Hom.hom ((Kgπ 𝕜 p n).f (n + q)))
              (pairLiftN 𝕜 p hfib n q σ z))
          - pairLiftN 𝕜 p hfib n q σ z) + pairLiftN 𝕜 p hfib n q σ z := by abel
  rw [hsum, map_add, map_add, h0, zero_add]

theorem e2Psi_pairingN (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ)
    (β : ↥(Work.Pi6.MSS.ZB 𝕜 B n)) (y : ↥(Work.Pi6.MSS.pZ 𝕜 (Work.Pi6.MSS.Wc 𝕜 p) 2 0 q))
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).d q
      ((ComplexShape.down ℕ).next q))) z = 0)
    (hc : (ModuleCat.Hom.hom ((Work.Pi6.MSS.Kg 𝕜 p n).d (n + q) ((n + q) - 1)))
      (Work.Pi6.MSS.pairWchainN 𝕜 p hfib n q σ z) = 0) :
    Work.Pi6.MSS.evZ 𝕜 p n (n + q) (Work.Pi6.MSS.coFiltAnn 𝕜 (Work.Pi6.MSS.sF p))
        (Work.Pi6.MSS.pairElemOne 𝕜 p n q β y)
        ((Work.StemsB.fdH 𝕜 (Work.Pi6.MSS.Kg 𝕜 p n) (n + q)).mkQ
          (Work.Pi6.MSS.pairWn 𝕜 p hfib n q σ z hc))
      = Work.Pi6.MSS.pairRHSn 𝕜 p e₀ hfib hconn n q β y σ z hz := by
  have h1 := evZ_apply 𝕜 p n (n + q) (coFiltAnn 𝕜 (sF p))
    (pairElemOne 𝕜 p n q β y) (pairWn 𝕜 p hfib n q σ z hc)
  rw [h1, cochainFun_grSecX_pairWn 𝕜 p hfib n q β y σ z hc]
  rw [inclL_pairLiftN 𝕜 p hfib n q σ z]
  have hmain : cochainFun 𝕜 p (n + q) (pairElemOne 𝕜 p n q β y).1
        (cruxChain 𝕜 p hfib n q (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z)
      = Work.Cohomology.cup 𝕜 (Work.SSS.sSing E) (pbC 𝕜 p n β.1) y.1
        (cruxChain 𝕜 p hfib n q (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z) := by
    rw [pairElemOne_val]
    rfl
  rw [hmain, pairRHSn]
  exact mixedEvaluation_cruxEps 𝕜 E B p e₀ hfib hconn n q β.1 β.2 y
    (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z hz

end

end Work.Pi6.MSS
