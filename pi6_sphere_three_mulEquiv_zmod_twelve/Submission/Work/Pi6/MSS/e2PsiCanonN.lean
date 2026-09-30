import Mathlib
import Submission.Work.Pi6.MSS.e2Lbar
import Submission.Work.Pi6.MSS.e2Canon
import Submission.Work.Pi6.MSS.e2Canon_gen
import Submission.Work.Pi6.MSS.e1SerreIso_gen
import Submission.Work.Pi6.MSS.e2Psi_pairing
import Submission.Work.Pi6.MSS.Kgpi_d_cruxIota_sndToR
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# Degree-general vocabulary for the comparison `L̄ ∘ Ψ = Λ ∘ T`

The existing vocabulary of `Submission/Work/Pi6/MSS/e2PsiPairDefs.lean` and
`.../e2FinalDefs.lean` (`genElem`, `pairW`, `pairRHS`, `genCyc`, ...) is indexed by `s + 1`, i.e. it
only covers total filtration degree `≥ 1`.  The comparison `Work.Pi6.MSS.e2Psi_canon` must hold in
*all* filtration degrees, in particular in degree `0`, so here we reproduce those definitions with
the degree `n : ℕ` as the parameter (for `n = k + 1` they are definitionally the old ones).

* `genElemN` — the generator `∑_j λ_j ι_{σ_j}(triv_{σ_j}[z_j])` of `N_n(B) ⊗ H_q(F)`;
* `genCycN`  — its homology class (given that it is a cycle);
* `pairWchainN` — the Eilenberg–Zilber chain over `σ` pushed to the graded piece `Kg n`;
* `pairWsumN` — the corresponding sum;
* `pairRHSn` — the scalar of the mixed evaluation.
-/

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial TensorProduct

noncomputable section

variable {E B : Type} [TopologicalSpace E] [TopologicalSpace B]

/-- The degree general generator `∑_j λ_j ι_{σ_j}(triv_{σ_j}[z_j])` of `N_n(B) ⊗ H_q(F)`. -/
noncomputable def genElemN (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (n q k : ℕ) (lam : Fin k → 𝕜)
    (σ : Fin k → Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).X q)
    (hz : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).d q
      ((ComplexShape.down ℕ).next q) (z j) = 0) :
    (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM (R := 𝕜) p e₀ q)).X n :=
  (Work.SSSR.serreE1CoefIsoIso (Work.SSSR.sSing B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) n).hom.hom
    (∑ j : Fin k, lam j •
      (CategoryTheory.Limits.Sigma.ι
        (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) n => Work.SSSR.coefM (R := 𝕜) p e₀ q)
        (σ j))
        ((ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).hom)
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).cyclesMk
              (z j) ((ComplexShape.down ℕ).next q) rfl (hz j)))))

/-- The homology class of the degree-`n` generator, given that it is a cycle. -/
noncomputable def genCycN (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (n q k : ℕ) (lam : Fin k → 𝕜)
    (σ : Fin k → Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).X q)
    (hz : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).d q
      ((ComplexShape.down ℕ).next q) (z j) = 0)
    (hcyc : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q)).d n ((ComplexShape.down ℕ).next n)
        (genElemN 𝕜 p e₀ hfib hconn n q k lam σ z hz) = 0) :
    (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B)
      (Work.SSSR.coefM (R := 𝕜) p e₀ q)).homology n :=
  ModuleCat.Hom.hom (HomologicalComplex.homologyπ
    (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM (R := 𝕜) p e₀ q)) n)
    (HomologicalComplex.cyclesMk
      (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM (R := 𝕜) p e₀ q))
      (genElemN 𝕜 p e₀ hfib hconn n q k lam σ z hz)
      ((ComplexShape.down ℕ).next n) rfl hcyc)

/-- The Eilenberg–Zilber chain over `σ`, pushed to the graded piece `Kg n`. -/
noncomputable def pairWchainN (𝕜 : Type) [Field 𝕜] (p : C(E, B))
    (hfib : Work.StemsB.IsSerreFibration p) (n q : ℕ)
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).X q) :
    (Kg 𝕜 p n).X (n + q) :=
  (ModuleCat.Hom.hom ((Kgπ 𝕜 p n).f (n + q)))
    ((ModuleCat.Hom.hom ((Work.SSSR.sCCMap 𝕜
      (Work.SSSR.sndToR (Work.SSSR.sSingP p) σ)).f (n + q)))
      (cruxIota 𝕜 p hfib n q (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z))

/-- The corresponding element of the cycle submodule, given the cycle condition. -/
noncomputable def pairWn (𝕜 : Type) [Field 𝕜] (p : C(E, B))
    (hfib : Work.StemsB.IsSerreFibration p) (n q : ℕ)
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).X q)
    (hc : (ModuleCat.Hom.hom ((Kg 𝕜 p n).d (n + q) ((n + q) - 1)))
      (pairWchainN 𝕜 p hfib n q σ z) = 0) :
    ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p n) (n + q)) :=
  ⟨pairWchainN 𝕜 p hfib n q σ z, hc⟩

/-- The degree `n` scalar of the mixed-product computation `⟨Ψ(β ⊗ f), [W_γ]⟩`. -/
noncomputable def pairRHSn (𝕜 : Type) [Field 𝕜] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ)
    (β : ↥(ZB 𝕜 B n)) (y : ↥(pZ 𝕜 (Wc 𝕜 p) 2 0 q))
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).X q)
    (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
        (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).d q
        ((ComplexShape.down ℕ).next q))) z = 0) :
    𝕜 :=
  cruxEps 𝕜 n * Work.Cohomology.genEval 𝕜 (Work.SSS.sSing B) β.1
      ((Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ).app
        (op (SimplexCategory.mk n)) (Work.Pi6.MSSK.topS n)) *
    Work.Cohomology.kronH 𝕜 (Work.SSS.sSing (Work.StemsB.fibre p (p e₀))) q
      (rho 𝕜 E B p e₀ q
        (Submodule.mkQ ((pDen 𝕜 (Wc 𝕜 p) 2 0 q).comap (pZ 𝕜 (Wc 𝕜 p) 2 0 q).subtype) y))
      (cruxFibre 𝕜 p e₀ hfib hconn n q (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ) z hz)

/-- The corresponding sum of the degree-`n` graded-piece cycles. -/
noncomputable def pairWsumN (𝕜 : Type) [Field 𝕜] (p : C(E, B))
    (hfib : Work.StemsB.IsSerreFibration p) (n q k : ℕ) (lam : Fin k → 𝕜)
    (σ : Fin k → Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (z : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).X q)
    (hz : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).d q
      ((ComplexShape.down ℕ).next q) (z j) = 0)
    (hc : ∀ j : Fin k, (ModuleCat.Hom.hom ((Kg 𝕜 p n).d (n + q)
      ((n + q) - 1))) (pairWchainN 𝕜 p hfib n q (σ j) (z j)) = 0) :
    ↥(Work.StemsB.fdZ 𝕜 (Kg 𝕜 p n) (n + q)) :=
  ∑ j : Fin k, lam j • pairWn 𝕜 p hfib n q (σ j) (z j) (hc j)

end

end Work.Pi6.MSS
