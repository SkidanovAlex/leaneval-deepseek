import Mathlib
import Submission.Work.Pi6.MSS.faceSum_cycle
import Submission.Work.Pi6.MSS.jF_ker_decomp
import Submission.Work.Pi6.MSS.kF_psiSig_sum
import Submission.Work.Pi6.MSS.CruxDefs
import Submission.Work.Pi6.MSS.E1Map
import Submission.Work.Pi6.MSS.e2Pairing_descent
import Submission.Work.Pi6.MSS.cruxChain_mem_A
import Submission.Work.Pi6.MSS.Kgpi_d_cruxIota_sndToR
import Submission.Work.SSSR.chainCondition_gen
import Submission.Work.SSSR.serreE1Main
import Submission.Work.SSSR.kF_psiCoef_gen
import Submission.Work.SSSR.grFMap
import Submission.Work.SSSR.faceDiff
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

set_option autoImplicit false
set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

namespace Work.Pi6.MSS

theorem big1_faceSum (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (k q : ℕ)
    (n : ℕ) (lam : Fin n → 𝕜)
    (σ : Fin n → Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1))
    (z : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).X q)
    (hz : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).d q ((ComplexShape.down ℕ).next q) (z j) = 0)
    (hcyc : Work.SSSR.faceD' (Work.SSSR.sSing B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) k
      (∑ j : Fin n, lam j •
        (CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1) =>
            Work.SSSR.coefM (R := 𝕜) p e₀ q) (σ j))
          ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
            (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom)
            ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).homologyπ q))
              ((Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).cyclesMk (z j)
                ((ComplexShape.down ℕ).next q) rfl (hz j))))) = 0) :
    ∃ (Y : ↥((Work.Pi6.MSS.Cc 𝕜 p k).X (k+q)))
      (Z : ↥((Work.Pi6.MSS.Cc 𝕜 p (k+1)).X ((k+1)+q))),
      (Work.Pi6.MSS.inclL 𝕜 p (k+1)).f (k+q)
          (∑ j : Fin n, lam j • Work.SSSR.faceSum p hfib k q
            (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j))) (Work.SSSR.sigHat (σ j)) rfl (z j))
        = (Work.Pi6.MSS.inclL 𝕜 p k).f (k+q) Y
          + (Work.Pi6.MSS.inclL 𝕜 p (k+1)).f (k+q)
              ((ModuleCat.Hom.hom (((Work.Pi6.MSS.Cc 𝕜 p (k+1)).d ((k+1)+q) (k+q)))) Z) := by
  have hfib' : Work.SSSR.StemsB.IsSerreFibration p := hfib
  have hconn' : Work.SSSR.PiS.SimplyConn B (p e₀) := hconn
  obtain ⟨c, hc1, hal⟩ := Work.SSSR.exists_pieceAlpha (R := 𝕜) p hfib'
  obtain ⟨eps, heps, hcan⟩ := Work.SSSR.PsiSig_chainCondition (R := 𝕜) p e₀ hfib' hconn' q
  let G := ∑ j : Fin n, lam j •
      (CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1) =>
          Work.SSSR.coefM (R := 𝕜) p e₀ q) (σ j))
        ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib' hconn' q
          (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom)
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).cyclesMk (z j)
              ((ComplexShape.down ℕ).next q) rfl (hz j))))
  let V : (Work.Pi6.MSS.Cc 𝕜 p (k+1)).X (k+q) :=
    ∑ j : Fin n, lam j • Work.SSSR.faceSum p hfib' k q
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j))) (Work.SSSR.sigHat (σ j)) rfl (z j)
  have hGcyc : (ModuleCat.Hom.hom (Work.SSSR.faceD' (Work.SSSR.sSing B)
      (Work.SSSR.coefM (R := 𝕜) p e₀ q) k)) G = 0 := by
    exact hcyc
  have hface : ∀ j : Fin n, (ModuleCat.Hom.hom (((Work.SSSR.Fc (R := 𝕜) p).obj k).d (k+q)
      ((ComplexShape.down ℕ).next (k+q))))
      (Work.SSSR.faceSum p hfib' k q (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))
        (Work.SSSR.sigHat (σ j)) rfl (z j)) = 0 :=
    fun j => faceSum_cycle 𝕜 E B p hfib' k q (σ j) (z j) (hz j)
  have hVcyc : (ModuleCat.Hom.hom (((Work.SSSR.Fc (R := 𝕜) p).obj k).d (k+q)
      ((ComplexShape.down ℕ).next (k+q)))) V = 0 := by
    show (ModuleCat.Hom.hom (((Work.SSSR.Fc (R := 𝕜) p).obj k).d (k+q)
      ((ComplexShape.down ℕ).next (k+q))))
      (∑ j : Fin n, lam j • Work.SSSR.faceSum p hfib' k q
        (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j))) (Work.SSSR.sigHat (σ j)) rfl (z j)) = 0
    rw [map_sum]
    refine Finset.sum_eq_zero (fun j _ => ?_)
    rw [map_smul, hface j, smul_zero]
  have hkF : (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan (R := 𝕜) p) k q))
      ((ModuleCat.Hom.hom (Work.SSSR.PsiSig p e₀ hfib' hconn' q (k+1))) G)
      = c (k+1) • ((Work.Pi6.MSS.Cc 𝕜 p (k+1)).homologyπ (k+q)
          ((Work.Pi6.MSS.Cc 𝕜 p (k+1)).cyclesMk V ((ComplexShape.down ℕ).next (k+q))
            rfl hVcyc)) := by
    dsimp only [G, V]
    exact kF_psiSig_sum 𝕜 E B p e₀ hfib' hconn' k q c hc1 hal n lam σ z hz hface hVcyc
  have hd1 : (ModuleCat.Hom.hom (Work.SSSR.d1 (Work.SSSR.xiCan (R := 𝕜) p) k q))
      ((ModuleCat.Hom.hom (Work.SSSR.PsiSig p e₀ hfib' hconn' q (k+1))) G) = 0 := by
    have h := congrArg (fun (g : (∐ fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1) =>
        Work.SSSR.coefM (R := 𝕜) p e₀ q) ⟶
          (Work.SSSR.grF (Work.SSSR.Fc (R := 𝕜) p) k).homology (k+q)) =>
      (ModuleCat.Hom.hom g) G) (hcan k)
    have h0 : (ModuleCat.Hom.hom ((eps k) • (Work.SSSR.faceD' (Work.SSSR.sSing B)
        (Work.SSSR.coefM (R := 𝕜) p e₀ q) k ≫
        Work.SSSR.PsiSig p e₀ hfib' hconn' q k))) G = 0 := by
      show (eps k) • ((ModuleCat.Hom.hom (Work.SSSR.PsiSig p e₀ hfib' hconn' q k))
        ((ModuleCat.Hom.hom (Work.SSSR.faceD' (Work.SSSR.sSing B)
          (Work.SSSR.coefM (R := 𝕜) p e₀ q) k)) G)) = 0
      rw [hGcyc]
      simp
    exact h.trans h0
  have hd1' : (ModuleCat.Hom.hom (Work.SSSR.jF (Work.SSSR.xiCan (R := 𝕜) p) k q))
      ((ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan (R := 𝕜) p) k q))
        ((ModuleCat.Hom.hom (Work.SSSR.PsiSig p e₀ hfib' hconn' q (k+1))) G)) = 0 :=
    hd1
  have hker : (ModuleCat.Hom.hom (Work.SSSR.jF (Work.SSSR.xiCan (R := 𝕜) p) k q))
      ((Work.Pi6.MSS.Cc 𝕜 p (k+1)).homologyπ (k+q)
        ((Work.Pi6.MSS.Cc 𝕜 p (k+1)).cyclesMk V ((ComplexShape.down ℕ).next (k+q))
          rfl hVcyc)) = 0 := by
    have hd1'' : (ModuleCat.Hom.hom (Work.SSSR.jF (Work.SSSR.xiCan (R := 𝕜) p) k q))
        (c (k+1) • ((Work.Pi6.MSS.Cc 𝕜 p (k+1)).homologyπ (k+q)
          ((Work.Pi6.MSS.Cc 𝕜 p (k+1)).cyclesMk V ((ComplexShape.down ℕ).next (k+q))
            rfl hVcyc))) = 0 := by
      rw [← hkF]
      exact hd1'
    have h2 : c (k+1) • ((ModuleCat.Hom.hom (Work.SSSR.jF (Work.SSSR.xiCan (R := 𝕜) p) k q))
        ((Work.Pi6.MSS.Cc 𝕜 p (k+1)).homologyπ (k+q)
          ((Work.Pi6.MSS.Cc 𝕜 p (k+1)).cyclesMk V ((ComplexShape.down ℕ).next (k+q))
            rfl hVcyc))) = 0 :=
      (map_zsmul (ModuleCat.Hom.hom (Work.SSSR.jF (Work.SSSR.xiCan (R := 𝕜) p) k q)) (c (k+1))
        ((Work.Pi6.MSS.Cc 𝕜 p (k+1)).homologyπ (k+q)
          ((Work.Pi6.MSS.Cc 𝕜 p (k+1)).cyclesMk V ((ComplexShape.down ℕ).next (k+q))
            rfl hVcyc))).symm.trans hd1''
    rcases hc1 (k+1) with hc | hc
    · simpa [hc] using h2
    · rw [hc] at h2
      simpa using h2
  obtain ⟨Y, Z, hYZ⟩ := jF_ker_decomp 𝕜 E B p k q V hVcyc hker
  exact ⟨Y, Z, hYZ⟩

end Work.Pi6.MSS
