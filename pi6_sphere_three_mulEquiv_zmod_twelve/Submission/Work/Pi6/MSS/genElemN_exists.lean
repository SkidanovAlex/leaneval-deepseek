import Mathlib
import Submission.Work.Pi6.MSS.e2PsiCanonN
import Submission.Work.Pi6.MSS.coprod_fin_decomp
import Submission.Work.Pi6.MSS.genElemN_single
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite
open scoped Simplicial

/-- **Every element of the `E¹` page of the Serre spectral sequence is a sum of canonical
generators.**  The coefficient isomorphism `serreE1CoefIsoIso` identifies `(N_*(B) ⊗ H_q(F))_n`
with the coproduct `∐_{σ ∈ nIndex} H_q(F)`; an element of a direct sum of modules is a finite sum
of its coordinates, and each coordinate is the image of a cycle of the corresponding fibre chain
complex under `triv_σ ∘ homologyπ`. -/
theorem genElemN_exists (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ)
    (x : (Work.SSSR.tensorComplex 𝕜 (Work.SSSR.Nn B) (Work.SSSR.coefM (R := 𝕜) p e₀ q)).X n) :
    ∃ (k : ℕ) (lam : Fin k → 𝕜) (σ : Fin k → Work.SSSR.nIndex (Work.SSSR.sSing B) n)
      (z : ∀ j : Fin k, (Work.SSSR.fibreCC (R := 𝕜) p
        (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).X q)
      (hz : ∀ j : Fin k, (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
        (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).d q
        ((ComplexShape.down ℕ).next q))) (z j) = 0),
      Work.Pi6.MSS.genElemN 𝕜 p e₀ hfib hconn n q k lam σ z hz = x := by
  classical
  let ι := Work.SSSR.nIndex (Work.SSSR.sSing B) n
  let Mf : ι → ModuleCat 𝕜 := fun _ => Work.SSSR.coefM (R := 𝕜) p e₀ q
  let E1 := Work.SSSR.serreE1CoefIsoIso (Work.SSSR.sSing B) (Work.SSSR.coefM (R := 𝕜) p e₀ q) n
  let y : (∐ (fun i => Mf i) : ModuleCat 𝕜) := (ModuleCat.Hom.hom E1.inv) x
  -- `y` is `x` read in the coproduct `∐_{σ ∈ nIndex} H_q(F)`
  have hxy : (ModuleCat.Hom.hom E1.hom) y = x := by
    have h := congrArg (fun f => ModuleCat.Hom.hom f x) (Iso.inv_hom_id E1)
    simpa only [ModuleCat.hom_comp, ModuleCat.hom_id, LinearMap.comp_apply, LinearMap.id_apply, y]
      using h
  -- `y` is a finite sum of coordinates
  obtain ⟨k, σ, v, hv⟩ := Work.Pi6.MSS.coprod_fin_decomp Mf y
  -- each coordinate is the class of a cycle of the fibre over the vertical of `σ`
  have hstep : ∀ j : Fin k, ∃ (z : (Work.SSSR.fibreCC (R := 𝕜) p
        (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).X q)
      (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
        (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).d q
        ((ComplexShape.down ℕ).next q))) z = 0),
      (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).hom)
        ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).homologyπ q))
          ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).cyclesMk z
            ((ComplexShape.down ℕ).next q) rfl hz)) = v j :=
    fun j => Work.Pi6.MSS.genElemN_single 𝕜 E B p e₀ hfib hconn n q (σ j) (v j)
  choose z hz hztriv using hstep
  refine ⟨k, fun _ => 1, σ, z, hz, ?_⟩
  rw [Work.Pi6.MSS.genElemN]
  have h1 : (∑ j : Fin k, (1:𝕜) • (CategoryTheory.Limits.Sigma.ι Mf (σ j))
      ((ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).hom)
        ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).homologyπ q))
          ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n (σ j)))).cyclesMk
            (z j) ((ComplexShape.down ℕ).next q) rfl (hz j))))) = y := by
    rw [hv]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [one_smul, hztriv j]
  rw [h1]
  exact hxy

end Work.Pi6.MSS
