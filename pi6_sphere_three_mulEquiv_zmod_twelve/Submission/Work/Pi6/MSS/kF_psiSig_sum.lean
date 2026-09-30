import Mathlib
import Submission.Work.SSSR.kF_psiCoef_gen
import Submission.Work.SSSR.serreE1Main
import Submission.Work.SSSR.serreE1CruxDefs
import Submission.Work.SSSR.FirstPage.HomElts
import Submission.Work.PiS.Interfaces
import Submission.Work.StemsB.Fibrations
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits Simplicial Opposite MonoidalCategory
open scoped MonoidalCategory Simplicial Topology

set_option maxHeartbeats 1600000
set_option backward.isDefEq.respectTransparency false

/-! ## Linearity of the cycle class `homologyπ ∘ cyclesMk`

Bookkeeping lemmas for chain complexes of `𝕜`-modules: the class of a cycle is additive and
`𝕜`-homogeneous in the underlying chain element.  They are used to distribute `kF ∘ PsiSig` over a
finite `𝕜`-linear combination of generators in `kF_psiSig_sum`. -/

/-- `iCycles` of `cyclesMk` (the module-level form, avoiding the `forget₂ _ Ab` bookkeeping
of `HomologicalComplex.i_cyclesMk`). -/
private lemma iCycles_cyclesMk_mod {𝕜 : Type} [Field 𝕜] {K : ChainComplex (ModuleCat 𝕜) ℕ} {a : ℕ}
    (x : K.X a) (j : ℕ) (hj : (ComplexShape.down ℕ).next a = j) (hx : (K.d a j).hom x = 0) :
    (K.iCycles a).hom (K.cyclesMk x j hj hx) = x := by
  simpa using HomologicalComplex.i_cyclesMk (K := K) (x := x) (j := j) (hj := hj) (hx := hx)

/-- `cyclesMk` re-typed with the module-level carrier of the cycles, so that the `𝕜`-scalar
structure is available on its values. -/
private noncomputable def cycMkMod {𝕜 : Type} [Field 𝕜] (K : ChainComplex (ModuleCat 𝕜) ℕ)
    {i : ℕ} (x : K.X i) (j : ℕ) (hj : (ComplexShape.down ℕ).next i = j)
    (hx : (K.d i j).hom x = 0) : K.cycles i :=
  K.cyclesMk x j hj hx

/-- **The cycle class is `𝕜`-linear.**  For a finite family of cycles `x j` and coefficients
`a j`, the class of the cycle `∑ j, a j • x j` is `∑ j, a j •` the class of `x j`. -/
private lemma homologyπ_cyclesMk_sum_smul {𝕜 : Type} [Field 𝕜]
    {K : ChainComplex (ModuleCat 𝕜) ℕ} {i : ℕ} {ι : Type} (s : Finset ι) (a : ι → 𝕜)
    (x : ι → K.X i)
    (hx : ∀ j : ι, (K.d i ((ComplexShape.down ℕ).next i)).hom (x j) = 0)
    (h : (K.d i ((ComplexShape.down ℕ).next i)).hom (∑ j ∈ s, a j • x j) = 0) :
    (K.homologyπ i).hom (K.cyclesMk (∑ j ∈ s, a j • x j) ((ComplexShape.down ℕ).next i) rfl h)
      = ∑ j ∈ s, a j • (K.homologyπ i).hom
          (K.cyclesMk (x j) ((ComplexShape.down ℕ).next i) rfl (hx j)) := by
  have key : cycMkMod K (∑ j ∈ s, a j • x j) ((ComplexShape.down ℕ).next i) rfl h
      = ∑ j ∈ s, a j • cycMkMod K (x j) ((ComplexShape.down ℕ).next i) rfl (hx j) := by
    apply (ModuleCat.mono_iff_injective (K.iCycles i)).1 inferInstance
    simp only [cycMkMod, map_sum, map_smul, iCycles_cyclesMk_mod]
  show (K.homologyπ i).hom (cycMkMod K (∑ j ∈ s, a j • x j) ((ComplexShape.down ℕ).next i) rfl h)
      = ∑ j ∈ s, a j • (K.homologyπ i).hom
          (cycMkMod K (x j) ((ComplexShape.down ℕ).next i) rfl (hx j))
  rw [key, map_sum]
  exact Finset.sum_congr rfl (fun j _ => by rw [map_smul])

theorem kF_psiSig_sum (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E]
    [TopologicalSpace B] (p : C(E, B)) (e₀ : E)
    (hfib : Work.StemsB.IsSerreFibration p) (hconn : Work.PiS.SimplyConn B (p e₀))
    (k q : ℕ) (c : ℕ → ℤ) (hc1 : ∀ n : ℕ, c n = 1 ∨ c n = -1)
    (hal : Work.SSSR.PieceAlpha (R := 𝕜) p hfib c)
    (n : ℕ) (lam : Fin n → 𝕜)
    (σ : Fin n → Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1))
    (z : ∀ j : Fin n, (Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).X q)
    (hz : ∀ j : Fin n, (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).d q ((ComplexShape.down ℕ).next q))) (z j) = 0)
    (hcyc : ∀ j : Fin n, (ModuleCat.Hom.hom (((Work.SSSR.Fc (R := 𝕜) p).obj k).d (k+q)
      ((ComplexShape.down ℕ).next (k+q))))
      (Work.SSSR.faceSum p hfib k q (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))
        (Work.SSSR.sigHat (σ j)) rfl (z j)) = 0)
    (hcycSum : (ModuleCat.Hom.hom (((Work.SSSR.Fc (R := 𝕜) p).obj k).d (k+q)
      ((ComplexShape.down ℕ).next (k+q))))
      (∑ j : Fin n, lam j • Work.SSSR.faceSum p hfib k q
        (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j))) (Work.SSSR.sigHat (σ j)) rfl (z j)) = 0) :
    (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) k q))
      ((ModuleCat.Hom.hom (Work.SSSR.PsiSig p e₀ hfib hconn q (k+1)))
        (∑ j : Fin n, lam j •
          (CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1) =>
              Work.SSSR.coefM (R := 𝕜) p e₀ q) (σ j))
            ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom)
              ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).homologyπ q))
                ((Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).cyclesMk (z j)
                  ((ComplexShape.down ℕ).next q) rfl (hz j))))))
    = c (k+1) • ((Work.SSSR.Fc (R := 𝕜) p).obj k).homologyπ (k+q)
        (((Work.SSSR.Fc (R := 𝕜) p).obj k).cyclesMk
          (∑ j : Fin n, lam j • Work.SSSR.faceSum p hfib k q
            (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j))) (Work.SSSR.sigHat (σ j)) rfl (z j))
          ((ComplexShape.down ℕ).next (k+q)) rfl hcycSum) := by
  -- `PsiSig` is additive and `𝕜`-homogeneous
  have hPsi_lin : (ModuleCat.Hom.hom (Work.SSSR.PsiSig p e₀ hfib hconn q (k+1)))
        (∑ j : Fin n, lam j •
          (CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1) =>
              Work.SSSR.coefM (R := 𝕜) p e₀ q) (σ j))
            ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom)
              ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).homologyπ q))
                ((Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).cyclesMk (z j)
                  ((ComplexShape.down ℕ).next q) rfl (hz j)))))
      = ∑ j : Fin n, lam j • (ModuleCat.Hom.hom (Work.SSSR.PsiSig p e₀ hfib hconn q (k+1)))
          ((CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1) =>
              Work.SSSR.coefM (R := 𝕜) p e₀ q) (σ j))
            ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom)
              ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).homologyπ q))
                ((Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).cyclesMk (z j)
                  ((ComplexShape.down ℕ).next q) rfl (hz j))))) := by
    rw [map_sum]
    exact Finset.sum_congr rfl (fun j _ => by rw [map_smul])
  -- the `σ j`-component of `PsiSig` is the first-page comparison map
  have hgen : ∀ j : Fin n,
      (ModuleCat.Hom.hom (Work.SSSR.PsiSig p e₀ hfib hconn q (k+1)))
        ((CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1) =>
            Work.SSSR.coefM (R := 𝕜) p e₀ q) (σ j))
          ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
            (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom)
            ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).homologyπ q))
              ((Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).cyclesMk (z j)
                ((ComplexShape.down ℕ).next q) rfl (hz j)))))
      = (ModuleCat.Hom.hom ((Work.SSSR.PsiCoef p e₀ hfib hconn q (k+1) (σ j)).hom ≫
          HomologicalComplex.homologyMap (Work.SSSR.mapPhiY 𝕜 (Work.SSSR.sSingP p) (k+1)
            (σ j)) ((k+1)+q)))
        ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
          (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom)
          ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).homologyπ q))
            ((Work.SSSR.fibreCC (R := 𝕜) p
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).cyclesMk (z j)
              ((ComplexShape.down ℕ).next q) rfl (hz j)))) := by
    intro j
    rw [← ModuleCat.comp_apply (CategoryTheory.Limits.Sigma.ι
          (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1) => Work.SSSR.coefM (R := 𝕜) p e₀ q) (σ j))
        (Work.SSSR.PsiSig p e₀ hfib hconn q (k+1)) _]
    rw [Work.SSSR.Sigma_ι_comp_PsiSig (R := 𝕜) p e₀ hfib hconn q (k+1) (σ j)]
  -- the generator-level evaluation of `kF ∘ PsiSig`
  have hstep : ∀ j : Fin n,
      (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) k q))
        ((ModuleCat.Hom.hom (Work.SSSR.PsiSig p e₀ hfib hconn q (k+1)))
          ((CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1) =>
              Work.SSSR.coefM (R := 𝕜) p e₀ q) (σ j))
            ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom)
              ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).homologyπ q))
                ((Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).cyclesMk (z j)
                  ((ComplexShape.down ℕ).next q) rfl (hz j))))))
      = c (k+1) • (ModuleCat.Hom.hom (((Work.SSSR.Fc (R := 𝕜) p).obj k).homologyπ (k+q)))
          (((Work.SSSR.Fc (R := 𝕜) p).obj k).cyclesMk
            (Work.SSSR.faceSum p hfib k q (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))
              (Work.SSSR.sigHat (σ j)) rfl (z j))
            ((ComplexShape.down ℕ).next (k+q)) rfl (hcyc j)) := by
    intro j
    rw [hgen j]
    exact Work.SSSR.kF_psiCoef_gen (R := 𝕜) p e₀ hfib hconn q c hc1 hal k (σ j) (z j) (hz j) (hcyc j)
  calc
    (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) k q))
      ((ModuleCat.Hom.hom (Work.SSSR.PsiSig p e₀ hfib hconn q (k+1)))
        (∑ j : Fin n, lam j •
          (CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1) =>
              Work.SSSR.coefM (R := 𝕜) p e₀ q) (σ j))
            ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom)
              ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).homologyπ q))
                ((Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).cyclesMk (z j)
                  ((ComplexShape.down ℕ).next q) rfl (hz j))))))
    _ = (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) k q))
        (∑ j : Fin n, lam j • (ModuleCat.Hom.hom (Work.SSSR.PsiSig p e₀ hfib hconn q (k+1)))
          ((CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1) =>
              Work.SSSR.coefM (R := 𝕜) p e₀ q) (σ j))
            ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom)
              ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).homologyπ q))
                ((Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).cyclesMk (z j)
                  ((ComplexShape.down ℕ).next q) rfl (hz j)))))) := by
      rw [hPsi_lin]
    _ = ∑ j : Fin n, lam j • (ModuleCat.Hom.hom (Work.SSSR.kF (Work.SSSR.xiCan p) k q))
          ((ModuleCat.Hom.hom (Work.SSSR.PsiSig p e₀ hfib hconn q (k+1)))
            ((CategoryTheory.Limits.Sigma.ι (fun _ : Work.SSSR.nIndex (Work.SSSR.sSing B) (k+1) =>
                Work.SSSR.coefM (R := 𝕜) p e₀ q) (σ j))
              ((ModuleCat.Hom.hom (Work.SSSR.triv p e₀ hfib hconn q
                (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).hom)
                ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
                  (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).homologyπ q))
                  ((Work.SSSR.fibreCC (R := 𝕜) p
                    (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))).cyclesMk (z j)
                    ((ComplexShape.down ℕ).next q) rfl (hz j)))))) := by
      rw [map_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [map_smul])
    _ = ∑ j : Fin n, lam j • (c (k+1) • (ModuleCat.Hom.hom (((Work.SSSR.Fc (R := 𝕜) p).obj k).homologyπ (k+q)))
          (((Work.SSSR.Fc (R := 𝕜) p).obj k).cyclesMk
            (Work.SSSR.faceSum p hfib k q (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))
              (Work.SSSR.sigHat (σ j)) rfl (z j))
            ((ComplexShape.down ℕ).next (k+q)) rfl (hcyc j))) := by
      exact Finset.sum_congr rfl (fun j _ => by rw [hstep j])
    _ = c (k+1) • ∑ j : Fin n, lam j • (ModuleCat.Hom.hom (((Work.SSSR.Fc (R := 𝕜) p).obj k).homologyπ (k+q)))
          (((Work.SSSR.Fc (R := 𝕜) p).obj k).cyclesMk
            (Work.SSSR.faceSum p hfib k q (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j)))
              (Work.SSSR.sigHat (σ j)) rfl (z j))
            ((ComplexShape.down ℕ).next (k+q)) rfl (hcyc j)) := by
      rw [Finset.smul_sum]
      exact Finset.sum_congr rfl (fun j _ => by rw [smul_comm])
    _ = c (k+1) • (ModuleCat.Hom.hom (((Work.SSSR.Fc (R := 𝕜) p).obj k).homologyπ (k+q)))
          (((Work.SSSR.Fc (R := 𝕜) p).obj k).cyclesMk
            (∑ j : Fin n, lam j • Work.SSSR.faceSum p hfib k q
              (Work.SSSR.sigmaVert (Work.SSSR.sigHat (σ j))) (Work.SSSR.sigHat (σ j)) rfl (z j))
            ((ComplexShape.down ℕ).next (k+q)) rfl hcycSum) := by
      rw [← homologyπ_cyclesMk_sum_smul (s := Finset.univ) (h := hcycSum)]

end Work.Pi6.MSS
