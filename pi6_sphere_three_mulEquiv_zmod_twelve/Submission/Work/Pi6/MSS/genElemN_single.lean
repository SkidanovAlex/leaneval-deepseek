import Mathlib
import Submission.Work.SSSR.serreE1Assembly
import Submission.Work.SSSR.serreE1PieceIotaDefs
import Submission.Work.Pi6.MSS.e2PsiCanonN
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

set_option autoImplicit false

namespace Work.Pi6.MSS

open CategoryTheory CategoryTheory.Limits

noncomputable section

/-- An isomorphism of modules is surjective on the underlying sets, spelled as an
existence statement (the element-level form used below). -/
lemma exists_preimage_iso_hom {R : Type} [CommRing R] [Nontrivial R] {M N : ModuleCat R}
    (e : M ≅ N) (m : N) : ∃ y : M, (ModuleCat.Hom.hom e.hom) y = m := by
  refine ⟨(ModuleCat.Hom.hom e.inv) m, ?_⟩
  have h := congrArg (fun (g : N ⟶ N) => (ModuleCat.Hom.hom g) m) (Iso.inv_hom_id e)
  rw [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id, LinearMap.id_apply] at h
  exact h

/-- Every homology class of a chain complex of modules is represented by the homology class of an
explicit cycle: the projection `cycles → homology` is surjective and `cyclesMk` is a section of the
inclusion of the cycles into the chain complex. -/
lemma exists_cyclesMk_homologyπ {R : Type} [CommRing R] [Nontrivial R]
    (K : ChainComplex (ModuleCat R) ℕ) (q : ℕ) (y : K.homology q) :
    ∃ (z : K.X q) (hz : (ModuleCat.Hom.hom (K.d q ((ComplexShape.down ℕ).next q))) z = 0),
      (ModuleCat.Hom.hom (K.homologyπ q))
        (K.cyclesMk z ((ComplexShape.down ℕ).next q) rfl hz) = y := by
  obtain ⟨c, hc⟩ := (ModuleCat.epi_iff_surjective (K.homologyπ q)).mp inferInstance y
  have hz : (ModuleCat.Hom.hom (K.d q ((ComplexShape.down ℕ).next q)))
      ((ModuleCat.Hom.hom (K.iCycles q)) c) = 0 :=
    congrArg (fun (g : K.cycles q ⟶ K.X ((ComplexShape.down ℕ).next q)) =>
      (ModuleCat.Hom.hom g) c) (K.iCycles_d q ((ComplexShape.down ℕ).next q))
  refine ⟨(ModuleCat.Hom.hom (K.iCycles q)) c, hz, ?_⟩
  have h2 : K.cyclesMk ((ModuleCat.Hom.hom (K.iCycles q)) c) ((ComplexShape.down ℕ).next q)
      rfl hz = c := by
    apply (Preadditive.mono_iff_injective (K.iCycles q)).1 inferInstance
    exact HomologicalComplex.i_cyclesMk (K := K) ((ModuleCat.Hom.hom (K.iCycles q)) c)
      ((ComplexShape.down ℕ).next q) rfl hz
  rw [h2]
  exact hc

theorem genElemN_single (𝕜 : Type) [Field 𝕜] (E B : Type) [TopologicalSpace E] [TopologicalSpace B]
    (p : C(E, B)) (e₀ : E) (hfib : Work.StemsB.IsSerreFibration p)
    (hconn : Work.PiS.SimplyConn B (p e₀)) (n q : ℕ)
    (σ : Work.SSSR.nIndex (Work.SSSR.sSing B) n)
    (m : ↥(Work.SSSR.coefM (R := 𝕜) p e₀ q)) :
    ∃ (z : (Work.SSSR.fibreCC (R := 𝕜) p
        (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).X q)
      (hz : (ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).d q
          ((ComplexShape.down ℕ).next q))) z = 0),
      (ModuleCat.Hom.hom (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
          (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).hom)
        ((ModuleCat.Hom.hom ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).homologyπ q))
          ((Work.SSSR.fibreCC (R := 𝕜) p
            (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))).cyclesMk z
            ((ComplexShape.down ℕ).next q) rfl hz)) = m := by
  classical
  obtain ⟨y, hy⟩ := exists_preimage_iso_hom
    (Work.SSSR.triv (R := 𝕜) p e₀ hfib hconn q
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))) m
  obtain ⟨z, hz, hzy⟩ := exists_cyclesMk_homologyπ
    (K := Work.SSSR.fibreCC (R := 𝕜) p
      (Work.SSSR.sigmaVert (Work.SSSR.nIndexSigma (Work.SSSR.sSing B) n σ))) q y
  exact ⟨z, hz, by rw [hzy, hy]⟩

end

end Work.Pi6.MSS
