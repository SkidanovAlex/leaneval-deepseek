import Mathlib
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.sigmaChainsIso
import Submission.Work.Serre.sigmaSSetDefs
import Submission.Work.Serre.sigmaToSSetHom_isIso
import Submission.Work.Serre.chainComplexFunctor_preserves_coproduct
import Submission.Work.Serre.cokernel_coproduct_iso
import Submission.Work.Serre.coprodChainAux
import Submission.Work.Serre.sigmaHomologyRat
import Submission.Work.Serre.sigmaPairIso

set_option maxHeartbeats 1600000

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre

noncomputable section

/-- **Additivity of relative singular homology over `ℚ` for a disjoint union of pairs.**  For a
family of pairs `(X i, A i) → (Y i, B i)` (with `A i ⊆ X i`, `B i ⊆ Y i`), the relative chain
complex of the disjoint union `Σ i, X i` relative to `Σ i, A i` is the direct sum of those of the
pieces, and the map induced by the family corresponds to the coproduct of the maps; hence if each
piece induces an isomorphism on `H_m`, so does the disjoint union. -/
theorem csrSigmaAdditivity {ι : Type} {X Y : ι → Type}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (A : ∀ i, Set (X i)) (B : ∀ i, Set (Y i)) (g : ∀ i, C(X i, Y i))
    (hg : ∀ i, Set.MapsTo (g i) (A i) (B i)) (m : ℕ)
    (h : ∀ i, CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i)) m)) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap {x : (Σ i, X i) | x.2 ∈ A x.1}
        {x : (Σ i, Y i) | x.2 ∈ B x.1}
        ⟨Sigma.map id (fun i => g i), by fun_prop⟩
        (by rintro ⟨i, x⟩ hx; exact hg i hx)) m) := by
  obtain ⟨eX, eY, hsq⟩ := relChainsCoproductSquareRat A B g hg
  haveI hadd : IsIso (HomologicalComplex.homologyMap
      (Limits.Sigma.map (fun i => Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i))) m) :=
    isIso_homologyMap_sigma (fun i => Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i)) m h
  haveI heX : IsIso (HomologicalComplex.homologyMap eX.hom m) :=
    Iso.isIso_hom (HomologicalComplex.homologyMapIso eX m)
  haveI heY : IsIso (HomologicalComplex.homologyMap eY.hom m) :=
    Iso.isIso_hom (HomologicalComplex.homologyMapIso eY m)
  have hsq' : HomologicalComplex.homologyMap eX.hom m
        ≫ HomologicalComplex.homologyMap (Limits.Sigma.map
            (fun i => Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i))) m
      = HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
            {x : (Σ i, X i) | x.2 ∈ A x.1} {x : (Σ i, Y i) | x.2 ∈ B x.1}
            ⟨Sigma.map id (fun i => g i), by fun_prop⟩
            (by rintro ⟨i, x⟩ hx; exact hg i hx)) m
        ≫ HomologicalComplex.homologyMap eY.hom m := by
    calc HomologicalComplex.homologyMap eX.hom m
          ≫ HomologicalComplex.homologyMap (Limits.Sigma.map
              (fun i => Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i))) m
        = HomologicalComplex.homologyMap
            (eX.hom ≫ Limits.Sigma.map
              (fun i => Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i))) m :=
          (HomologicalComplex.homologyMap_comp eX.hom _ m).symm
      _ = HomologicalComplex.homologyMap
            (Work.Serre.relChainsRPairMap
              {x : (Σ i, X i) | x.2 ∈ A x.1} {x : (Σ i, Y i) | x.2 ∈ B x.1}
              ⟨Sigma.map id (fun i => g i), by fun_prop⟩
              (by rintro ⟨i, x⟩ hx; exact hg i hx)
              ≫ eY.hom) m := by rw [hsq]
      _ = HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
              {x : (Σ i, X i) | x.2 ∈ A x.1} {x : (Σ i, Y i) | x.2 ∈ B x.1}
              ⟨Sigma.map id (fun i => g i), by fun_prop⟩
              (by rintro ⟨i, x⟩ hx; exact hg i hx)) m
          ≫ HomologicalComplex.homologyMap eY.hom m :=
          HomologicalComplex.homologyMap_comp _ eY.hom m
  have hX : HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
              {x : (Σ i, X i) | x.2 ∈ A x.1} {x : (Σ i, Y i) | x.2 ∈ B x.1}
              ⟨Sigma.map id (fun i => g i), by fun_prop⟩
              (by rintro ⟨i, x⟩ hx; exact hg i hx)) m
      = HomologicalComplex.homologyMap eX.hom m
        ≫ (HomologicalComplex.homologyMap (Limits.Sigma.map
              (fun i => Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i))) m
            ≫ inv (HomologicalComplex.homologyMap eY.hom m)) := by
    calc HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
              {x : (Σ i, X i) | x.2 ∈ A x.1} {x : (Σ i, Y i) | x.2 ∈ B x.1}
              ⟨Sigma.map id (fun i => g i), by fun_prop⟩
              (by rintro ⟨i, x⟩ hx; exact hg i hx)) m
        = HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
              {x : (Σ i, X i) | x.2 ∈ A x.1} {x : (Σ i, Y i) | x.2 ∈ B x.1}
              ⟨Sigma.map id (fun i => g i), by fun_prop⟩
              (by rintro ⟨i, x⟩ hx; exact hg i hx)) m
            ≫ HomologicalComplex.homologyMap eY.hom m
            ≫ inv (HomologicalComplex.homologyMap eY.hom m) := by
          rw [IsIso.hom_inv_id, Category.comp_id]
      _ = (HomologicalComplex.homologyMap (Work.Serre.relChainsRPairMap
              {x : (Σ i, X i) | x.2 ∈ A x.1} {x : (Σ i, Y i) | x.2 ∈ B x.1}
              ⟨Sigma.map id (fun i => g i), by fun_prop⟩
              (by rintro ⟨i, x⟩ hx; exact hg i hx)) m
            ≫ HomologicalComplex.homologyMap eY.hom m)
            ≫ inv (HomologicalComplex.homologyMap eY.hom m) := (Category.assoc _ _ _).symm
      _ = (HomologicalComplex.homologyMap eX.hom m
            ≫ HomologicalComplex.homologyMap (Limits.Sigma.map
              (fun i => Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i))) m)
            ≫ inv (HomologicalComplex.homologyMap eY.hom m) := by rw [← hsq']
      _ = HomologicalComplex.homologyMap eX.hom m
          ≫ (HomologicalComplex.homologyMap (Limits.Sigma.map
              (fun i => Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i))) m
            ≫ inv (HomologicalComplex.homologyMap eY.hom m)) := Category.assoc _ _ _
  rw [hX]
  infer_instance

end

end Work.Serre
