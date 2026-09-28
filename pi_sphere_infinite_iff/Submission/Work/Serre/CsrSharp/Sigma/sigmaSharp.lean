import Mathlib
import Submission.Work.Serre.CsrSharp.Defs
import Submission.Work.Serre.csrDefs
import Submission.Work.Serre.csrGlue
import Submission.Work.Serre.sigmaChainsIso
import Submission.Work.Serre.sigmaHomologyRat
import Submission.Work.Serre.sigmaRelChainsIso
import Submission.Work.Serre.cokernel_coproduct_iso
import Submission.Work.Serre.chainComplexFunctor_preserves_coproduct
import Submission.Work.Serre.sigmaToSSetHom_isIso
import Submission.Work.Serre.homology_coproduct_iso
import Submission.Work.Serre.csrSigmaAdditivityProved

/-!
# Additivity of relative rational homology over a disjoint union of pairs

This file proves `Work.Serre.CsrSharp.SigmaIso`, the additivity of relative singular homology
with `ℚ`-coefficients over a disjoint union of pairs, in the sharp form needed by the cell-step
argument (isomorphisms *and* surjectivity in the top degree).

The two ingredients are already in the tree:

* the *isomorphism* half is `Work.Serre.csrSigmaAdditivity` (`Submission/Work/Serre/csrSigmaAdditivity.lean`,
  restated as `csrSigmaAdditivityProved`);
* the decomposition of the relative chain complex of a disjoint union into the coproduct of the
  relative chain complexes of the pieces, naturally in a family of maps of pairs, is
  `Work.Serre.relChainsCoproductSquareRat` (`Submission/Work/Serre/sigmaPairIso.lean`), and the
  homology of a coproduct of chain complexes of `ℚ`-modules is the coproduct of the homologies
  (`Work.Serre.sigmaHomologyMap`, `Submission/Work/Serre/sigmaHomologyRat.lean`).

The surjectivity half is the same square argument, with "epi"/surjectivity replacing "iso": a
coproduct of surjections is surjective, and `Work.Serre.sigmaHomologyMap` is an isomorphism, so the
map of the disjoint union is surjective whenever its pieces are.
-/

open scoped Topology
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.CsrSharp.Sigma

noncomputable section

/-- **Surjectivity of the coproduct of a family of chain maps.**  If every member of a family of
chain maps `f i : K i ⟶ L i` of chain complexes of `ℚ`-modules induces a surjection on `H_m`, then
so does the coproduct `∐ i, f i`.

This is the "surjectivity" companion of `Work.Serre.isIso_homologyMap_sigma`: the comparison
`Work.Serre.sigmaHomologyMap` is an isomorphism, so it is harmless, and a coproduct of surjections
is surjective (`Limits.Sigma.map_epi`). -/
lemma surjective_homologyMap_sigma {ι : Type} {K L : ι → ChainComplex (ModuleCat ℚ) ℕ}
    (f : ∀ i, K i ⟶ L i) (m : ℕ)
    (h : ∀ i, Function.Surjective (HomologicalComplex.homologyMap (f i) m).hom) :
    Function.Surjective (HomologicalComplex.homologyMap (Limits.Sigma.map f) m).hom := by
  have hE : ∀ i, Epi (HomologicalComplex.homologyMap (f i) m) :=
    fun i => (ModuleCat.epi_iff_surjective _).mpr (h i)
  haveI hL : IsIso (Work.Serre.sigmaHomologyMap L m) := Work.Serre.isIso_sigmaHomologyMap L m
  haveI hK : IsIso (Work.Serre.sigmaHomologyMap K m) := Work.Serre.isIso_sigmaHomologyMap K m
  have hepi : Epi (Work.Serre.sigmaHomologyMap K m
      ≫ HomologicalComplex.homologyMap (Limits.Sigma.map f) m) := by
    rw [← Work.Serre.homologyMap_sigma_natural f m]
    haveI : ∀ i, Epi (HomologicalComplex.homologyMap (f i) m) := hE
    infer_instance
  haveI : Epi (HomologicalComplex.homologyMap (Limits.Sigma.map f) m) :=
    (epi_comp_iff_of_epi (Work.Serre.sigmaHomologyMap K m) _).mp hepi
  exact (ModuleCat.epi_iff_surjective _).mp inferInstance

/-- **Surjectivity half of the additivity of relative homology over a disjoint union of pairs.**
If for every `i` the map of pairs `(X i, A i) → (Y i, B i)` is surjective on relative `ℚ`-homology
in degree `m`, then so is the map of pairs
`(Σ i, X i, Σ i, A i) → (Σ i, Y i, Σ i, B i)`.

This is `Work.Serre.csrSigmaAdditivity` with isomorphisms relaxed to surjections. -/
lemma surjective_relChainsSigma {ι : Type} {X Y : ι → Type}
    [∀ i, TopologicalSpace (X i)] [∀ i, TopologicalSpace (Y i)]
    (A : ∀ i, Set (X i)) (B : ∀ i, Set (Y i)) (g : ∀ i, C(X i, Y i))
    (hg : ∀ i, Set.MapsTo (g i) (A i) (B i)) (m : ℕ)
    (h : ∀ i, Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i)) m).hom) :
    Function.Surjective (HomologicalComplex.homologyMap
      (Work.Serre.relChainsRPairMap {x : (Σ i, X i) | x.2 ∈ A x.1}
        {x : (Σ i, Y i) | x.2 ∈ B x.1}
        ⟨Sigma.map id (fun i => g i), by fun_prop⟩
        (by rintro ⟨i, x⟩ hx; exact hg i hx)) m).hom := by
  obtain ⟨eX, eY, hsq⟩ := Work.Serre.relChainsCoproductSquareRat A B g hg
  have hsigma : Function.Surjective (HomologicalComplex.homologyMap
      (Limits.Sigma.map (fun i => Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i))) m).hom :=
    surjective_homologyMap_sigma _ m h
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
  haveI : Epi (HomologicalComplex.homologyMap (Limits.Sigma.map
      (fun i => Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i))) m) :=
    (ModuleCat.epi_iff_surjective _).mpr hsigma
  have hepi : Epi (HomologicalComplex.homologyMap eX.hom m
      ≫ (HomologicalComplex.homologyMap (Limits.Sigma.map
            (fun i => Work.Serre.relChainsRPairMap (A i) (B i) (g i) (hg i))) m
          ≫ inv (HomologicalComplex.homologyMap eY.hom m))) := inferInstance
  exact (ModuleCat.epi_iff_surjective _).mp hepi

/-- **Additivity of relative rational homology over a disjoint union of pairs**, in the sharp form
needed by the cell-step argument: isomorphisms in every degree, and surjectivity in the boundary
degree.  This is the interface `Work.Serre.CsrSharp.SigmaIso`. -/
theorem sigmaSharp : Work.Serre.CsrSharp.SigmaIso := by
  intro ι X Y hX hY A B g hg m
  exact ⟨fun h => Work.Serre.csrSigmaAdditivityProved A B g hg m h,
    fun h => surjective_relChainsSigma A B g hg m h⟩

end

end Work.Serre.CsrSharp.Sigma
