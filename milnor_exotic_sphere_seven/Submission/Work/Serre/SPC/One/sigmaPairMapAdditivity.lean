import Mathlib
import Submission.Work.Serre.SPC.One.SigmaDefs
import Submission.Work.Serre.CellStep.sigmaAdditivity

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# Additivity of relative homology over a disjoint union

`Work.Serre.SPC.One.sigmaPairMapAdditivity` : the relative chain map of a *family* of maps of pairs
on a disjoint union is the coproduct of the individual maps
(`Work.Serre.CellStep.relChainsCoproductSquare`, proved in
`Submission/Work/Serre/CellStep/sigmaAdditivity.lean`), and (relative) homology — being a
functor from chain complexes of `ℤ`-modules — carries the coproduct of a family of chain maps to
the coproduct of the induced maps.  Hence the union map is an isomorphism on `H_m` as soon as every
piece map is, and it is surjective on `H_m` as soon as every piece map is.

The relative chain maps `pairMap` and `sigmaPairMap` of this area are *definitionally* the ones used
in `Work.Serre` (`Work.Serre.pairMap`, `Work.Serre.sigmaPairMap`), so the additivity statement
proved there applies verbatim; the only new ingredient is the surjectivity half, whose coproduct
argument is the `Epi`-analogue of `Work.Serre.CellStep.isIso_homologyMap_sigma`.
-/

set_option linter.style.haveILetI false

open scoped Topology unitInterval
open CategoryTheory CategoryTheory.Limits

namespace Work.Serre.SPC.One

noncomputable section

/-- The relative chain map of a single map of pairs of the `SPC.One` area is the one of the
additivity theorem of `Work.Serre`, definitionally. -/
theorem pairMap_eq {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    (A : Set X) (B : Set Y) (g : C(X, Y)) (hg : Set.MapsTo g A B) :
    pairMap A B g hg = Work.Serre.pairMap A B g hg := rfl

/-- The relative chain map of a family of maps of pairs of the `SPC.One` area is the one of the
additivity theorem of `Work.Serre`, definitionally. -/
theorem sigmaPairMap_eq {ι : Type} {X Y : ι → Type} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (A : ∀ i, Set (X i)) (B : ∀ i, Set (Y i))
    (g : ∀ i, C(X i, Y i)) (hg : ∀ i, Set.MapsTo (g i) (A i) (B i)) :
    sigmaPairMap X Y A B g hg = Work.Serre.sigmaPairMap X Y A B g hg := rfl

theorem sigmaPairMapAdditivity {ι : Type} {X Y : ι → Type} [∀ i, TopologicalSpace (X i)]
    [∀ i, TopologicalSpace (Y i)] (A : ∀ i, Set (X i)) (B : ∀ i, Set (Y i))
    (g : ∀ i, ContinuousMap (X i) (Y i)) (hg : ∀ i, Set.MapsTo (g i) (A i) (B i)) :
    (∀ m : ℕ, (∀ i, CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Serre.SPC.One.pairMap (A i) (B i) (g i) (hg i)) m)) →
      CategoryTheory.IsIso (HomologicalComplex.homologyMap
        (Work.Serre.SPC.One.sigmaPairMap X Y A B g hg) m)) ∧
    (∀ m : ℕ, (∀ i, Function.Surjective (HomologicalComplex.homologyMap
        (Work.Serre.SPC.One.pairMap (A i) (B i) (g i) (hg i)) m).hom) →
      Function.Surjective (HomologicalComplex.homologyMap
        (Work.Serre.SPC.One.sigmaPairMap X Y A B g hg) m).hom) := by
  constructor
  · -- the isomorphism half: the map of pairs of the union is the coproduct of the piece maps
    intro m h
    exact Work.Serre.CellStep.sigmaAdditivity A B g hg m (fun i => h i)
  · -- the surjectivity half: a coproduct of surjections is surjective
    intro m h
    let K : ι → ChainComplex (ModuleCat ℤ) ℕ :=
      fun i => Work.Cohomology.relChains (TopCat.of (X i)) (A i)
    let L : ι → ChainComplex (ModuleCat ℤ) ℕ :=
      fun i => Work.Cohomology.relChains (TopCat.of (Y i)) (B i)
    let pm : ∀ i, K i ⟶ L i := fun i => Work.Serre.pairMap (A i) (B i) (g i) (hg i)
    haveI hEpi : ∀ i, CategoryTheory.Epi (HomologicalComplex.homologyMap (pm i) m) :=
      fun i => (ModuleCat.epi_iff_surjective _).mpr (h i)
    have hB : CategoryTheory.Epi (Limits.Sigma.map
        (fun i => HomologicalComplex.homologyMap (pm i) m)) := Limits.Sigma.map_epi _
    have hKiso : IsIso (Limits.Sigma.desc
        (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι K i) m)) :=
      Work.Serre.sigma_desc_sigmaι_isIso K m
    have hLiso : IsIso (Limits.Sigma.desc
        (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι L i) m)) :=
      Work.Serre.sigma_desc_sigmaι_isIso L m
    have hnat := Work.Serre.CellStep.sigma_desc_homologyMap_natural pm m
    -- the coproduct of the individual homology maps
    have hAeq : HomologicalComplex.homologyMap (Limits.Sigma.map pm) m
        = (asIso (Limits.Sigma.desc
              (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι K i) m))).inv
          ≫ (Limits.Sigma.map (fun i => HomologicalComplex.homologyMap (pm i) m)
              ≫ Limits.Sigma.desc (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι L i) m)) := by
      rw [← hnat]
      exact (Iso.inv_hom_id_assoc (asIso (Limits.Sigma.desc
          (fun i => HomologicalComplex.homologyMap (Limits.Sigma.ι K i) m))) _).symm
    haveI hA : CategoryTheory.Epi (HomologicalComplex.homologyMap (Limits.Sigma.map pm) m) := by
      rw [hAeq]
      infer_instance
    -- transport along the coproduct decomposition of the relative chains
    obtain ⟨eX, eY, hsq⟩ := Work.Serre.CellStep.relChainsCoproductSquare A B g hg
    haveI heX : IsIso (HomologicalComplex.homologyMap eX.hom m) :=
      Iso.isIso_hom (HomologicalComplex.homologyMapIso eX m)
    haveI heY : IsIso (HomologicalComplex.homologyMap eY.hom m) :=
      Iso.isIso_hom (HomologicalComplex.homologyMapIso eY m)
    have hsq' : HomologicalComplex.homologyMap eX.hom m
          ≫ HomologicalComplex.homologyMap (Limits.Sigma.map pm) m
        = HomologicalComplex.homologyMap (Work.Serre.sigmaPairMap X Y A B g hg) m
          ≫ HomologicalComplex.homologyMap eY.hom m := by
      calc HomologicalComplex.homologyMap eX.hom m
            ≫ HomologicalComplex.homologyMap (Limits.Sigma.map pm) m
          = HomologicalComplex.homologyMap (eX.hom ≫ Limits.Sigma.map pm) m :=
            (HomologicalComplex.homologyMap_comp eX.hom (Limits.Sigma.map pm) m).symm
        _ = HomologicalComplex.homologyMap
              (Work.Serre.sigmaPairMap X Y A B g hg ≫ eY.hom) m := by rw [hsq]
        _ = HomologicalComplex.homologyMap (Work.Serre.sigmaPairMap X Y A B g hg) m
            ≫ HomologicalComplex.homologyMap eY.hom m :=
            HomologicalComplex.homologyMap_comp (Work.Serre.sigmaPairMap X Y A B g hg) eY.hom m
    have hC_eq : HomologicalComplex.homologyMap (Work.Serre.sigmaPairMap X Y A B g hg) m
        = HomologicalComplex.homologyMap eX.hom m
          ≫ (HomologicalComplex.homologyMap (Limits.Sigma.map pm) m
              ≫ inv (HomologicalComplex.homologyMap eY.hom m)) := by
      calc HomologicalComplex.homologyMap (Work.Serre.sigmaPairMap X Y A B g hg) m
          = HomologicalComplex.homologyMap (Work.Serre.sigmaPairMap X Y A B g hg) m ≫ 𝟙 _ :=
            (Category.comp_id _).symm
        _ = HomologicalComplex.homologyMap (Work.Serre.sigmaPairMap X Y A B g hg) m
              ≫ (HomologicalComplex.homologyMap eY.hom m
                  ≫ inv (HomologicalComplex.homologyMap eY.hom m)) := by
            rw [IsIso.hom_inv_id]
        _ = (HomologicalComplex.homologyMap (Work.Serre.sigmaPairMap X Y A B g hg) m
              ≫ HomologicalComplex.homologyMap eY.hom m)
              ≫ inv (HomologicalComplex.homologyMap eY.hom m) := (Category.assoc _ _ _).symm
        _ = (HomologicalComplex.homologyMap eX.hom m
              ≫ HomologicalComplex.homologyMap (Limits.Sigma.map pm) m)
              ≫ inv (HomologicalComplex.homologyMap eY.hom m) := by rw [← hsq']
        _ = HomologicalComplex.homologyMap eX.hom m
              ≫ (HomologicalComplex.homologyMap (Limits.Sigma.map pm) m
                  ≫ inv (HomologicalComplex.homologyMap eY.hom m)) := Category.assoc _ _ _
    haveI hC : CategoryTheory.Epi (HomologicalComplex.homologyMap
        (Work.Serre.sigmaPairMap X Y A B g hg) m) := by
      rw [hC_eq]
      infer_instance
    exact (ModuleCat.epi_iff_surjective _).mp hC

end

end Work.Serre.SPC.One
