import Mathlib
import ChallengeDeps
import Submission.Blueprint.Interfaces
import Submission.Work.HOMOL.Basic
import Submission.Work.HOMOL.Discrete
import Submission.Work.HOMOL.Extend

/-!
# AREA HOMOL — homology inputs for hole 11

The goal of this file is

`Work.HOMOL.homology_prop : Submission.Blueprint.HomologyProp`

which is the pair of computations needed to pass from the natural isomorphism of derived
complexes (hole 10) to the homology computation of hole 11 (`REFS/05 §4`):

1. `H^{−n}(Q C(X)) ≅ discrete(H_n^{sing}(X))`, where `C(X)` is the discrete singular chain
   complex of `X` placed in cohomological degrees `≤ 0`; and
2. the derived inclusion commutes with homology,
   `ι (H^k_{Solid} K) ≅ H^k_{LCA}(ι_D K)`.

For (1) we use `DerivedCategory.homologyFunctorFactors` (homology on the derived category is the
homology of any representative complex), `extendFunctorHomologyIso` (extension by zero along
`ComplexShape.embeddingDownNat : down ℕ ⥤ up ℤ` preserves homology, shifting `n` to `−n`) and
`discreteHomologyIso` (the discrete functor is exact, `Submission/Work/HOMOL/Discrete.lean`).

For (2) we use `mapDerivedCategoryHomologyIso` with `F := isSolid.ι`, which is exact by
`ChallengeDeps`.

Nothing here is specific to CW complexes: the results hold for every topological space `X`.
-/

noncomputable section

open CategoryTheory Limits LightProfinite LightCondensed

open _root_.LightCondensed _root_.LightCondensed.Solid

namespace Work.HOMOL

/-- The discrete singular chain complex of `X`, as a chain complex in homological
degrees `ℕ` (the object appearing inside `singularChainsLightCondAbComplexFunctor` before
extension by zero to cohomological degrees `≤ 0`). -/
abbrev discreteSingularChainComplex (X : TopCat.{0}) :
    ChainComplex LightCondAb ℕ :=
  ((LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex (ComplexShape.down ℕ)).obj
    (Submission.Blueprint.singC.obj X)

/-- **`Q`, extension by zero and `discrete` commute with homology.**
For *any* chain complex `K` of abelian groups, the `−n`-th cohomology of the extended degreewise
discretisation of `K` is the discrete `n`-th homology of `K`. No input from topology is used. -/
noncomputable def discreteExtendedHomologyIso (K : ChainComplex (ModuleCat ℤ) ℕ) (n : ℕ) :
    (DerivedCategory.homologyFunctor LightCondAb (-(n : ℤ))).obj
      (DerivedCategory.Q.obj
        ((ComplexShape.embeddingDownNat.extendFunctor LightCondAb).obj
          (((LightCondensed.discrete (ModuleCat ℤ)).mapHomologicalComplex
            (ComplexShape.down ℕ)).obj K))) ≅
      (LightCondensed.discrete (ModuleCat ℤ)).obj (K.homology n) :=
  (DerivedCategory.homologyFunctorFactors LightCondAb (-(n : ℤ))).app _ ≪≫
    extendHomologyIso _ n ≪≫
    discreteHomologyIso (ComplexShape.down ℕ) K n

/-- **`H^{−n}` of the discrete singular chains is discrete singular homology.**
The `n`-th homology of `discreteSingularChainComplex X` is `discrete (H_n^{sing}(X))`, and the
extension-by-zero to cohomological degrees shifts the index `n` to `−n`. -/
noncomputable def discreteSingularChainComplexHomologyIso (X : TopCat.{0}) (n : ℕ) :
    (singularChainsLightCondAbComplexFunctor.obj X).homology (-(n : ℤ)) ≅
      singularHomologyLightCondAb X n :=
  extendHomologyIso (discreteSingularChainComplex X) n ≪≫
    discreteHomologyIso (ComplexShape.down ℕ) (Submission.Blueprint.singC.obj X) n

/-- **Part 1 of `HomologyProp`**: the `−n`-th cohomology of the derived discrete singular chain
complex of `X` is the discrete `n`-th singular homology of `X`. -/
theorem singularChainsDerivedHomologyIso (X : TopCat.{0}) (n : ℕ) :
    Nonempty ((DerivedCategory.homologyFunctor LightCondAb (-(n : ℤ))).obj
      (singularChainsLightCondAbDerivedFunctor.obj X) ≅ singularHomologyLightCondAb X n) :=
  ⟨discreteExtendedHomologyIso (Submission.Blueprint.singC.obj X) n⟩

/-- **Part 2 of `HomologyProp`**: the derived inclusion of solid objects commutes with homology.
This is `mapDerivedCategoryHomologyIso` for the (exact) inclusion `isSolid.ι`; here `ι` denotes
`isSolid.ι` and `derivedInclusion = isSolid.ι.mapDerivedCategory`. -/
noncomputable def derivedInclusionHomologyIso (K : DSolid) (k : ℤ) :
    isSolid.ι.obj ((DerivedCategory.homologyFunctor Solid k).obj K) ≅
      (DerivedCategory.homologyFunctor LightCondAb k).obj (derivedInclusion.obj K) :=
  (mapDerivedCategoryHomologyIso (isSolid.ι) k).symm.app K

/-- Functorial form of `derivedInclusionHomologyIso`: the derived inclusion commutes with homology
as an isomorphism of functors on the derived category of solid objects. -/
noncomputable def derivedInclusionHomologyNatIso (k : ℤ) :
    derivedInclusion ⋙ DerivedCategory.homologyFunctor LightCondAb k ≅
      DerivedCategory.homologyFunctor Solid k ⋙ isSolid.ι :=
  mapDerivedCategoryHomologyIso (isSolid.ι) k

/-- The degreewise inclusion `ιC = isSolid.ι.mapHomologicalComplex (up ℤ)` of complexes commutes
with homology. This is the complex-level form of `derivedInclusionHomologyNatIso`. -/
noncomputable def iotaComplexHomologyIso (K : CochainComplex Solid ℤ) (k : ℤ) :
    ((Submission.Blueprint.ιC).obj K).homology k ≅ isSolid.ι.obj (K.homology k) :=
  mapHomologicalComplexHomologyIso_app (ComplexShape.up ℤ) isSolid.ι k K

/-- Complex-level form of `derivedInclusionHomologyIso`: for a complex `K` of solid objects, the
`k`-th homology of `Q (ιC K)` in `D(LightCondAb)` is `ι` of the `k`-th homology of `K`. -/
noncomputable def iotaComplexDerivedHomologyIso (K : CochainComplex Solid ℤ) (k : ℤ) :
    isSolid.ι.obj (K.homology k) ≅
      (DerivedCategory.homologyFunctor LightCondAb k).obj
        (DerivedCategory.Q.obj ((Submission.Blueprint.ιC).obj K)) :=
  (iotaComplexHomologyIso K k).symm ≪≫
    ((DerivedCategory.homologyFunctorFactors LightCondAb k).app
      ((Submission.Blueprint.ιC).obj K)).symm

/-- **AREA HOMOL.** The homology inputs for hole 11: homology of discrete singular chains, and
commutation of the derived inclusion with homology. -/
theorem homology_prop : Submission.Blueprint.HomologyProp :=
  ⟨fun X n => singularChainsDerivedHomologyIso X n,
    fun K k => ⟨derivedInclusionHomologyIso K k⟩⟩

end Work.HOMOL
