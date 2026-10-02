import Mathlib
import Submission.Work.ThomBordism.doubleDefs
import Submission.Work.ThomBordism.doubleCharted
import Submission.Work.ThomBordism.doubleChartedT2
import Submission.Work.Cohomology.localHomology
import Submission.Work.Cohomology.relChainsMapOf_comp
import Submission.Work.Orient.Boundary.localHomology_corner

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# The interior of `M` inside its double: the data

For a `C¹` manifold `M` with boundary modelled on `EuclideanHalfSpace (n+1)`, this file records the
*data* used to compare the local homology of `M` at an interior point `y` with the local homology of
the double `D = Double n M` at `doubleιM y`:

* `intSet n M` — the interior of `M` (the complement of the boundary);
* `intImg n M` — its image `doubleιM '' intSet` in the double (the range of `interiorEmb`);
* `eInt n M` — the homeomorphism `int M ≅ intImg` induced by the open embedding `interiorEmb`;
* `hInt n M` — the same map as a morphism of `TopCat`.

Only definitions; the properties live in `Submission/Work/ThomBordism/doubleFC/interiorDataProps.lean`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicTopology CategoryTheory.Limits
open scoped Manifold

namespace Work.ThomBordism.DoubleFC

noncomputable section

/-- **The interior of `M`**, as a subset (the complement of the boundary). -/
def intSet (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] : Set M :=
  ((modelWithCornersEuclideanHalfSpace (n + 1)).boundary M)ᶜ

/-- **The image of the interior of `M` in its double** (the range of `interiorEmb`). -/
def intImg (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] : Set (Double n M) :=
  Set.range (Work.ThomBordism.interiorEmb (n := n) (M := M))

/-- **The homeomorphism `int M ≅ ιM(int M)`** induced by the open embedding `interiorEmb`. -/
noncomputable def eInt (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] :
    ↥(intSet n M) ≃ₜ ↥(intImg n M) :=
  (Work.ThomBordism.isOpenEmbedding_interiorEmb (n := n) (M := M)).toIsEmbedding.toHomeomorph

/-- The underlying map of `eInt`, as a morphism of `TopCat`. -/
noncomputable def hInt (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] :
    TopCat.of (intSet n M) ⟶ TopCat.of (intImg n M) :=
  TopCat.ofHom (eInt n M).toHomotopyEquiv.toFun

/-- The inclusion of the first copy of `M`, as a morphism of `TopCat` (the `f` of
`Work.ThomBordism.DoubleFC.pairMapιM`). -/
noncomputable def fPair (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] :
    TopCat.of M ⟶ TopCat.of (Double n M) :=
  TopCat.ofHom ⟨doubleιM (n := n) (M := M), continuous_doubleιM (n := n) (M := M)⟩

/-- The restriction of `fPair` to the complements of `y` and of `doubleιM y` (the `g` of
`Work.ThomBordism.DoubleFC.pairMapιM`). -/
noncomputable def gPair (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (y : M) :
    TopCat.of ↥(({y} : Set M)ᶜ) ⟶
      TopCat.of ↥(({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ) :=
  TopCat.ofHom
    ⟨fun m => ⟨doubleιM (n := n) (M := M) m.1,
        by
          intro h
          exact m.2 (doubleιM_injective (n := n) (M := M) h)⟩,
      Continuous.subtype_mk
        ((continuous_doubleιM (n := n) (M := M)).comp continuous_subtype_val) _⟩

/-! ## The punctured versions -/

/-- The interior of `M` with the point `y` removed, as a subset of `intSet n M`. -/
def punctSet (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (y : M) : Set ↥(intSet n M) :=
  {x : ↥(intSet n M) | (x : M) ∈ ({y} : Set M)ᶜ}

/-- The image of the punctured interior in the double, as a subset of `intImg n M`. -/
def punctImg (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M] (y : M) : Set ↥(intImg n M) :=
  {v : ↥(intImg n M) | (v : Double n M) ∈
    ({doubleιM (n := n) (M := M) y} : Set (Double n M))ᶜ}

/-- The underlying point of `eInt u`. -/
theorem eInt_apply_coe (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (u : ↥(intSet n M)) :
    ((eInt n M u : ↥(intImg n M)) : Double n M) = doubleιM (n := n) (M := M) u.1 :=
  (Work.ThomBordism.isOpenEmbedding_interiorEmb (n := n) (M := M)).toIsEmbedding.toHomeomorph_apply_coe u

/-- **The punctured homeomorphism** `int M ∖ {y} ≅ ιM(int M) ∖ {ιM y}`. -/
noncomputable def eIntPunct (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    (y : M) (hy : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    ↥(punctSet n M y) ≃ₜ ↥(punctImg n M y) :=
  Work.Orient.Boundary.homeomorphRestrict (eInt n M) (punctSet n M y) (punctImg n M y) (by
    intro x
    constructor
    · intro hx hcontra
      have h1 : ((eInt n M x : ↥(intImg n M)) : Double n M) = doubleιM (n := n) (M := M) x.1 :=
        eInt_apply_coe n M x
      rw [Set.mem_singleton_iff] at hcontra
      exact hx (doubleιM_injective (n := n) (M := M) (by rw [← h1, hcontra]))
    · intro hx
      by_contra hcon
      have hxy : (x : M) = y := by
        simpa only [punctSet, Set.mem_setOf_eq, Set.mem_compl_iff, not_not,
          Set.mem_singleton_iff] using hcon
      have h1 : ((eInt n M x : ↥(intImg n M)) : Double n M) = doubleιM (n := n) (M := M) x.1 :=
        eInt_apply_coe n M x
      have h2 : ((eInt n M x : ↥(intImg n M)) : Double n M) =
          doubleιM (n := n) (M := M) y := by rw [h1, hxy]
      exact hx (by simpa using h2))

/-- The punctured version of `hInt`, as a morphism of `TopCat`. -/
noncomputable def hIntPunct (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    (y : M) (hy : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) :
    TopCat.of (punctSet n M y) ⟶ TopCat.of (punctImg n M y) :=
  TopCat.ofHom (eIntPunct n M y hy).toHomotopyEquiv.toFun

/-! ## Quasi-isomorphy of the two middle maps -/

/-- The chain map induced by `hInt` is a quasi-isomorphism (it comes from a homeomorphism). -/
theorem isIso_homologyMap_chainMap_hInt (n : ℕ) (M : Type) [TopologicalSpace M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M] (j : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (intSet n M)) (TopCat.of (intImg n M))
        (hInt n M)) j) :=
  Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
    (X := TopCat.of (intSet n M)) (Y := TopCat.of (intImg n M))
    (eInt n M).toHomotopyEquiv j

/-- The chain map induced by `hIntPunct` is a quasi-isomorphism. -/
theorem isIso_homologyMap_chainMap_hIntPunct (n : ℕ) (M : Type) [TopologicalSpace M] [T2Space M]
    [ChartedSpace (EuclideanHalfSpace (n + 1)) M]
    [IsManifold (modelWithCornersEuclideanHalfSpace (n + 1)) 1 M]
    (y : M) (hy : y ∉ (modelWithCornersEuclideanHalfSpace (n + 1)).boundary M) (j : ℕ) :
    CategoryTheory.IsIso (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (punctSet n M y)) (TopCat.of (punctImg n M y))
        (hIntPunct n M y hy)) j) :=
  Work.Cohomology.isIso_homologyMap_chainMap_of_homotopyEquiv
    (X := TopCat.of (punctSet n M y)) (Y := TopCat.of (punctImg n M y))
    (eIntPunct n M y hy).toHomotopyEquiv j

end

end Work.ThomBordism.DoubleFC
