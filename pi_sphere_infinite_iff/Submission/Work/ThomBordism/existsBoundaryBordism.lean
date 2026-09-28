import Mathlib
import Submission.Work.ThomBordism.Interface

/-!
# The bordism of a boundary: `(∂W, ∂w)` is bordant to the empty manifold

`Work.ThomBordism.BoundarySigma` asks that `∑ i, (F i).sigma = 0` for the pieces `F : ι → Man8`
of the boundary of a `W : NullBordismFamily ι F`.  The *route* taken here is the classical one:

* `(∂W, ∂w)` is an oriented closed `8`-manifold that **is a boundary** —
  `Work.Bordism.Bordism ⟨∂W, ∂w⟩ ⟨∅, 0⟩` (this file);
* the signature is a bordism invariant (`Work.Bordism.sigma_eq_of_bordant`), so `σ(∂W) = σ(∅) = 0`
  — the missing input of that step is `Work.Bordism.HalfDimension` for this bordism, i.e.
  middle-degree Lefschetz duality of the pair `(W, ∂W)`;
* `σ(∂W) = ∑ i, (F i).sigma` by additivity over the disjoint union and the homeomorphism
  `W.bdry` (`Work.ThomBordism.sigmaBoundarySum`).

Here we record the *first* step.  Note that `Work.Bordism.Bordism` is the honest, if minimal,
model of a bordism: a space `V` with two parametrisations of the two boundary pieces and the
resulting relation between the fundamental classes (`V.iM_* [M] = V.iN_* [N]`); both the isotropy
of the middle map (`Work.Bordism.boundaryForm_middleMap_eq_zero`) and bordism invariance of the
signature (`Work.Bordism.sigma_eq_of_bordant`, given `HalfDimension`) consume exactly this data.
The relation here is the exactness of the pair sequence, `Work.Cohomology.hPairδ_comp`
(`i_* ∘ ∂ = 0`), applied to `W.w`.
-/

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false

open CategoryTheory

namespace Work.ThomBordism

noncomputable section

/-- The boundary set of a `NullBordismFamily`. -/
abbrev bdrySet (W : Type*) [TopologicalSpace W] [ChartedSpace (EuclideanHalfSpace 9) W] : Set W :=
  (modelWithCornersEuclideanHalfSpace 9).boundary W

/-- **`(∂W, ∂w)` is bordant to the empty manifold.**  The bordism space is `W` itself, the
parametrisation of the first end is the inclusion of the boundary, the second end is empty, and the
class relation is `i_* ∘ ∂ = 0` (`Work.Cohomology.hPairδ_comp`) together with `map_zero`. -/
theorem existsBoundaryBordism {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F) :
    Nonempty (Work.Bordism.Bordism
      ⟨TopCat.of (bdrySet W.W),
        Work.Cohomology.hPairδ (TopCat.of W.W) (bdrySet W.W) 8 W.w⟩
      ⟨TopCat.of PEmpty, 0⟩) := by
  refine ⟨⟨TopCat.of W.W,
    Work.Cohomology.subtypeIncl (TopCat.of W.W) (bdrySet W.W),
    TopCat.ofHom ⟨fun e => PEmpty.elim e,
      continuous_iff_continuousAt.mpr (fun x => PEmpty.elim x)⟩, ?_⟩⟩
  -- the class relation: `i_* (∂w) = 0 = (iN)_* 0`
  rw [map_zero]
  have hz : (Work.Cohomology.hPairδ (TopCat.of W.W) (bdrySet W.W) 8 ≫
        HomologicalComplex.homologyMap
          (Work.Cohomology.inclChains (TopCat.of W.W) (bdrySet W.W)) 8) W.w = 0 := by
    rw [Work.Cohomology.hPairδ_comp]
    simp
  have h3 : (HomologicalComplex.homologyMap
        (Work.Cohomology.inclChains (TopCat.of W.W) (bdrySet W.W)) 8)
        ((Work.Cohomology.hPairδ (TopCat.of W.W) (bdrySet W.W) 8) W.w) = 0 := by
    simpa using hz
  show (HomologicalComplex.homologyMap
      (Work.Cohomology.chainMap ℤ (TopCat.of (bdrySet W.W)) (TopCat.of W.W)
        (Work.Cohomology.subtypeIncl (TopCat.of W.W) (bdrySet W.W))) 8).hom
      ((Work.Cohomology.hPairδ (TopCat.of W.W) (bdrySet W.W) 8).hom W.w) = 0
  simpa only [Work.Cohomology.inclChains] using h3

end

end Work.ThomBordism
