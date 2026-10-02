import Mathlib
import Submission.Work.ThomBordism.Interface
import Submission.Work.ThomBordism.existsBoundaryBordism
import Submission.Work.ThomBordism.sigmaBoundarySum
import Submission.Work.Bordism.Middle
import Submission.Work.Bordism.Invariance

-- Lean v4.35.0-rc3: restore v4.34 instance-unification transparency (port).
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
set_option synthInstance.maxHeartbeats 400000

/-!
# `BoundarySigma` from the boundary duality input

`Work.ThomBordism.BoundarySigma` (`Interface.lean`) is the statement that `∑ i, (F i).sigma = 0`
for the pieces of the boundary of a `W : NullBordismFamily ι F`.  This file isolates **exactly what
is still missing** from its proof, as a single named `Prop`:

`Work.ThomBordism.BoundaryDuality` consists of, for every `W : NullBordismFamily ι F`,

* the middle cohomology `H⁴(∂W;ℚ)` is finite dimensional (this follows from the finite
  dimensionalities of the pieces, transported along `W.bdry`, and the coproduct splitting
  `Work.ThomBordism.pullbackRat_sigma_bijective`);
* the middle intersection form of `∂W` is non-degenerate (this follows from the *closed* Poincaré
  duality of `∂W` — `Work.ThomBordism.goodUniv_of_localGen` together with the local generation of
  `∂w` at the points of `∂W`, which is inherited from `Man8.c_fund` of the pieces);
* **`Work.Bordism.HalfDimension 4` for the bordism `(∂W, ∂w) ⟶ (∅, 0)`** — this is the genuine
  geometric input: middle-degree Lefschetz duality for the pair `(W, ∂W)`, i.e. that the image of
  `H⁴(W;ℚ) → H⁴(∂W;ℚ)` is a Lagrangian of the middle form of `∂W` (the isotropy half is
  `Work.Bordism.boundaryBil_middleMap_eq_zero`, already proved; the missing half is the dimension
  count `dim im r = dim H⁴(∂W;ℚ)/2`, equivalently the isotropy of
  `im(∂: H₅(W,∂W;ℚ) → H₄(∂W;ℚ))`, for which the workspace has no proof — the classical proof uses
  the double `W ∪_M W̄` and the Mayer–Vietoris transgression identity `⟨x, i_*z⟩_D = ⟨∂_D x, z⟩_M`,
  neither of which is formalised yet).

Given `BoundaryDuality`, the proof of `BoundarySigma` is the two halves:

* `σ(∂W, ∂w) = 0`: it is the signature of a boundary, so by
  `Work.Bordism.sigma_eq_of_bordant_eight` (bordism invariance of the signature, which consumes
  exactly the three inputs above) it equals `σ(∅, 0) = 0`;
* `σ(∂W, ∂w) = ∑ i, (F i).sigma`: `Work.ThomBordism.sigmaBoundarySum`.
-/

set_option autoImplicit false
set_option maxHeartbeats 1600000

open CategoryTheory AlgebraicTopology

namespace Work.ThomBordism

noncomputable section

/-- The closed oriented `8`-manifold `(∂W, ∂w)` of a `NullBordismFamily`. -/
abbrev bdryClosed {ι : Type} [Fintype ι] {F : ι → Man8} (W : NullBordismFamily ι F) :
    Work.Bordism.ClosedOriented 8 :=
  ⟨TopCat.of (bdrySet W.W), Work.Cohomology.hPairδ (TopCat.of W.W) (bdrySet W.W) 8 W.w⟩

/-- The empty closed oriented `8`-manifold, as the second end of the bordism. -/
abbrev emptyClosed : Work.Bordism.ClosedOriented 8 :=
  ⟨TopCat.of PEmpty, 0⟩

/-- The bordism `(∂W, ∂w) ⟶ (∅, 0)` supplied by a `NullBordismFamily`
(`Work.ThomBordism.existsBoundaryBordism`, made definite by a choice). -/
noncomputable def boundaryBordism {ι : Type} [Fintype ι] {F : ι → Man8}
    (W : NullBordismFamily ι F) : Work.Bordism.Bordism (bdryClosed W) emptyClosed :=
  Classical.choice (existsBoundaryBordism W)

/-- **The duality input of `BoundarySigma`**, for every boundary `∂W`: finiteness and
non-degeneracy of the middle form of `∂W`, and `HalfDimension 4` for the bordism
`(∂W, ∂w) ⟶ (∅, 0)` (middle-degree Lefschetz duality for the pair `(W, ∂W)`). -/
structure BoundaryDuality : Prop where
  /-- `H⁴(∂W;ℚ)` is finite dimensional -/
  finite : ∀ (ι : Type) [Fintype ι] (F : ι → Man8) (W : NullBordismFamily ι F),
    FiniteDimensional ℚ
      (Work.SignatureBordism.ratCohomology 4 (TopCat.toSSet.obj (TopCat.of (bdrySet W.W))))
  /-- the middle intersection form of `∂W` is non-degenerate -/
  nondegenerate : ∀ (ι : Type) [Fintype ι] (F : ι → Man8) (W : NullBordismFamily ι F),
    Work.Bordism.Nondegenerate (Work.Bordism.midForm (k := 4) (bdryClosed W))
  /-- **the crux**: `HalfDimension` for the bordism `(∂W, ∂w) ⟶ (∅, 0)` -/
  halfDimension : ∀ (ι : Type) [Fintype ι] (F : ι → Man8) (W : NullBordismFamily ι F),
    Work.Bordism.HalfDimension 4 (boundaryBordism W)
  /-- the middle cohomology of the empty manifold vanishes (a *formal* side condition: the singular
  (co)chain complex of the empty space is zero) -/
  finite_empty : FiniteDimensional ℚ (Work.SignatureBordism.ratCohomology 4
    (TopCat.toSSet.obj (TopCat.of PEmpty)))
  /-- the middle form of the empty manifold is non-degenerate (the same formal side condition: the
  form lives on the zero space) -/
  nondegenerate_empty : Work.Bordism.Nondegenerate (Work.Bordism.midForm (k := 4) emptyClosed)

/-- **`BoundarySigma` from the boundary duality input.** -/
theorem boundarySigma_of_duality (h : BoundaryDuality) : BoundarySigma := by
  intro ι _ F W
  rw [← sigmaBoundarySum W]
  haveI := h.finite ι F W
  haveI := h.finite_empty
  have heq := Work.Bordism.sigma_eq_of_bordant_eight (boundaryBordism W)
    (h.nondegenerate ι F W) h.nondegenerate_empty (h.halfDimension ι F W)
  rw [heq]
  simp

end

end Work.ThomBordism
