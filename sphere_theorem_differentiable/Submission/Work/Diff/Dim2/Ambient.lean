import Mathlib
import Submission.Work.Diff.Dim2.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The ambient data for the immersion criterion of the `d = 2` branch

This file contains only *definitions* used by the delegated lemma
`Work.Diff.Dim2.sphere_immersion_criterion` (see `Plan3.lean` §9).

The map to the sphere in the `d = 2` construction is

    G x = (sin (ξ x) • Az x, cos (ξ x)) ∈ ℝ³

with `Az x ∈ S¹ ⊂ ℝ² = EuclideanSpace ℝ (Fin 2)` and `ξ x ∈ ℝ`.  This is the composite of the
pair map `x ↦ (ξ x, Az x) : M → ℝ × ℝ²` with the *ambient* map

    sphereAmb (r, z) := (sin r * z 0, sin r * z 1, cos r) ∈ EuclideanSpace ℝ (Fin 3),

whose target is the unit sphere of `ℝ³`.

For the *immersion* check one wants the two `1`-forms

* `dξ := mfderiv I 𝓘(ℝ,ℝ) ξ x : TₓM → ℝ`, and
* `angForm Az x := w ↦ ⟪rot90 (Az x), mfderiv I _ Az x w⟫ : TₓM → ℝ`

(the *angular form* of the azimuth).  The criterion is: if `sin (ξ x) ≠ 0` and the two forms have
*trivially intersecting* kernels, then `mfderiv G x` is injective; since the source and target have
the same dimension, it is then invertible and `G` is a local diffeomorphism at `x` (inverse function
theorem, `Commons.Geometry.Manifold.LocalDiffeomorph.isLocalDiffeomorphAt_infty_of_contMDiffOn_of_mfderiv_isInvertible`).
-/

namespace Work.Diff.Dim2

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set Filter

noncomputable section

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The `i`-th component of the ambient map `(r, z) ↦ (sin r * z 0, sin r * z 1, cos r)`. -/
noncomputable def sphereAmbComp (i : Fin 3) (p : ℝ × EuclideanSpace ℝ (Fin 2)) : ℝ :=
  Fin.cases (Real.sin p.1 * (p.2 0))
    (fun j => Fin.cases (Real.sin p.1 * (p.2 1)) (fun _ => Real.cos p.1) j) i

/-- **The ambient map of the sphere parametrisation**: `(r, z) ↦ (sin r • z, cos r)` as a map
`ℝ × ℝ² → ℝ³`. -/
noncomputable def sphereAmb (p : ℝ × EuclideanSpace ℝ (Fin 2)) : EuclideanSpace ℝ (Fin 3) :=
  (EuclideanSpace.equiv (Fin 3) ℝ).symm (fun i => sphereAmbComp i p)

/-- **The angular form of an azimuth field** `Az : M → ℝ²`: the `1`-form
`w ↦ ⟪rot90 (Az x), mfderiv Az x w⟫` on the tangent space at `x`. -/
noncomputable def angForm {Az : M → EuclideanSpace ℝ (Fin 2)} (x : M) :
    TangentSpace I x →L[ℝ] ℝ :=
  (innerSL ℝ (rot90 (Az x))).comp
    (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin 2)) Az x)

end

end Work.Diff.Dim2
