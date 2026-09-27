import Mathlib
import Submission.Work.Drive.Interfaces

/-!
# The boundary triple intersections of three chains in a `4`-manifold

`Work.Drive.transverse_inter_boundary_parity` (`Submission/Work/Drive/transverse_inter_boundary_parity.lean`)
proves the mod-2 form of the Leibniz rule `∂(D ⋔ N) = ∂D ⋔ N + D ⋔ ∂N` for a `2`-chain `D` and a
`3`-chain `N` in a smooth `4`-manifold: the set of *boundary* intersections of the two chains is
finite with even cardinality.  The vector-space chapter
(`Submission/Work/Drive/intersection_triple.lean`) proves the corresponding statement for **three**
`3`-chains (`even_ncard_blockMeet_sum`), which is what Hugelmeyer's Lemmas 3 and 4 use at the chain
level (`Submission/Work/Drive/RADIAL_CHAIN_NOTES.md`); the manifold form of that statement is not in
the workspace yet.

This file only fixes the *vocabulary*: the three sets of boundary triple intersections, grouped by
which of the three boxes a coordinate lies on the boundary of, exactly as `blockMeet` does in the
vector-space chapter.  Each chain is presented parametrically, as a map
`D k : ℝ³ → M` from the unit cube, so that the three copies of `ℝ³` are the three blocks of the
nine-box.
-/

namespace Work.Drive

open Manifold
open scoped Manifold ContDiff

/-- **The `k`-th boundary triple intersection.**  The set of triples `(x₀, x₁, x₂)` of points of the
three unit cubes at which the three chains meet in a single point of the ambient manifold, and whose
`k`-th coordinate is on the boundary of its cube (so that the corresponding chain has hit its own
boundary there: the `k`-th summand `n_{P_k}` of Hugelmeyer's parity identities). -/
def tripleBdryMeet (M : Type*) [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) (k : Fin 3) :
    Set (Fin 3 → EuclideanSpace ℝ (Fin 3)) :=
  {x | (∀ k' : Fin 3, x k' ∈ Submission.Drive.unitBox 2) ∧
    D 0 (x 0) = D 1 (x 1) ∧ D 0 (x 0) = D 2 (x 2) ∧
    x k ∈ Submission.Drive.unitBoxBdry 2}

/-- The set of triples at which the three chains meet, with no boundary condition. -/
def tripleMeet (M : Type*) [TopologicalSpace M]
    (D : Fin 3 → EuclideanSpace ℝ (Fin 3) → M) :
    Set (Fin 3 → EuclideanSpace ℝ (Fin 3)) :=
  {x | (∀ k' : Fin 3, x k' ∈ Submission.Drive.unitBox 2) ∧
    D 0 (x 0) = D 1 (x 1) ∧ D 0 (x 0) = D 2 (x 2)}


/-! ## The transversality conditions, in a form that is independent of charts -/

/-- **Transversality of three `3`-chains in a `4`-manifold.**  At a triple point the derivative of the
difference map `(x₀,x₁,x₂) ↦ (D₀x₀ − D₁x₁, D₀x₀ − D₂x₂)` is the linear map
`(v₀,v₁,v₂) ↦ (d₀v₀ − d₁v₁, d₀v₀ − d₂v₂)`; the triple intersection is a `1`-manifold exactly when
this map is surjective onto the tangent space squared.  (This is *not* equivalent to the three tangent
images spanning the tangent space: they must be transverse, i.e. the three tangent spaces must meet in
the expected dimension.)  The condition is chart-independent, so it is stated here for the three
derivatives alone. -/
def TripleTransverse (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4)) : Prop :=
  ∀ w₁ w₂ : EuclideanSpace ℝ (Fin 4), ∃ v : Fin 3 → EuclideanSpace ℝ (Fin 3),
    f₀ (v 0) - f₁ (v 1) = w₁ ∧ f₀ (v 0) - f₂ (v 2) = w₂

/-- **A common tangent direction of three `3`-chains at a triple point**: a triple `(v₀,v₁,v₂)` whose
three images under the three derivatives coincide.  These are the tangent vectors of the triple
intersection `1`-manifold, and they are what the face condition of the parity theorem uses to see that
the intersection crosses a face of the parameter box transversally. -/
def TripleCommonDir (f₀ f₁ f₂ : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 4))
    (v : Fin 3 → EuclideanSpace ℝ (Fin 3)) : Prop :=
  f₀ (v 0) = f₁ (v 1) ∧ f₀ (v 0) = f₂ (v 2)

end Work.Drive
