import Mathlib
import Submission.Work.DSEQ0.Coaug

universe u

namespace Work.DSEQ0

open AlgebraicGeometry CategoryTheory

/-- A scheme proper over an affine base admits a finite cover by affine open subschemes. -/
theorem exists_finite_affineCover {A : Type u} [CommRing A] {X : AlgebraicGeometry.Scheme.{u}}
    (f : X ⟶ AlgebraicGeometry.Spec (.of A)) [AlgebraicGeometry.IsProper f] :
    ∃ (J : Type u) (_ : Finite J) (U : J → X.Opens),
      (∀ i, AlgebraicGeometry.IsAffineOpen (U i)) ∧ ⨆ i, U i = ⊤ := by
  classical
  -- `IsProper f` gives `UniversallyClosed f`, hence `QuasiCompact f`, hence `X` is quasi-compact
  -- because the affine base `Spec A` is quasi-compact.
  haveI : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  -- Take the affine cover of `X` and pass to a finite subcover.
  let 𝒰 : X.OpenCover := X.affineCover.finiteSubcover
  refine ⟨𝒰.I₀, inferInstance, fun i => (𝒰.f i).opensRange,
    fun i => isAffineOpen_opensRange (𝒰.f i), ?_⟩
  exact Scheme.OpenCover.iSup_opensRange 𝒰

end Work.DSEQ0
