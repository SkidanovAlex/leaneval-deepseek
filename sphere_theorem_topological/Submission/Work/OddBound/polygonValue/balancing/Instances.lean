import Mathlib

/-!
# Instance aliases for the tangent spaces of a Riemannian manifold

Statements about the tangent bundle of a Riemannian manifold mention the typeclass arguments
`(x : M) → NormedAddCommGroup (TangentSpace I x)` and `(x : M) → InnerProductSpace ℝ (TangentSpace I x)`
of `IsContMDiffRiemannianBundle`.  In Mathlib these are synthesised from `Bundle.RiemannianBundle`
only when the `Bundle` scoped instances are open; the two global instances below make them available
unconditionally, so that statements phrased without `open Bundle` (in particular the statements of
delegated lemmas, which are elaborated in a bare `Mathlib` context) still elaborate.
-/

open scoped Manifold ContDiff Bundle Topology ENNReal
open Bundle

/-- The Riemannian `NormedAddCommGroup` structure on the tangent spaces, as a global instance. -/
noncomputable instance (priority := 50) instTangentNormedAddCommGroup
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (WithTop.some (⊤ : ENat)) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)] (x : M) :
    NormedAddCommGroup (TangentSpace I x) :=
  inferInstance

/-- The Riemannian `InnerProductSpace` structure on the tangent spaces, as a global instance. -/
noncomputable instance (priority := 50) instTangentInnerProductSpace
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} {M : Type*}
    [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I (WithTop.some (⊤ : ENat)) M]
    [Bundle.RiemannianBundle (fun x : M ↦ TangentSpace I x)] (x : M) :
    InnerProductSpace ℝ (TangentSpace I x) :=
  inferInstance
