import Mathlib
import Submission.Work.Diff.EXT.bilinMat

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The chart-coordinate expression of a bilinear form on the tangent space

`ContinuousLinearMap.inCoordinates` rewrites a continuous linear map between fibers of two
vector bundles in the trivialisations at two base points.  For the *bilinear* forms on the tangent
bundle, `Submission.Work.Diff.EXT.matToBilin` reconstructs a bilinear form on the model space `E`
from its matrix.  The two are related by the coordinate frame `frameVector x₀ x ·` of the chart
at `x₀`: on the `(v, w)` pair the coordinate form of `φ` is
`φ (frameVector x₀ x v) (frameVector x₀ x w)`.

This is the tool that lets one pass from the matrix `chartMat` of a metric family (a `MatE`-valued
function) to the *bilinear-form valued* section of the hom bundle, and back.

The main input is Mathlib's `inCoordinates_apply_eq₂` (in
`Mathlib.Topology.VectorBundle.Hom`), which computes `inCoordinates` of a bilinear map in terms of
the coordinate maps of the two factor bundles and of the trivial line bundle `ℝ`.
-/

set_option linter.unusedSectionVars false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT

/-- The coordinate form of a bilinear form `φ` on the tangent space at `x`, in the trivialisation
at `x₀`, evaluated on `v w : E`, is `φ` evaluated on the coordinate frame at `x`. -/
lemma inCoordinates_tangent_apply
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    {x₀ x : M} (hx : x ∈ (chartAt H' x₀).source)
    (φ : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) (v w : E) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] ℝ) x₀ x x₀ x φ v w
      = φ (Submission.Geodesic.frameVector (I := I) x₀ x v)
          (Submission.Geodesic.frameVector (I := I) x₀ x w) := by
  have hx' : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet := by
    rw [TangentBundle.trivializationAt_baseSet]; exact hx
  have h3 : x ∈ (trivializationAt ℝ (fun _ : M => ℝ) x₀).baseSet := by simp
  rw [inCoordinates_apply_eq₂ hx' hx' h3]
  have hid : ∀ z : ℝ,
      (Trivialization.linearMapAt ℝ (trivializationAt ℝ (Trivial M ℝ) x₀) x) z = z := by
    intro z; simp
  rw [hid]
  simp only [Submission.Geodesic.frameVector]
  rw [Bundle.Trivialization.symmL_apply (e := trivializationAt E (TangentSpace I) x₀) hx' v,
      Bundle.Trivialization.symmL_apply (e := trivializationAt E (TangentSpace I) x₀) hx' w]

theorem inCoordinates_tangent_bilin
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    {x₀ x : M} (hx : x ∈ (chartAt H' x₀).source)
    (φ : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    ContinuousLinearMap.inCoordinates E (TangentSpace I) (E →L[ℝ] ℝ)
        (fun x : M => TangentSpace I x →L[ℝ] ℝ) x₀ x x₀ x φ
      = Work.Diff.EXT.matToBilin (fun i j =>
          φ (Submission.Geodesic.frameVector (I := I) x₀ x (Work.Diff.EXT.bB (E := E) i))
            (Submission.Geodesic.frameVector (I := I) x₀ x (Work.Diff.EXT.bB (E := E) j))) := by
  apply Work.Diff.EXT.eq_of_apply_basis_basis
  intro i j
  rw [Work.Diff.EXT.matToBilin_apply_basis]
  exact inCoordinates_tangent_apply hx φ _ _

end Work.Diff.EXT
