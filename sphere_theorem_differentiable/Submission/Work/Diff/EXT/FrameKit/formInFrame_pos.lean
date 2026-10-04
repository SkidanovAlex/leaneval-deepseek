import Mathlib
import Submission.Work.Diff.EXT.glueDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.FrameKit

/-- **Positivity of `formInFrame`.**  If the matrix `A` is positive definite (in the sense of the
quadratic form `v ↦ ∑ᵢ ∑ⱼ vᵢ vⱼ Aᵢⱼ` on the coefficient space) and `x` lies in the base set of the
tangent-bundle trivialisation at `x₀`, then the bilinear form `formInFrame x₀ x A` is positive on
every non-zero tangent vector `u` at `x`.

The proof transports `u` into the model space by the trivialisation `frameCoords x₀ x`
(`frameVector x₀ x` is its inverse on the base set), and reads off the quadratic form through
`formInFrame_apply`. -/
theorem formInFrame_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    {x₀ x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    {A : Work.Diff.EXT.MatE (E := E)}
    (h : ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * v j * A i j)
    {u : TangentSpace I x} (hu : u ≠ 0) :
    0 < Work.Diff.EXT.formInFrame (I := I) x₀ x A u u := by
  -- The coordinates of `u` in the frame of the chart at `x₀`.
  let c : Fin (Module.finrank ℝ E) → ℝ :=
    fun i => ((bB (E := E)).coord i) (frameCoords (I := I) x₀ x u)
  -- `frameVector` is the inverse of `frameCoords` at points of the base set.
  have hvu : u = Submission.Geodesic.frameVector (I := I) x₀ x (frameCoords (I := I) x₀ x u) :=
    (Bundle.Trivialization.symmL_continuousLinearMapAt
      (e := trivializationAt E (TangentSpace I) x₀) (R := ℝ) hx u).symm
  -- Non-zero vectors have non-zero coordinates.
  have hc : c ≠ 0 := by
    intro h0
    apply hu
    have hz : frameCoords (I := I) x₀ x u = 0 := by
      have h1 := (bB (E := E)).sum_repr (frameCoords (I := I) x₀ x u)
      have hrepr : ∀ i, (bB (E := E)).repr (frameCoords (I := I) x₀ x u) i = 0 := by
        intro i
        rw [← Module.Basis.coord_apply]
        exact congrFun h0 i
      have hsum0 : (∑ i, (bB (E := E)).repr (frameCoords (I := I) x₀ x u) i •
          bB (E := E) i) = 0 :=
        Finset.sum_eq_zero fun i _ => by rw [hrepr i, zero_smul]
      calc frameCoords (I := I) x₀ x u
          = ∑ i, (bB (E := E)).repr (frameCoords (I := I) x₀ x u) i • bB (E := E) i := h1.symm
        _ = 0 := hsum0
    rw [hvu, hz]
    rw [Submission.Geodesic.frameVector]
    simp
  have hkey : 0 < ∑ i, ∑ j, c i * c j * A i j := h c hc
  rw [formInFrame_apply]
  convert hkey using 1
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  show A i j * c i * c j = c i * c j * A i j
  ring

end Work.Diff.EXT.FrameKit
