import Mathlib
import Submission.Work.Diff.EXT.glueDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT

theorem formInFrame_pos
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    {x₀ x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    {A : Work.Diff.EXT.MatE (E := E)}
    (h : ∀ v : Fin (Module.finrank ℝ E) → ℝ, v ≠ 0 → 0 < ∑ i, ∑ j, v i * v j * A i j)
    {u : TangentSpace I x} (hu : u ≠ 0) :
    0 < Work.Diff.EXT.formInFrame (I := I) x₀ x A u u := by
  -- The coordinates of `u` in the frame of the chart at `x₀` are nonzero, because the frame map
  -- inverts the trivialisation at `x₀`.
  have hfiv : Submission.Geodesic.frameVector (I := I) x₀ x
      ((Work.Diff.EXT.frameCoords (I := I) x₀ x) u) = u := by
    rw [Work.Diff.EXT.frameCoords, Submission.Geodesic.frameVector]
    exact Bundle.Trivialization.symmL_continuousLinearMapAt (R := ℝ)
      (e := trivializationAt E (TangentSpace I) x₀) hx u
  have hne : (Work.Diff.EXT.frameCoords (I := I) x₀ x) u ≠ 0 := by
    intro h0
    refine hu ?_
    rw [← hfiv, h0]
    simp [Submission.Geodesic.frameVector]
  -- The coefficients of `frameCoords x₀ x u` in the basis `bB` are not all zero.
  have hvne : (fun i => (Work.Diff.EXT.bB (E := E)).coord i
      ((Work.Diff.EXT.frameCoords (I := I) x₀ x) u)) ≠ 0 := by
    intro h0
    apply hne
    have hcoord : ∀ i, (Work.Diff.EXT.bB (E := E)).repr
        ((Work.Diff.EXT.frameCoords (I := I) x₀ x) u) i = 0 := by
      intro i
      rw [← Module.Basis.coord_apply]
      exact congrFun h0 i
    rw [← Module.Basis.sum_repr (Work.Diff.EXT.bB (E := E))
      ((Work.Diff.EXT.frameCoords (I := I) x₀ x) u)]
    simp [hcoord]
  have hpos := h (fun i => (Work.Diff.EXT.bB (E := E)).coord i
      ((Work.Diff.EXT.frameCoords (I := I) x₀ x) u)) hvne
  -- `formInFrame` reads off the coordinate quadratic form, which is exactly the sum of `h`.
  rw [Work.Diff.EXT.formInFrame_apply]
  have heq : (∑ i, ∑ j, (Work.Diff.EXT.bB (E := E)).coord i
          ((Work.Diff.EXT.frameCoords (I := I) x₀ x) u)
        * (Work.Diff.EXT.bB (E := E)).coord j ((Work.Diff.EXT.frameCoords (I := I) x₀ x) u)
        * A i j)
      = ∑ i, ∑ j, A i j * (Work.Diff.EXT.bB (E := E)).coord i
          ((Work.Diff.EXT.frameCoords (I := I) x₀ x) u)
        * (Work.Diff.EXT.bB (E := E)).coord j ((Work.Diff.EXT.frameCoords (I := I) x₀ x) u) := by
    apply Finset.sum_congr rfl; intro i _
    apply Finset.sum_congr rfl; intro j _
    ring
  rw [← heq]
  exact hpos

end Work.Diff.EXT
