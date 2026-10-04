import Mathlib
import Submission.Work.Diff.STE.B3.TransportDefs
import Submission.Work.Diff.STE.B3.transport_Mf_second

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE.B3

/-- **The frame-change matrix identity on the chart target.**

`Mf = Ff · Gf · Ffᵀ` is the matrix form of the expansion of the section `h` in the
`g₀`-orthonormal frame `e j ·` against the coordinate frame of the chart at `D.x₀ j`: the
coordinate-frame chart matrix `Gf` conjugated by the change-of-frame matrix `Ff`.

This is the version whose hypothesis is membership of the flat coordinate in the chart *target*
(an open condition), rather than the `‖z‖ ≤ 2 D.σ j`-ball used by
`Work.Diff.STE.B3.Mf_matrix_eq`; the entrywise identity on the chart target is
`Work.Diff.STE.B3.Mf_eq_of_target`. -/
theorem Mf_matrix_eq_of_target
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M] [I.Boundaryless]
    {ι₀ : Type*} [Fintype ι₀] {g₀ : Submission.Diff.SMet I M}
    (D : Work.Diff.STE.B3Data (I := I) (M := M) ι₀ g₀)
    (h : Work.Diff.STE.Bil (I := I) (M := M)) (j : ι₀)
    (z : Fin (Module.finrank ℝ E) → ℝ)
    (htgt : Work.Diff.STE.flatToE (I := I) (M := M) (D.x₀ j) z
      ∈ (extChartAt I (D.x₀ j)).target) :
    Matrix.of (Work.Diff.STE.B3.Mf (I := I) (M := M) D h j z)
      = Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j z)
        * Matrix.of (Work.Diff.STE.B3.Gf (I := I) (M := M) D h j z)
        * (Matrix.of (Work.Diff.STE.B3.Ff (I := I) (M := M) D j z)).transpose := by
  ext a b
  rw [Matrix.mul_apply]
  simp only [Matrix.mul_apply, Matrix.transpose_apply, Finset.sum_mul, Matrix.of_apply]
  rw [Mf_eq_of_target (I := I) (M := M) D h j a b htgt]
  conv_rhs => rw [Finset.sum_comm]

end Work.Diff.STE.B3
