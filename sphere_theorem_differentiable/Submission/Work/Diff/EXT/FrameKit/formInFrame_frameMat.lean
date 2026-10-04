import Mathlib
import Submission.Work.Diff.EXT.glueDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `formInFrame` and `frameMat` are mutually inverse

For a chart centre `x₀`, the *frame* of the chart at `x₀` identifies the model space `E` with the
tangent space `TangentSpace I x` at a point `x` of the chart:

* `frameCoords x₀ x : TangentSpace I x →L[ℝ] E` — the coordinates of a tangent vector,
* `frameVector x₀ x : E → TangentSpace I x` — the tangent vector with prescribed coordinates,
* `formInFrame x₀ x A` — the bilinear form whose matrix in that frame is `A`,
* `frameMat x₀ x φ` — the matrix of the bilinear form `φ` in that frame.

Here we prove that these two operations are mutually inverse: for every continuous bilinear form
`φ` on `TangentSpace I x` and every `x` in the base set of the chart at `x₀`,

`formInFrame x₀ x (frameMat x₀ x φ) = φ`.

The proof does not need the *linear independence* of the frame, only that it *spans*: on the
base set `frameVector x₀ x (frameCoords x₀ x u) = u` (`Trivialization.symmL_continuousLinearMapAt`),
so every `u` expands in the frame as `u = ∑ i, coord i (frameCoords u) • frameVector x₀ x (bB i)`
(`hdecomp` below).  Evaluating `formInFrame x₀ x A` on a pair of such expansions gives the double
sum `∑ i, ∑ j, A i j * c i * d j`, and substituting `A = frameMat x₀ x φ` turns this into the
expansion of `φ` on the same two sums (`formInFrame_bilin_expand`).
-/

open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.FrameKit

/-- **Expansion of a continuous bilinear form on a pair of finite sums.**
`φ (∑ i, c i • a i) (∑ j, d j • b j) = ∑ i, ∑ j, φ (a i) (b j) * c i * d j`. -/
lemma formInFrame_bilin_expand
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    {x : M} {ι : Type*} [Fintype ι]
    (φ : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ)
    (a b : ι → TangentSpace I x) (c d : ι → ℝ) :
    φ (∑ i, c i • a i) (∑ j, d j • b j) = ∑ i, ∑ j, φ (a i) (b j) * c i * d j := by
  have h1 : φ (∑ i, c i • a i) = ∑ i, c i • φ (a i) := by
    rw [map_sum]; simp only [map_smul]
  rw [h1]
  simp only [sum_apply, smul_apply]
  apply Finset.sum_congr rfl
  intro i _
  have h2 : (φ (a i)) (∑ j, d j • b j) = ∑ j, d j • (φ (a i)) (b j) := by
    rw [map_sum]; simp only [map_smul]
  rw [h2, Finset.smul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp only [smul_eq_mul]
  ring

theorem formInFrame_frameMat
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H' : Type*} [TopologicalSpace H'] {I : ModelWithCorners ℝ E H'}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H' M] [IsManifold I (⊤ : ℕ∞) M]
    {x₀ x : M} (hx : x ∈ (trivializationAt E (TangentSpace I) x₀).baseSet)
    (φ : TangentSpace I x →L[ℝ] TangentSpace I x →L[ℝ] ℝ) :
    Work.Diff.EXT.formInFrame (I := I) x₀ x (Work.Diff.EXT.frameMat (I := I) x₀ x φ) = φ := by
  -- the frame spans: every tangent vector is the sum of the frame vectors times its coordinates
  have hfvfc : ∀ v : TangentSpace I x, Submission.Geodesic.frameVector (I := I) x₀ x
      (Work.Diff.EXT.frameCoords (I := I) x₀ x v) = v := by
    intro v
    exact Trivialization.symmL_continuousLinearMapAt
      (trivializationAt E (TangentSpace I) x₀) hx v
  have hdecomp : ∀ u : TangentSpace I x, u =
      ∑ i, ((Work.Diff.EXT.bB (E := E)).coord i) (Work.Diff.EXT.frameCoords (I := I) x₀ x u) •
        Submission.Geodesic.frameVector (I := I) x₀ x (Work.Diff.EXT.bB (E := E) i) := by
    intro u
    have h1 : (∑ i, ((Work.Diff.EXT.bB (E := E)).coord i)
          (Work.Diff.EXT.frameCoords (I := I) x₀ x u) • (Work.Diff.EXT.bB (E := E) i))
        = Work.Diff.EXT.frameCoords (I := I) x₀ x u := by
      conv_rhs => rw [← (Work.Diff.EXT.bB (E := E)).sum_repr
        (Work.Diff.EXT.frameCoords (I := I) x₀ x u)]
      simp only [Module.Basis.coord_apply]
    calc u = Submission.Geodesic.frameVector (I := I) x₀ x
            (Work.Diff.EXT.frameCoords (I := I) x₀ x u) := (hfvfc u).symm
      _ = Submission.Geodesic.frameVector (I := I) x₀ x
            (∑ i, ((Work.Diff.EXT.bB (E := E)).coord i)
              (Work.Diff.EXT.frameCoords (I := I) x₀ x u) • (Work.Diff.EXT.bB (E := E) i)) := by
          rw [h1]
      _ = ∑ i, ((Work.Diff.EXT.bB (E := E)).coord i)
            (Work.Diff.EXT.frameCoords (I := I) x₀ x u) •
            Submission.Geodesic.frameVector (I := I) x₀ x (Work.Diff.EXT.bB (E := E) i) := by
          show (trivializationAt E (TangentSpace I) x₀).symmL ℝ x
              (∑ i, ((Work.Diff.EXT.bB (E := E)).coord i)
                (Work.Diff.EXT.frameCoords (I := I) x₀ x u) • (Work.Diff.EXT.bB (E := E) i))
            = ∑ i, ((Work.Diff.EXT.bB (E := E)).coord i)
                (Work.Diff.EXT.frameCoords (I := I) x₀ x u) •
                (trivializationAt E (TangentSpace I) x₀).symmL ℝ x (Work.Diff.EXT.bB (E := E) i)
          rw [map_sum]
          simp only [map_smul]
  ext u v
  rw [Work.Diff.EXT.formInFrame_apply]
  simp only [Work.Diff.EXT.frameMat]
  conv_rhs => rw [hdecomp u, hdecomp v]
  rw [formInFrame_bilin_expand]

end Work.Diff.EXT.FrameKit
