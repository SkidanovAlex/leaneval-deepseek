import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.Frame
import Submission.Work.Diff.GE.Gest.Base
import Submission.Work.Diff.GE.Kato3.CovRmKit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- **The pointwise Laplacian is additive over finite sums.**  For a finite family of globally smooth
functions `f i`, `laplAt g (fun y ↦ ∑ i, f i y) x = ∑ i, laplAt g (f i) x`.  The frame in `laplAt` is
the fixed `onFrame g x`, so this is only the additivity of `mvfderiv` (twice), i.e.
`mvfderiv_sum_apply` (`Submission.ChartCurv`) applied to the sum and to the summed inner functions. -/
theorem kato_lapl_sum
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [T2Space M] [ChartedSpace H M] [IsManifold I ∞ M]
    (g : SMet I M) {ι : Type*} [Fintype ι] (f : ι → M → ℝ) (x : M)
    (hf : ∀ i, CMDiff ∞ (f i)) :
    laplAt g (fun y : M ↦ ∑ i, f i y) x = ∑ i, laplAt g (f i) x := by
  classical
  -- The first derivative of a finite sum of smooth functions is the sum of the derivatives.
  have hd1 : ∀ (y : M) (v : TangentSpace I y),
      mvfderiv I (fun z : M => ∑ i, f i z) y v = ∑ i, mvfderiv I (f i) y v := by
    intro y v
    have h := Work.Diff.GE.Kato3.mvfderiv_sum (I := I) (M := M) (Finset.univ : Finset ι) f hf y v
    simpa using h
  -- The directional derivative of each `f i` along the fixed smooth field `smoothExt x w` is smooth.
  have hGs : ∀ (w : TangentSpace I x) (i : ι),
      CMDiff ∞ (fun y : M => mvfderiv I (f i) y (smoothExt x w y)) :=
    fun w i => Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff (I := I) (M := M)
      (hf i) (Work.Diff.GE.Gest.smoothExt_contMDiff (I := I) (M := M) x w)
  -- Additivity of the Hessian in the frozen frame directions.
  have hhess : ∀ w : TangentSpace I x,
      hessAt g (fun y : M => ∑ i, f i y) x w w = ∑ i, hessAt g (f i) x w w := by
    intro w
    -- the inner function `y ↦ d(∑ f i) y (smoothExt x w y)` is the sum of the pieces
    have hinner : (fun y : M => mvfderiv I (fun z : M => ∑ i, f i z) y (smoothExt x w y))
        = (fun y : M => ∑ i, mvfderiv I (f i) y (smoothExt x w y)) := by
      funext y
      exact hd1 y (smoothExt x w y)
    -- differentiate the sum of the pieces
    have hsumouter :
        mvfderiv I (fun y : M => ∑ i, mvfderiv I (f i) y (smoothExt x w y)) x w
          = ∑ i, mvfderiv I (fun y : M => mvfderiv I (f i) y (smoothExt x w y)) x w := by
      have h := Work.Diff.GE.Kato3.mvfderiv_sum (I := I) (M := M) (Finset.univ : Finset ι)
        (fun i => fun y : M => mvfderiv I (f i) y (smoothExt x w y))
        (fun i => hGs w i) x w
      simpa using h
    have hfirst :
        mvfderiv I (fun y : M => mvfderiv I (fun z : M => ∑ i, f i z) y (smoothExt x w y)) x w
          = ∑ i, mvfderiv I (fun y : M => mvfderiv I (f i) y (smoothExt x w y)) x w := by
      rw [hinner]
      exact hsumouter
    have hsecond : mvfderiv I (fun z : M => ∑ i, f i z) x (lcOf g (smoothExt x w) x w)
        = ∑ i, mvfderiv I (f i) x (lcOf g (smoothExt x w) x w) :=
      hd1 x (lcOf g (smoothExt x w) x w)
    simp only [hessAt]
    rw [hfirst, hsecond, Finset.sum_sub_distrib]
  -- Assemble the frame sum and swap the two finite sums.
  simp only [laplAt]
  rw [show (∑ i, hessAt g (fun y : M => ∑ j, f j y) x (onFrame g x i) (onFrame g x i))
        = ∑ i, ∑ j, hessAt g (f j) x (onFrame g x i) (onFrame g x i) from
      Finset.sum_congr rfl (fun i _ => hhess (onFrame g x i))]
  exact Finset.sum_comm

end Work.Diff.GE
