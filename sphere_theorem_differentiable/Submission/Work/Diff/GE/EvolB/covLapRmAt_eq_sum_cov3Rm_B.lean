import Mathlib
import Submission.Work.Diff.GE.EvolB.Lib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 2000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.EvolB

namespace Work.Diff.GE.EvolB

/-- The frame-motion cancellation for the rough Laplacian: the covariant derivative `∇_v(ΔRm)` of
the rough Laplacian of the curvature (the `Ext` pattern `Work.Diff.GE.covLapRmAt`) is the trace
`∑ m, ∇_v∇_m∇_m Rm` of the third covariant derivative in the `Classical.epsilon`-chosen orthonormal
frame `onFrame g x`.  (In `Work.Diff.GE.cov3Rm g x v (e m) (e m) a b c d` the first slot `v` is the
outer differentiation direction, so the sum is `∑ m ∇_v∇_{e_m}∇_{e_m} Rm`.)

This is a re-proof (in namespace `Work.Diff.GE.EvolB`) of the statement of
`Submission/Work/Diff/GE/covLapRmAt_eq_sum_cov3Rm.lean`, which contains a `sorry`; do not import
that file (the `EvolB` development must stay `sorry`-free).

Route.  `Work.Diff.GE.onFrameONfield` (PROVED) gives a family `E` of smooth fields which is
`g`-orthonormal near `x` with `E i x = onFrame g x i`; `Work.Diff.GE.lapRmAt_trace` (PROVED) lets
one compute `lapRmAt g y (A y) (B y) (C y) (D y)` in the frame `E y` (for `y` near `x`), so

`covLapRmAt g x v a b c d = ∑ m, (mvfderiv (fun y => cov2Rm g y (E m y) (E m y) (A y).. ) x v
  - the six Leibniz corrections of the `Ext` pattern) - (the four slot terms of `covLapRmAt`)`.

Interchanging `mvfderiv` with the finite sum (`Work.Diff.GE.Kato3.mvfderiv_sum`) and writing
`cov2Rm` back in terms of `cov3RmExt` gives, for each `m`, the summand
`cov3RmExt g x v (E m) (E m) A B C D` plus the two *frame-motion* terms
`cov2Rm g x (lcOf g (E m) x v) (E m x) ...` and `cov2Rm g x (E m x) (lcOf g (E m) x v) ...`
(the other four corrections of `cov3RmExt` are exactly the slot terms subtracted in `covLapRmAt`,
so they cancel).  The frame-motion terms cancel in the sum by
`Work.Diff.GE.frameMotion_cancel_cov2Rm` (PROVED), and `cov3RmExt g x v (E m) (E m) A B C D` is
`cov3Rm g x v (E m x) (E m x) a b c d` by the value-dependence
`Work.Diff.GE.kato_cov3RmExt_field` (PROVED); finally `E m x = onFrame g x m`. -/
theorem covLapRmAt_eq_sum_cov3Rm_B
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (v a b c d : TangentSpace I x) :
    Work.Diff.GE.covLapRmAt g x v a b c d
      = ∑ m, Work.Diff.GE.cov3Rm g x v (Submission.Diff.onFrame g x m)
          (Submission.Diff.onFrame g x m) a b c d := by
  classical
  -- a globally smooth family of fields, `g`-orthonormal near `x`, with `E m x = onFrame g x m`
  obtain ⟨Ef, hEsm, hEON, hEval⟩ := Work.Diff.GE.onFrameONfield hLC g x
  have hA : CMDiff ∞ (T% (smoothExt x a)) := Work.Diff.GE.smoothExt_cmdiff x a
  have hB : CMDiff ∞ (T% (smoothExt x b)) := Work.Diff.GE.smoothExt_cmdiff x b
  have hC : CMDiff ∞ (T% (smoothExt x c)) := Work.Diff.GE.smoothExt_cmdiff x c
  have hD : CMDiff ∞ (T% (smoothExt x d)) := Work.Diff.GE.smoothExt_cmdiff x d
  -- ## Step 1: compute `lapRmAt` in the frame `Ef`, and split the derivative of the sum
  have hmvf1 : mvfderiv I (fun y : M => Work.Diff.GE.lapRmAt g y (smoothExt x a y)
        (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v
      = mvfderiv I (fun y : M => ∑ m, Work.Diff.GE.cov2Rm g y (Ef m y) (Ef m y)
        (smoothExt x a y) (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v := by
    exact congrArg (fun L : TangentSpace I x →L[ℝ] ℝ => L v)
      (Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I) (by
        filter_upwards [hEON] with y hy
        exact Work.Diff.GE.lapRmAt_trace hLC g y (fun m => Ef m y) hy _ _ _ _))
  have hsm : ∀ m : Fin (Module.finrank ℝ E), CMDiff ∞ (fun y : M => Work.Diff.GE.cov2Rm g y
        (Ef m y) (Ef m y) (smoothExt x a y) (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) :=
    fun m => Work.Diff.GE.Kato3.cov2Rm_field_smooth (g := g) hLC (hEsm m) (hEsm m) hA hB hC hD
  have hmvf2 : mvfderiv I (fun y : M => ∑ m, Work.Diff.GE.cov2Rm g y (Ef m y) (Ef m y)
        (smoothExt x a y) (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v
      = ∑ m, mvfderiv I (fun y : M => Work.Diff.GE.cov2Rm g y (Ef m y) (Ef m y)
        (smoothExt x a y) (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v := by
    simpa using Work.Diff.GE.Kato3.mvfderiv_sum (I := I) (M := M)
      (Finset.univ : Finset (Fin (Module.finrank ℝ E))) (fun m y => Work.Diff.GE.cov2Rm g y
        (Ef m y) (Ef m y) (smoothExt x a y) (smoothExt x b y) (smoothExt x c y) (smoothExt x d y))
      hsm x v
  -- ## Step 2: unfold `cov3RmExt` into the six corrections, for each `m`
  have hcov3 : ∀ m : Fin (Module.finrank ℝ E),
      mvfderiv I (fun y : M => Work.Diff.GE.cov2Rm g y (Ef m y) (Ef m y)
        (smoothExt x a y) (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v
      = Work.Diff.GE.cov3RmExt g x v (Ef m) (Ef m) (smoothExt x a) (smoothExt x b)
          (smoothExt x c) (smoothExt x d)
        + (Work.Diff.GE.cov2Rm g x (lcOf g (Ef m) x v) (Ef m x) a b c d
           + Work.Diff.GE.cov2Rm g x (Ef m x) (lcOf g (Ef m) x v) a b c d)
        + (Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) (lcOf g (smoothExt x a) x v) b c d
           + Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) a (lcOf g (smoothExt x b) x v) c d
           + Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) a b (lcOf g (smoothExt x c) x v) d
           + Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) a b c (lcOf g (smoothExt x d) x v)) := by
    intro m
    unfold Work.Diff.GE.cov3RmExt
    simp only [Work.Diff.GE.smoothExt_apply]
    ring
  -- the two frame-motion corrections cancel in the sum
  have hfm : (∑ m, (Work.Diff.GE.cov2Rm g x (lcOf g (Ef m) x v) (Ef m x) a b c d
        + Work.Diff.GE.cov2Rm g x (Ef m x) (lcOf g (Ef m) x v) a b c d)) = 0 :=
    Work.Diff.GE.frameMotion_cancel_cov2Rm hLC g x Ef hEsm hEON v a b c d
  -- each of the four slot corrections is a slot term of `covLapRmAt`
  have hsl3 : (∑ m, Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) (lcOf g (smoothExt x a) x v) b c d)
      = Work.Diff.GE.lapRmAt g x (lcOf g (smoothExt x a) x v) b c d := by
    rw [show (∑ m, Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) (lcOf g (smoothExt x a) x v) b c d)
        = ∑ m, Work.Diff.GE.cov2Rm g x (Submission.Diff.onFrame g x m)
            (Submission.Diff.onFrame g x m) (lcOf g (smoothExt x a) x v) b c d
        from Finset.sum_congr rfl (fun m _ => by rw [hEval m])]
    rfl
  have hsl4 : (∑ m, Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) a (lcOf g (smoothExt x b) x v) c d)
      = Work.Diff.GE.lapRmAt g x a (lcOf g (smoothExt x b) x v) c d := by
    rw [show (∑ m, Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) a (lcOf g (smoothExt x b) x v) c d)
        = ∑ m, Work.Diff.GE.cov2Rm g x (Submission.Diff.onFrame g x m)
            (Submission.Diff.onFrame g x m) a (lcOf g (smoothExt x b) x v) c d
        from Finset.sum_congr rfl (fun m _ => by rw [hEval m])]
    rfl
  have hsl5 : (∑ m, Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) a b (lcOf g (smoothExt x c) x v) d)
      = Work.Diff.GE.lapRmAt g x a b (lcOf g (smoothExt x c) x v) d := by
    rw [show (∑ m, Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) a b (lcOf g (smoothExt x c) x v) d)
        = ∑ m, Work.Diff.GE.cov2Rm g x (Submission.Diff.onFrame g x m)
            (Submission.Diff.onFrame g x m) a b (lcOf g (smoothExt x c) x v) d
        from Finset.sum_congr rfl (fun m _ => by rw [hEval m])]
    rfl
  have hsl6 : (∑ m, Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) a b c (lcOf g (smoothExt x d) x v))
      = Work.Diff.GE.lapRmAt g x a b c (lcOf g (smoothExt x d) x v) := by
    rw [show (∑ m, Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) a b c (lcOf g (smoothExt x d) x v))
        = ∑ m, Work.Diff.GE.cov2Rm g x (Submission.Diff.onFrame g x m)
            (Submission.Diff.onFrame g x m) a b c (lcOf g (smoothExt x d) x v)
        from Finset.sum_congr rfl (fun m _ => by rw [hEval m])]
    rfl
  have hsl : (∑ m, (Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) (lcOf g (smoothExt x a) x v) b c d
           + Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) a (lcOf g (smoothExt x b) x v) c d
           + Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) a b (lcOf g (smoothExt x c) x v) d
           + Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) a b c (lcOf g (smoothExt x d) x v)))
      = Work.Diff.GE.lapRmAt g x (lcOf g (smoothExt x a) x v) b c d
        + Work.Diff.GE.lapRmAt g x a (lcOf g (smoothExt x b) x v) c d
        + Work.Diff.GE.lapRmAt g x a b (lcOf g (smoothExt x c) x v) d
        + Work.Diff.GE.lapRmAt g x a b c (lcOf g (smoothExt x d) x v) := by
    simp only [Finset.sum_add_distrib]
    rw [hsl3, hsl4, hsl5, hsl6]
  -- ## Step 3: the sum of the pointwise decompositions
  have hsum_split : (∑ m, mvfderiv I (fun y : M => Work.Diff.GE.cov2Rm g y (Ef m y) (Ef m y)
        (smoothExt x a y) (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v)
      = (∑ m, Work.Diff.GE.cov3RmExt g x v (Ef m) (Ef m) (smoothExt x a) (smoothExt x b)
          (smoothExt x c) (smoothExt x d))
        + (∑ m, (Work.Diff.GE.cov2Rm g x (lcOf g (Ef m) x v) (Ef m x) a b c d
           + Work.Diff.GE.cov2Rm g x (Ef m x) (lcOf g (Ef m) x v) a b c d))
        + (∑ m, (Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) (lcOf g (smoothExt x a) x v) b c d
           + Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) a (lcOf g (smoothExt x b) x v) c d
           + Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) a b (lcOf g (smoothExt x c) x v) d
           + Work.Diff.GE.cov2Rm g x (Ef m x) (Ef m x) a b c (lcOf g (smoothExt x d) x v))) := by
    rw [Finset.sum_congr rfl (fun m _ => hcov3 m)]
    simp only [Finset.sum_add_distrib]
  have step2 : (∑ m, mvfderiv I (fun y : M => Work.Diff.GE.cov2Rm g y (Ef m y) (Ef m y)
        (smoothExt x a y) (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v)
      = (∑ m, Work.Diff.GE.cov3RmExt g x v (Ef m) (Ef m) (smoothExt x a) (smoothExt x b)
          (smoothExt x c) (smoothExt x d))
        + Work.Diff.GE.lapRmAt g x (lcOf g (smoothExt x a) x v) b c d
        + Work.Diff.GE.lapRmAt g x a (lcOf g (smoothExt x b) x v) c d
        + Work.Diff.GE.lapRmAt g x a b (lcOf g (smoothExt x c) x v) d
        + Work.Diff.GE.lapRmAt g x a b c (lcOf g (smoothExt x d) x v) := by
    rw [hsum_split, hfm, hsl]
    ring
  have step1 : mvfderiv I (fun y : M => Work.Diff.GE.lapRmAt g y (smoothExt x a y)
        (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v
      = ∑ m, mvfderiv I (fun y : M => Work.Diff.GE.cov2Rm g y (Ef m y) (Ef m y)
        (smoothExt x a y) (smoothExt x b y) (smoothExt x c y) (smoothExt x d y)) x v :=
    hmvf1.trans hmvf2
  have step3 : Work.Diff.GE.covLapRmAt g x v a b c d
      = ∑ m, Work.Diff.GE.cov3RmExt g x v (Ef m) (Ef m) (smoothExt x a) (smoothExt x b)
          (smoothExt x c) (smoothExt x d) := by
    unfold Work.Diff.GE.covLapRmAt
    rw [step1, step2]
    ring
  -- ## Step 4: `cov3RmExt` only sees the values, and `Ef m x = onFrame g x m`
  rw [step3]
  refine Finset.sum_congr rfl (fun m _ => ?_)
  rw [show Work.Diff.GE.cov3Rm g x v (Submission.Diff.onFrame g x m)
        (Submission.Diff.onFrame g x m) a b c d
      = Work.Diff.GE.cov3RmExt g x v (smoothExt x (Ef m x)) (smoothExt x (Ef m x))
        (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) from by
    rw [← hEval m]; rfl]
  exact Work.Diff.GE.kato_cov3RmExt_field (I := I) (M := M) hLC g x (Ef m) (Ef m) (smoothExt x a)
      (smoothExt x b) (smoothExt x c) (smoothExt x d) (smoothExt x (Ef m x)) (smoothExt x (Ef m x))
      (smoothExt x a) (smoothExt x b) (smoothExt x c) (smoothExt x d) (hEsm m) (hEsm m) hA hB hC hD
      (Work.Diff.GE.smoothExt_cmdiff x (Ef m x)) (Work.Diff.GE.smoothExt_cmdiff x (Ef m x)) hA hB hC hD
      (Work.Diff.GE.smoothExt_apply x (Ef m x)).symm (Work.Diff.GE.smoothExt_apply x (Ef m x)).symm
      rfl rfl rfl rfl v

end Work.Diff.GE.EvolB

/-- The same statement under the requested name `Work.Diff.GE.EvolB.covLapRmAt_eq_sum_cov3Rm_B`
(the `namespace Work.Diff.GE.EvolB` line carried by the statement block above is *nested* inside the
ambient `namespace Work.Diff.GE.EvolB` of this file, so the declaration proved above is registered
as `Work.Diff.GE.EvolB.Work.Diff.GE.EvolB.covLapRmAt_eq_sum_cov3Rm_B`; this is the same theorem,
whose proof is the one above). -/
theorem covLapRmAt_eq_sum_cov3Rm_B
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
    [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (v a b c d : TangentSpace I x) :
    Work.Diff.GE.covLapRmAt g x v a b c d
      = ∑ m, Work.Diff.GE.cov3Rm g x v (Submission.Diff.onFrame g x m)
          (Submission.Diff.onFrame g x m) a b c d :=
  Work.Diff.GE.EvolB.Work.Diff.GE.EvolB.covLapRmAt_eq_sum_cov3Rm_B hLC g x v a b c d

end Work.Diff.GE.EvolB
