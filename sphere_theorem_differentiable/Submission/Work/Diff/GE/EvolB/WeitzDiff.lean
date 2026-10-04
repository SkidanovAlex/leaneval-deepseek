import Mathlib
import Submission.Work.Diff.GE.EvolB.covLapRmAt_eq_sum_cov3Rm_B
import Submission.Work.Diff.GE.EvolB.cov3Rm_ricci_B
import Submission.Work.Diff.GE.EvolB.cov3Rm_swap_B

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# The Weitzenböck difference `∇_v(ΔRm) − Δ(∇Rm)` (`EvolB`)

`Work.Diff.GE.EvolB.covLapRm_sub_lapCovRm_eq_B` is the exact identity

`covLapRmAt g x v a b c d − lapCovRmAt g x v a b c d
  = ∑ m ( −(covRm (R(v,e_m)e_m) a b c d + the four slot terms) − (the four `rmP (curvDeriv …)` terms)
        − (the four `covRm (e_m) (R(v,e_m) slot)` terms) )`

with `e = onFrame g x`: the two traces of `∇³Rm` (`∇_v` of the trace over a smooth orthonormal
frame, versus the trace of `∇_v∇∇Rm`) differ by the terms produced by two applications of the Ricci
identity (first two slots, and second/third slots).  The `(1 + 4 + 4 + 4)` summands per `m` are all
of the form `Rm ∗ ∇Rm`, which is what the following estimate bounds.
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.EvolB

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ((⊤ : ENat) : WithTop ENat) M] [T2Space M]

/-- **The Weitzenböck commutator identity.**  The difference of the two traces of `∇³Rm` is the sum
over the frame of the two Ricci-identity corrections. -/
theorem covLapRm_sub_lapCovRm_eq_B
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M) (x : M)
    (v a b c d : TangentSpace I x) :
    Work.Diff.GE.covLapRmAt g x v a b c d - Work.Diff.GE.lapCovRmAt g x v a b c d
      = ∑ m, (- (Submission.Diff.covRm g x
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m)
                (Submission.Diff.onFrame g x m)) a b c d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m)
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) a)
              b c d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) b)
              c d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a b
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) c)
              d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a b c
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) d))
          - (Submission.Diff.rmP g x
              (Work.Diff.GE.curvDeriv g x (Submission.Diff.onFrame g x m) v
                (Submission.Diff.onFrame g x m) a) b c d
            + Submission.Diff.rmP g x a
              (Work.Diff.GE.curvDeriv g x (Submission.Diff.onFrame g x m) v
                (Submission.Diff.onFrame g x m) b) c d
            + Submission.Diff.rmP g x a b
              (Work.Diff.GE.curvDeriv g x (Submission.Diff.onFrame g x m) v
                (Submission.Diff.onFrame g x m) c) d
            + Submission.Diff.rmP g x a b c
              (Work.Diff.GE.curvDeriv g x (Submission.Diff.onFrame g x m) v
                (Submission.Diff.onFrame g x m) d))
          - (Submission.Diff.covRm g x (Submission.Diff.onFrame g x m)
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) a)
              b c d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) b)
              c d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a b
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) c)
              d
            + Submission.Diff.covRm g x (Submission.Diff.onFrame g x m) a b c
              (Submission.Diff.rmVec (Submission.Diff.lcOf g) x v (Submission.Diff.onFrame g x m) d))) := by
  have hQ' : Work.Diff.GE.covLapRmAt g x v a b c d
      = ∑ m, Work.Diff.GE.cov3Rm g x v (Submission.Diff.onFrame g x m)
          (Submission.Diff.onFrame g x m) a b c d :=
    covLapRmAt_eq_sum_cov3Rm_B (I := I) (M := M) hLC g x v a b c d
  have hQ : Work.Diff.GE.lapCovRmAt g x v a b c d
      = ∑ m, Work.Diff.GE.cov3Rm g x (Submission.Diff.onFrame g x m)
          (Submission.Diff.onFrame g x m) v a b c d := rfl
  rw [hQ', hQ, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  -- the two Ricci identities at the frame vector `e m`
  have hA := cov3Rm_ricci_B (I := I) (M := M) hLC g x v
    (Submission.Diff.onFrame g x m) (Submission.Diff.onFrame g x m) a b c d
  have hB := cov3Rm_swap_B (I := I) (M := M) hLC g x
    (Submission.Diff.onFrame g x m) v (Submission.Diff.onFrame g x m) a b c d
  linarith [hA, hB]

end Work.Diff.GE.EvolB
