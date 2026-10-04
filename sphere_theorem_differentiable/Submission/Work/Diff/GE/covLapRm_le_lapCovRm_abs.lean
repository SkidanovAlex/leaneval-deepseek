import Mathlib
import Submission.Work.Diff.GE.NablaRm
import Submission.Work.Diff.GE.ReactionDefs
import Submission.Work.Diff.GE.covLapRm_sub_lapCovRm_eq
import Submission.Work.Diff.GE.covLapRm_sub_lapCovRm_summand_bound

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

/-- `|-(a) - b - c| = |a + b + c|`. -/
private theorem abs_neg_sub_sub (a b c : ℝ) : |-(a) - (b) - (c)| = |a + b + c| := by
  rw [show -(a) - (b) - (c) = -(a + b + c) by ring, abs_neg]

theorem covLapRm_le_lapCovRm_abs
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (g : Submission.Diff.SMet I M) (x : M)
        (v a b c d : TangentSpace I x),
      |Work.Diff.GE.covLapRmAt g x v a b c d - Work.Diff.GE.lapCovRmAt g x v a b c d|
        ≤ C * Real.sqrt (Submission.Diff.rmNormSq g x)
            * Real.sqrt (Submission.Diff.dRmNormSq g x)
            * (Real.sqrt (g.inner x v v) * Real.sqrt (g.inner x a a)
              * Real.sqrt (g.inner x b b) * Real.sqrt (g.inner x c c)
              * Real.sqrt (g.inner x d d)) := by
  refine ⟨13 * (Module.finrank ℝ E : ℝ), by positivity, ?_⟩
  intro g x v a b c d
  rw [covLapRm_sub_lapCovRm_eq hLC g x v a b c d]
  refine le_trans (Finset.abs_sum_le_sum_abs _ _) ?_
  simp_rw [abs_neg_sub_sub]
  refine le_trans (Finset.sum_le_sum (fun m _ =>
    covLapRm_sub_lapCovRm_summand_bound hLC g x v a b c d m)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  apply le_of_eq
  ring

end Work.Diff.GE
