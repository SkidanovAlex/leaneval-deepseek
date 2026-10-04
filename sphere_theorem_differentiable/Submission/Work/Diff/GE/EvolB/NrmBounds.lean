import Mathlib
import Submission.Work.Diff.GE.EvolB.Lib
import Submission.Work.Diff.GE.MovingFrame.covRm5_contMultilinear_bound
import Submission.Work.Diff.GE.curvDerivNormSq_le

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Norm bounds for `covRm`, `rmVec` and `curvDeriv` (`EvolB`)

The pointwise estimates
`|∇Rm(u,a,b,c,d)| ≤ √|∇Rm|² · |u||a||b||c||d|`,
`|R(X,Y)Z| ≤ √n √|Rm|² |X||Y||Z|`,
`|(∇_X R)(Y,P)Z| ≤ √|∇Rm|² |X||Y||P||Z|`
used in the Weitzenböck / reaction estimates.  All are consequences of already proved results of
the workspace (`covRm5_contMultilinear_bound` and `curvDerivNormSq_le`; the curvature-vector bound
comes from the delegated `rmVec_normSq_le_B`), rewritten with the shorthand `nrm g x v` for the
metric norm `√(g.inner x v v)`.

**Caution.**  `Submission.Work.Diff.GE.connectionVariation_le` (which contains the smooth-level
`rmP_norm_bound_smooth`) is *not* imported here on purpose: its transitive closure currently pulls
in `Submission.Work.Diff.GE.covReactionFormAt_le_A`, which is being edited by another agent.  A
smooth-level `rmP` bound is provided in `Submission/Work/Diff/GE/EvolB/rmPbound_B.lean`.
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
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The metric norm `|v| = √(g.inner x v v)` of a tangent vector. -/
noncomputable def nrm (g : SMet I M) (x : M) (v : TangentSpace I x) : ℝ :=
  Real.sqrt (g.inner x v v)

theorem inner_self_nonneg_B (g : SMet I M) (x : M) (v : TangentSpace I x) :
    0 ≤ g.inner x v v := by
  rcases eq_or_ne v 0 with h | h
  · rw [h]
    simp
  · exact le_of_lt (g.pos x v h)

theorem nrm_nonneg (g : SMet I M) (x : M) (v : TangentSpace I x) : 0 ≤ nrm g x v :=
  Real.sqrt_nonneg _

theorem nrm_sq (g : SMet I M) (x : M) (v : TangentSpace I x) :
    nrm g x v ^ 2 = g.inner x v v := by
  rw [nrm, Real.sq_sqrt (inner_self_nonneg_B g x v)]

theorem nrm_eq_sqrt (g : SMet I M) (x : M) (v : TangentSpace I x) :
    nrm g x v = Real.sqrt (g.inner x v v) := rfl

/-- The pointwise Frobenius bound for `∇Rm`: `|∇Rm(u,a,b,c,d)| ≤ √|∇Rm|² |u||a||b||c||d|`. -/
theorem covRm_norm_le_B [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (u a b c d : TangentSpace I x) :
    |covRm g x u a b c d|
      ≤ Real.sqrt (dRmNormSq g x) * nrm g x u * nrm g x a * nrm g x b * nrm g x c
          * nrm g x d := by
  obtain ⟨A, hA, hAb⟩ := Work.Diff.GE.MovingFrame.covRm5_contMultilinear_bound hLC g x
  have h := hAb ![u, a, b, c, d]
  rw [hA] at h
  have hdv : Work.Diff.GE.MovingFrame.covRm5 g x ![u, a, b, c, d] = covRm g x u a b c d := by
    simp [Work.Diff.GE.MovingFrame.covRm5]
  have han : Work.Diff.GE.MovingFrame.argNorms g x ![u, a, b, c, d]
      = nrm g x u * nrm g x a * nrm g x b * nrm g x c * nrm g x d := by
    rw [Work.Diff.GE.MovingFrame.argNorms, Fin.prod_univ_five]
    simp [nrm]
  have hdn : Work.Diff.GE.MovingFrame.dRmNorm g x = Real.sqrt (dRmNormSq g x) := rfl
  rw [hdv, han, hdn] at h
  calc |covRm g x u a b c d|
      ≤ Real.sqrt (dRmNormSq g x) * (nrm g x u * nrm g x a * nrm g x b * nrm g x c * nrm g x d) := h
    _ = Real.sqrt (dRmNormSq g x) * nrm g x u * nrm g x a * nrm g x b * nrm g x c
          * nrm g x d := by ring

/-- The norm bound for `(∇_X R)(Y,P)Z`, from the already proved
`Work.Diff.GE.curvDerivNormSq_le`. -/
theorem curvDeriv_nrm_le_B [T2Space M]
    (hLC : LCSmooth I M) (g : SMet I M) (x : M) (X Y P Z : TangentSpace I x) :
    nrm g x (Work.Diff.GE.curvDeriv g x X Y P Z)
      ≤ Real.sqrt (dRmNormSq g x) * nrm g x X * nrm g x Y * nrm g x P * nrm g x Z := by
  have h := Work.Diff.GE.curvDerivNormSq_le (I := I) (M := M) hLC g x X Y P Z
  have hD : (0 : ℝ) ≤ dRmNormSq g x := by
    rw [dRmNormSq]
    positivity
  have h1 : dRmNormSq g x * g.inner x X X * g.inner x Y Y * g.inner x P P * g.inner x Z Z
      = (Real.sqrt (dRmNormSq g x) * nrm g x X * nrm g x Y * nrm g x P * nrm g x Z) ^ 2 := by
    rw [show (Real.sqrt (dRmNormSq g x) * nrm g x X * nrm g x Y * nrm g x P * nrm g x Z) ^ 2
        = Real.sqrt (dRmNormSq g x) ^ 2 * nrm g x X ^ 2 * nrm g x Y ^ 2 * nrm g x P ^ 2
          * nrm g x Z ^ 2 from by ring]
    rw [Real.sq_sqrt hD, nrm_sq g x X, nrm_sq g x Y, nrm_sq g x P, nrm_sq g x Z]
  have hsq : nrm g x (Work.Diff.GE.curvDeriv g x X Y P Z) ^ 2
      ≤ (Real.sqrt (dRmNormSq g x) * nrm g x X * nrm g x Y * nrm g x P * nrm g x Z) ^ 2 := by
    rw [nrm_sq]
    calc g.inner x (Work.Diff.GE.curvDeriv g x X Y P Z)
          (Work.Diff.GE.curvDeriv g x X Y P Z)
        ≤ dRmNormSq g x * g.inner x X X * g.inner x Y Y * g.inner x P P
            * g.inner x Z Z := h
      _ = (Real.sqrt (dRmNormSq g x) * nrm g x X * nrm g x Y * nrm g x P * nrm g x Z) ^ 2 := h1
  exact le_of_sq_le_sq hsq (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg
    (Real.sqrt_nonneg _) (nrm_nonneg g x X)) (nrm_nonneg g x Y)) (nrm_nonneg g x P))
    (nrm_nonneg g x Z))

end Work.Diff.GE.EvolB
