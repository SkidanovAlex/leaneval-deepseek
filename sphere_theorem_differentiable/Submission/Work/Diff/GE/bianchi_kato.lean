import Submission.Work.Diff.GE.bianchi_kato_defs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.kato_array
import Submission.Work.Diff.GE.scalar_gradient_bound
import Submission.Work.Diff.GE.isAlgCurv_rmFrame
import Submission.Work.Diff.GE.gradSq_scalAt
import Submission.Work.Diff.GE.gradSq_rmoNormSq
import Submission.Work.Diff.Evol.covRm_skew12
import Submission.Work.Diff.GE.Kato3.CovRmKit
import Submission.Work.Diff.Evol.differential_bianchi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-! Guidance from the project lead (the requester):

CONTEXT: this is one area of the Brendle–Schoen differentiable sphere theorem, driven by the lead.
The contracts in Submission/Diff/Interfaces.lean and Submission/Diff/Alg.lean are frozen.

ROUTE (as implemented here). For a smooth metric `g` on a compact manifold and a point `x`, the array
`T m i j k l := covRm g x (e m) (e i) (e j) (e k) (e l)` (`e := onFrame g x`) is the array of first
covariant derivatives of the curvature tensor in an orthonormal frame; it is antisymmetric in `(i,j)`
and in `(k,l)` and satisfies the second Bianchi identity
`T m i j k l + T i j m k l + T j m i k l = 0`. Hence `Work.Diff.GE.scalar_gradient_bound` bounds the
trace `∑ᵢⱼ T m i j i j` (which is `∇ₘS`, by `Work.Diff.GE.gradSq_scalAt` and the definition of
`drmoNormSq`) by the trace-free norm `∑ₘ frobSq (T m) - 2(∑ᵢⱼ T m i j i j)²/(n(n-1)) = drmoNormSq g x`
— this is the first conjunct.
The second conjunct is Kato: `Work.Diff.GE.gradSq_rmoNormSq` identifies `gradSq g (rmoNormSq g) x`
with `∑ₘ (2∑ᵢⱼₖₗ (Rm°)ᵢⱼₖₗ (∇ₘRm°)ᵢⱼₖₗ)²`, and the Cauchy–Schwarz inequality
`Work.Diff.GE.kato_array` bounds it by `4 |Rm°|² |∇Rm°|² = 4 rmoNormSq g x * drmoNormSq g x`.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option maxHeartbeats 1000000

namespace Work.Diff.GE

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

theorem bianchi_kato
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hn : 3 ≤ Module.finrank ℝ E) (hLC : LCSmooth I M) :
    BianchiKato I M := by
  obtain ⟨K, hK₁, hbound⟩ := scalar_gradient_bound (n := Module.finrank ℝ E) hn
  refine ⟨K, hK₁, ?_⟩
  intro g x
  -- the array of first covariant derivatives of the curvature, in the frame `onFrame g x`
  obtain ⟨hcov⟩ := (hLC g).1
  have htor : (lcOf g).torsion = 0 := (hLC g).2.1
  have hmet : MetricCompat g := (hLC g).2.2
  let e : Fin (Module.finrank ℝ E) → TangentSpace I x := onFrame g x
  let T : Fin (Module.finrank ℝ E) → Curv4 (Module.finrank ℝ E) := fun m i j k l =>
    covRm g x (e m) (e i) (e j) (e k) (e l)
  -- the three symmetries of `T`
  have hT1 : ∀ m i j k l, T m j i k l = - T m i j k l := by
    intro m i j k l
    have h := Work.Diff.Evol.covRm_skew12 hLC g x (e m) (e j) (e i) (e k) (e l)
    simp only [T]
    linarith
  have hT2 : ∀ m i j k l, T m i j l k = - T m i j k l := by
    intro m i j k l
    have h := Work.Diff.GE.Kato3.covRm_skew_last hLC g x (e m) (e i) (e j) (e k) (e l)
    simp only [T]
    linarith
  have hT3 : ∀ m i j k l,
      T m i j k l + T i j m k l + T j m i k l = 0 :=
    fun m i j k l => Work.Diff.Evol.differential_bianchi hLC g x (e m) (e i) (e j) (e k) (e l)
  -- `dRmNormSq` is the sum of the Frobenius norms of the slices of `T`
  have hD : dRmNormSq g x = ∑ m, frobSq (T m) := by
    simp only [dRmNormSq, frobSq, T, e]
  -- the gradient of the scalar curvature is the trace of `∇Rm`
  have hA := gradSq_scalAt (I := I) (M := M) hLC g x
  constructor
  · -- first conjunct
    rw [drmoNormSq, hA, hD]
    exact hbound T hT1 hT2 hT3
  · -- second conjunct
    have hK : IsAlgCurv (rmC g x) := by
      show IsAlgCurv (rmFrame g x (onFrame g x))
      exact isAlgCurv_rmFrame (I := I) (M := M) g hcov htor hmet x (onFrame g x)
    have hB := gradSq_rmoNormSq (I := I) (M := M) hLC g x
    rw [hB, rmoNormSq, drmoNormSq, hA, hD]
    simp only [tfRm, tfDRm, T, e]
    exact kato_array (rmC g x) hK T hT1 hT2

end Work.Diff.GE
