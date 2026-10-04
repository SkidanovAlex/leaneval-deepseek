import Mathlib
import Submission.Work.Diff.EXT.ChartCoreDefs
import Submission.Work.Diff.GE.curvbasic
import Submission.Work.Diff.GE.ExtTensor
import Submission.Work.Diff.EXT.ATens.Defs
import Submission.Work.Diff.EXT.covKAExt_frame_eq_smoothExt

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Tensoriality of the iterated covariant derivatives of the connection difference

`Work.Diff.EXT.covKAExt G t k v A B C x` is the `k`-th covariant derivative, with respect to the
*fixed* background connection `∇^{G 0} = lcOf (G 0)`, of the lowered connection difference
`aOf G t = g_t(∇^{g_t} − ∇^{g_0})`, evaluated on `k` direction fields `v` and the three argument
fields `A B C`.  It is a `(0,k+3)`-tensor, so its value at `x` depends only on the *values* of the
`k + 3` fields at `x`.

The proof packs the `k` direction slots and the three argument slots into a single `Fin (k+3)`-tuple
and uses the iteration `Work.Diff.EXT.cktA` of `Submission/Work/Diff/EXT/ATens/Defs.lean`.  The
bridge `cktA_mkT3_eq` is definitional:
`covKAExt G t k v A B C x = cktA G t k (mkT3 v (trip3 A B C)) x`.
The value dependence of `cktA` in all slots at once,
`Work.Diff.EXT.ka_val_dep_all` (proved in
`Submission/Work/Diff/EXT/covKAExt_frame_eq_smoothExt.lean`), then gives the statement.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Commons.Geometry.Manifold.VectorField

namespace Work.Diff.EXT

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

theorem covKAExt_tensorial
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (G : ℝ → Submission.Diff.SMet I M) (t : ℝ) (k : ℕ)
    (x : M) (v v' : Fin k → (Π y : M, TangentSpace I y))
    (A A' B B' C C' : Π y : M, TangentSpace I y)
    (hv : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (v i))
    (hv' : ∀ i, Work.Diff.GE.SmoothFieldT (I := I) (M := M) (v' i))
    (hA : Work.Diff.GE.SmoothFieldT (I := I) (M := M) A)
    (hA' : Work.Diff.GE.SmoothFieldT (I := I) (M := M) A')
    (hB : Work.Diff.GE.SmoothFieldT (I := I) (M := M) B)
    (hB' : Work.Diff.GE.SmoothFieldT (I := I) (M := M) B')
    (hC : Work.Diff.GE.SmoothFieldT (I := I) (M := M) C)
    (hC' : Work.Diff.GE.SmoothFieldT (I := I) (M := M) C')
    (hvv : ∀ i, v i x = v' i x) (hAA : A x = A' x) (hBB : B x = B' x) (hCC : C x = C' x) :
    Work.Diff.EXT.covKAExt G t k v A B C x = Work.Diff.EXT.covKAExt G t k v' A' B' C' x := by
  -- smoothness of the two packed tuples
  have hFs : ∀ s, SmA (I := I) (M := M) ((mkT3 v (trip3 A B C)) s) := by
    intro s
    refine Fin.addCases ?_ ?_ s
    · intro i
      rw [mkT3_castAdd]
      exact hv i
    · intro p
      rw [mkT3_natAdd]
      fin_cases p
      · simpa using hA
      · simpa using hB
      · simpa using hC
  have hFs' : ∀ s, SmA (I := I) (M := M) ((mkT3 v' (trip3 A' B' C')) s) := by
    intro s
    refine Fin.addCases ?_ ?_ s
    · intro i
      rw [mkT3_castAdd]
      exact hv' i
    · intro p
      rw [mkT3_natAdd]
      fin_cases p
      · simpa using hA'
      · simpa using hB'
      · simpa using hC'
  -- the two packed tuples have the same values at `x`
  have hvals : ∀ s, (mkT3 v (trip3 A B C)) s x = (mkT3 v' (trip3 A' B' C')) s x := by
    intro s
    refine Fin.addCases ?_ ?_ s
    · intro i
      rw [mkT3_castAdd, mkT3_castAdd]
      exact hvv i
    · intro p
      rw [mkT3_natAdd, mkT3_natAdd]
      fin_cases p
      · simpa using hAA
      · simpa using hBB
      · simpa using hCC
  -- the bridge to the packed iteration
  have e1 : Work.Diff.EXT.covKAExt G t k v A B C x
      = cktA G t k (mkT3 v (trip3 A B C)) x := by
    rw [cktA_mkT3_eq]
    simp only [trip3_zero, trip3_one, trip3_two]
  have e2 : Work.Diff.EXT.covKAExt G t k v' A' B' C' x
      = cktA G t k (mkT3 v' (trip3 A' B' C')) x := by
    rw [cktA_mkT3_eq]
    simp only [trip3_zero, trip3_one, trip3_two]
  rw [e1, e2]
  exact ka_val_dep_all hLC G t k x hFs hFs' hvals

end Work.Diff.EXT
