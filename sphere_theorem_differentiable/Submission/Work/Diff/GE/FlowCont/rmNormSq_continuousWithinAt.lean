import Mathlib
import Submission.Work.Diff.GE.continuous_flow_quantities

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity of the curvature norm along a Ricci flow

`Work.Diff.GE.cfq_continuousWithinAt_rmNormSq_zero` gives the continuity of
`s ↦ |Rm(G s)|²(x)` within `[0,T)` at the *left endpoint* `0`.  The FIX chain
(`Submission/Work/Diff/GE/covRm_fixed_evol_interior.lean`, and the product rule
`Submission/Work/Diff/GE/rmP4_update_hasDerivWithinAt.lean`) needs the same continuity at *every*
`t ∈ [0,T)` (hypothesis `hNormCont`).  At an interior point this follows from the joint smoothness
of `(s,y) ↦ |Rm(G s)|²(y)` (`Work.Diff.GE.cfq_rmNormSq_jointSmoothAt`), which is why that
statement is available in the pointwise (`JointSmoothAt`) form.
-/

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1600000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

namespace Work.Diff.GE.FlowCont

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]

/-- **Continuity of `s ↦ |Rm(G s)|²(x)` within `[0,T)` at every `t ∈ [0,T)`.**  This is the
hypothesis `hNormCont` of the FIX chain. -/
theorem rmNormSq_continuousWithinAt [I.Boundaryless] [T2Space M]
    (hLC : LCSmooth I M) {G : ℝ → SMet I M} {T : ℝ} (hflow : IsRicciFlow G T)
    {t : ℝ} (ht : t ∈ Set.Ico 0 T) (x : M) :
    ContinuousWithinAt (fun s ↦ rmNormSq (G s) x) (Set.Ico 0 T) t := by
  rcases eq_or_lt_of_le ht.1 with h0 | hpos
  · subst h0
    exact cfq_continuousWithinAt_rmNormSq_zero (I := I) hLC hflow x
  · -- interior point: joint smoothness of `(s,y) ↦ |Rm(G s)|²(y)` on the open interval
    have hGJ : JointSmooth G (Set.Ioo (0 : ℝ) T) := by
      have h := hflow.1
      rw [JointSmooth] at h ⊢
      exact h.mono (Set.prod_mono Set.Ioo_subset_Ico_self (Set.Subset.refl _))
    have hjs : Work.Diff.EXT.JointSmoothAt I M
        (fun p : ℝ × M ↦ rmNormSq (G p.1) p.2) t x :=
      cfq_rmNormSq_jointSmoothAt (I := I) hLC isOpen_Ioo hGJ ⟨hpos, ht.2⟩ x
    have hcont : ContinuousAt (fun s : ℝ ↦ rmNormSq (G s) x) t :=
      cfq_continuousAt_of_jointSmoothAt (I := I) hjs
    exact hcont.continuousWithinAt

end Work.Diff.GE.FlowCont
