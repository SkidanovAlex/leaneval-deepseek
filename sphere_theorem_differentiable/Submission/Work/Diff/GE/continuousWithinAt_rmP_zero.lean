import Mathlib
import Submission.Work.Diff.GE.covRmFixedEvolDefs
import Submission.Work.Diff.GE.flowContAtZero

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# Continuity at `t = 0` of a fixed-vector curvature component along a Ricci flow

`ContinuousWithinAt (fun s ↦ rmP (G s) x u b c d) (Ico 0 T) 0` for a Ricci flow `G` on `[0,T)`.

The Ricci-flow hypothesis gives joint smoothness of the family `t ↦ G t` only on the *half-open*
interval `[0,T)`; reparametrising time by `t = τ²` turns `[0,T)` into an open neighbourhood of `0`,
on which `(τ,y) ↦ rmP (G (τ²)) y (A y) (B y) (C y) (D y)` is jointly `C^∞` for smooth fields
`A,B,C,D` (`Work.Diff.GE.rmP_jointSmooth`), and the conclusion is transferred back along
`s ↦ √s` (`Work.Diff.GE.continuousWithinAt_of_continuousAt_comp_sq`).
-/

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.GE

theorem continuousWithinAt_rmP_zero
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ((⊤ : ENat) : WithTop ENat) M]
    [I.Boundaryless] [T2Space M] [CompactSpace M]
    (hLC : Submission.Diff.LCSmooth I M)
    {G : ℝ → Submission.Diff.SMet I M} {T : ℝ} (hflow : Submission.Diff.IsRicciFlow G T)
    (x : M) (u b c d : TangentSpace I x) :
    ContinuousWithinAt (fun s : ℝ ↦ Submission.Diff.rmP (G s) x u b c d) (Set.Ico 0 T) 0 := by
  by_cases hT : T ≤ 0
  · rw [Set.Ico_eq_empty_iff.mpr (not_lt.mpr hT)]
    simp [ContinuousWithinAt, nhdsWithin_empty]
  · have hTpos : 0 < T := not_le.mp hT
    set ρ : ℝ := Real.sqrt T / 2 with hρdef
    have hρ : 0 < ρ := by positivity
    have hρT : ρ ^ 2 < T := by
      rw [hρdef, div_pow, Real.sq_sqrt (le_of_lt hTpos)]
      nlinarith
    have hsq : Submission.Diff.JointSmooth (sqFlow G) (Set.Ioo (-ρ) ρ) :=
      jointSmooth_sqFlow (I := I) (M := M) hTpos hρ hρT hflow.1
    have h0 : (0 : ℝ) ∈ Set.Ioo (-ρ) ρ := ⟨by linarith, hρ⟩
    have hjoint := rmP_jointSmooth (I := I) (M := M) hLC (sqFlow G) (Set.Ioo (-ρ) ρ) isOpen_Ioo
      hsq (smoothExt x u) (smoothExt x b) (smoothExt x c) (smoothExt x d)
      (smoothExt_cmdiff x u) (smoothExt_cmdiff x b) (smoothExt_cmdiff x c)
      (smoothExt_cmdiff x d) 0 h0 x
    have hcont : ContinuousAt (fun τ : ℝ ↦ Submission.Diff.rmP (sqFlow G τ) x u b c d) 0 := by
      have hj : Work.Diff.EXT.JointSmoothAt I M
          (fun p : ℝ × M ↦ Submission.Diff.rmP (sqFlow G p.1) p.2 (smoothExt x u p.2)
            (smoothExt x b p.2) (smoothExt x c p.2) (smoothExt x d p.2)) 0 x := hjoint
      have hslice := continuousAt_of_jointSmoothAt (I := I) (M := M) hj
      simpa only [smoothExt_apply] using hslice
    refine continuousWithinAt_of_continuousAt_comp_sq hTpos hcont ?_
    intro s hs
    show Submission.Diff.rmP (G s) x u b c d
      = Submission.Diff.rmP (sqFlow G (Real.sqrt s)) x u b c d
    rw [show sqFlow G (Real.sqrt s) = G s from by
      rw [sqFlow, Real.sq_sqrt hs.1]]

end Work.Diff.GE
