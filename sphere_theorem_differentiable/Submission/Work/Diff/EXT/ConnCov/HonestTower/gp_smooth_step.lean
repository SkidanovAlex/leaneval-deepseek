import Mathlib
import Submission.Work.Diff.EXT.ConnCov.HonestTower.Kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric

namespace Work.Diff.EXT.ConnCov.HonestTower

theorem gp_smooth_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (hih : Work.Diff.EXT.ConnCov.HonestTower.TensPropG (I := I) (M := M) g base k)
    {F : Fin (k + 3) → Work.Diff.EXT.ConnCov.HonestTower.Tf (I := I) (M := M)}
    (hF : ∀ s, Work.Diff.EXT.ConnCov.HonestTower.Sm (I := I) (M := M) (F s)) :
    Work.Diff.EXT.ATower.SmF I M
      (fun y : M => Work.Diff.EXT.ConnCov.HonestTower.gP g base (k + 1) F y) := by
  have hG : ∀ i : Fin (k + 2),
      Sm (I := I) (M := M) ((fun i : Fin (k + 2) => F i.succ) i) := fun i => hF i.succ
  have hΦ : CMDiff ∞ (fun y : M => gP g base k (fun i : Fin (k + 2) => F i.succ) y) :=
    (hih (fun i : Fin (k + 2) => F i.succ) hG).1
  have h1 : CMDiff ∞ (fun y : M =>
      (mvfderiv I (fun y : M => gP g base k (fun i : Fin (k + 2) => F i.succ) y) y) (F 0 y)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hΦ (hF 0)
  have h2 : ∀ s : Fin (k + 2), CMDiff ∞ (fun y : M => gP g base k
      (Function.update (fun i : Fin (k + 2) => F i.succ) s
        (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => F i.succ) s) (F 0))) y) := by
    intro s
    exact (hih _ (sm_update hG
      (Work.Diff.EXT.dirFA_smooth hLC g (hG s) (hF 0)))).1
  have h3' : CMDiff ∞ (fun y : M => ∑ s : Fin (k + 2), gP g base k
      (Function.update (fun i : Fin (k + 2) => F i.succ) s
        (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => F i.succ) s) (F 0))) y) :=
    ContMDiff.sum (t := Finset.univ) (fun s _ => h2 s)
  have h3 : CMDiff ∞ (∑ s : Fin (k + 2), gP g base k
      (Function.update (fun i : Fin (k + 2) => F i.succ) s
        (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => F i.succ) s) (F 0)))) := by
    have hfun : (∑ s : Fin (k + 2), gP g base k
        (Function.update (fun i : Fin (k + 2) => F i.succ) s
          (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => F i.succ) s) (F 0))))
        = fun y : M => ∑ s : Fin (k + 2), gP g base k
          (Function.update (fun i : Fin (k + 2) => F i.succ) s
            (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => F i.succ) s) (F 0))) y := by
      funext y; rw [Finset.sum_apply]
    rw [hfun]; exact h3'
  rw [gP_succ]
  exact h1.sub h3

end Work.Diff.EXT.ConnCov.HonestTower
