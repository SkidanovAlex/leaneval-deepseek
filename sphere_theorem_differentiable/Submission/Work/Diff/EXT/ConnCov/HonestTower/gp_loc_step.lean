import Mathlib
import Submission.Work.Diff.EXT.ConnCov.HonestTower.Kit

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

set_option linter.unusedSectionVars false
set_option maxHeartbeats 1200000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology BigOperators
open Bundle ContDiff Set VectorField CovariantDerivative Metric
open Commons.Geometry.Manifold.VectorField

namespace Work.Diff.EXT.ConnCov.HonestTower

variable
  {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]

/-- **Locality step** of the induction for the packed honest tower (the analogue of
`Work.Diff.EXT.ckt_loc_step`). -/
theorem gp_loc_step (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (hih : TensPropG (I := I) (M := M) g base k)
    {F F' : Fin (k + 3) → Tf (I := I) (M := M)}
    (hF : ∀ s, Sm (I := I) (M := M) (F s))
    (hF' : ∀ s, Sm (I := I) (M := M) (F' s)) {x : M}
    (h : ∀ s, F s =ᶠ[𝓝 x] F' s) :
    gP g base (k + 1) F =ᶠ[𝓝 x] gP g base (k + 1) F' := by
  have hGs : ∀ i : Fin (k + 2),
      Sm (I := I) (M := M) ((fun i : Fin (k + 2) => F i.succ) i) := fun i => hF i.succ
  have hG's : ∀ i : Fin (k + 2),
      Sm (I := I) (M := M) ((fun i : Fin (k + 2) => F' i.succ) i) := fun i => hF' i.succ
  have hGloc : ∀ᶠ y in 𝓝 x, ∀ i : Fin (k + 2),
      (fun i : Fin (k + 2) => F i.succ) i =ᶠ[𝓝 y] (fun i : Fin (k + 2) => F' i.succ) i := by
    rw [Filter.eventually_all]
    exact fun i => eventuallyEq_nhds_eventuallyA (h i.succ)
  have h0loc : ∀ᶠ y in 𝓝 x, F 0 =ᶠ[𝓝 y] F' 0 := eventuallyEq_nhds_eventuallyA (h 0)
  have hder : (fun z : M =>
        (mvfderiv I (fun z : M => gP g base k (fun i : Fin (k + 2) => F i.succ) z) z)
          (F 0 z))
      =ᶠ[𝓝 x] (fun z : M =>
        (mvfderiv I (fun z : M => gP g base k (fun i : Fin (k + 2) => F' i.succ) z) z)
          (F' 0 z)) := by
    filter_upwards [hGloc, h0loc] with y hyG hy0
    rw [Work.Diff.GE.mvfderiv_congr_eventuallyEq
        ((hih (fun i : Fin (k + 2) => F i.succ) hGs).2.2 y
          (fun i : Fin (k + 2) => F' i.succ) hG's hyG), hy0.eq_of_nhds]
  have hsum : (∑ q : Fin (k + 2), gP g base k
        (Function.update (fun i : Fin (k + 2) => F i.succ) q
          (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => F i.succ) q) (F 0))))
      =ᶠ[𝓝 x] (∑ q : Fin (k + 2), gP g base k
        (Function.update (fun i : Fin (k + 2) => F' i.succ) q
          (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => F' i.succ) q) (F' 0)))) := by
    filter_upwards [hGloc, h0loc] with y hyG hy0
    rw [Finset.sum_apply, Finset.sum_apply]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    have hdq : Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => F i.succ) q) (F 0)
        =ᶠ[𝓝 y] Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => F' i.succ) q) (F' 0) :=
      Work.Diff.EXT.dirFA_eventuallyEq (g := g) (hGs q) (hG's q) (hyG q) hy0
    have hgerm : ∀ s : Fin (k + 2),
        (Function.update (fun i : Fin (k + 2) => F i.succ) q
          (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => F i.succ) q) (F 0))) s
        =ᶠ[𝓝 y] (Function.update (fun i : Fin (k + 2) => F' i.succ) q
          (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => F' i.succ) q) (F' 0))) s := by
      intro s
      rcases eq_or_ne s q with hs | hs
      · subst hs; rw [Function.update_self, Function.update_self]; exact hdq
      · rw [Function.update_of_ne hs, Function.update_of_ne hs]; exact hyG s
    exact ((hih (Function.update (fun i : Fin (k + 2) => F i.succ) q
          (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => F i.succ) q) (F 0)))
        (sm_update hGs (Work.Diff.EXT.dirFA_smooth hLC g (hGs q) (hF 0)))).2.2 y
      (Function.update (fun i : Fin (k + 2) => F' i.succ) q
          (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 2) => F' i.succ) q) (F' 0)))
        (sm_update hG's (Work.Diff.EXT.dirFA_smooth hLC g (hG's q) (hF' 0))) hgerm).eq_of_nhds
  rw [gP_succ, gP_succ]
  exact hder.sub hsum

end Work.Diff.EXT.ConnCov.HonestTower
