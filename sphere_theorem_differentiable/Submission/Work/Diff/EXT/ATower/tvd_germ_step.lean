import Mathlib
import Submission.Work.Diff.EXT.ATower.tower_value_defs
import Submission.Work.Diff.EXT.covK_germ
import Submission.Work.Diff.GE.dRmPhi

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ATower

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

/-! ### Hints for the prover (supplied piece of `Work.Diff.EXT.ATower.tower_value_dep`)

This is a direct adaptation of `Work.Diff.EXT.covKRmExt_congr_germ` in
`Submission/Work/Diff/EXT/covK_germ.lean` (read it: the same induction, with three value slots
instead of four, on the packed `tvdP` recursion).  Import
`Submission.Work.Diff.EXT.covK_germ` (it provides `Work.Diff.EXT.lcOf_congr_germ`,
`Work.Diff.EXT.dirF_congr_germ`, `Work.Diff.EXT.update_congr_germ`,
`Work.Diff.EXT.germ_nhds_eventually`) and `Submission.Work.Diff.GE.dRmPhi`
(`Work.Diff.GE.mvfderiv_congr_eventuallyEq`).

Plan: unfold `tvdP g base (k+1) F` by `Work.Diff.EXT.ATower.tvdP_succ` and `tvdStepP`.
* the `mvfderiv` term: `tvdP k (F ∘ Fin.succ)` is eventually equal to `tvdP k (F' ∘ Fin.succ)` near
  `x` by the induction hypothesis applied at every nearby point (the germ hypotheses are hereditary:
  `germ_nhds_eventually`); then `Work.Diff.GE.mvfderiv_congr_eventuallyEq` and
  `(h 0).eq_of_nhds` for the direction;
* each correction term: apply the induction hypothesis to the tuple
  `Function.update (F ∘ Fin.succ) j (fun y => lcOf g (F (Fin.succ j)) y (F 0 y))` and its primed
  analogue; germ-equality of the inserted fields is `dirF_congr_germ` and of the tuples
  `update_congr_germ`.
No smoothness hypothesis is needed anywhere, and `germ_nhds_eventually` (already proved in
`covK_germ.lean`) is the tool that turns an eventual equality at `x` into an eventual equality at
every nearby point.
-/
theorem tvd_germ_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (g : Submission.Diff.SMet I M) (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (hG : Work.Diff.EXT.ATower.tvdGermT (I := I) (M := M) g base k) :
    Work.Diff.EXT.ATower.tvdGermT (I := I) (M := M) g base (k + 1) := by
  intro F F' x h
  -- the `Fin.succ`-shifted tuples, germ-equal at `x`
  have hsucc : ∀ j : Fin (k + 3), (fun i : Fin (k + 3) => F (Fin.succ i)) j
      =ᶠ[𝓝 x] (fun i : Fin (k + 3) => F' (Fin.succ i)) j :=
    fun j => h (Fin.succ j)
  -- hence at every nearby point (germ hypotheses are hereditary)
  have hFF : ∀ᶠ y in 𝓝 x, ∀ j : Fin (k + 3),
      (fun i : Fin (k + 3) => F (Fin.succ i)) j =ᶠ[𝓝 y]
        (fun i : Fin (k + 3) => F' (Fin.succ i)) j :=
    Filter.eventually_all.mpr (fun j => germ_nhds_eventually (hsucc j))
  -- the level-`k` packed tower is eventually equal near `x`
  have hlev : tvdP g base k (fun i : Fin (k + 3) => F (Fin.succ i))
      =ᶠ[𝓝 x] tvdP g base k (fun i : Fin (k + 3) => F' (Fin.succ i)) := by
    filter_upwards [hFF] with y hy
    exact hG (fun i : Fin (k + 3) => F (Fin.succ i))
      (fun i : Fin (k + 3) => F' (Fin.succ i)) y hy
  -- the `mvfderiv` term
  have hter : (mvfderiv I (tvdP g base k (fun i : Fin (k + 3) => F (Fin.succ i))) x) (F 0 x)
      = (mvfderiv I (tvdP g base k (fun i : Fin (k + 3) => F' (Fin.succ i))) x) (F' 0 x) := by
    rw [Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I) hlev, (h 0).eq_of_nhds]
  -- each correction term
  have hsum : (∑ j : Fin (k + 3), tvdP g base k
        (Function.update (fun i : Fin (k + 3) => F (Fin.succ i)) j
          (fun y => lcOf g (F (Fin.succ j)) y (F 0 y))) x)
      = (∑ j : Fin (k + 3), tvdP g base k
        (Function.update (fun i : Fin (k + 3) => F' (Fin.succ i)) j
          (fun y => lcOf g (F' (Fin.succ j)) y (F' 0 y))) x) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    exact hG _ _ x (update_congr_germ hsucc (dirF_congr_germ g (h (Fin.succ j)) (h 0)))
  rw [tvdP_succ, tvdP_succ]
  simp only [tvdStepP]
  rw [hter, hsum]

end Work.Diff.EXT.ATower
