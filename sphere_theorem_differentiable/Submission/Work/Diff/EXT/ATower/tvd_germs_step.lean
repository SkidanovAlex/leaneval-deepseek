import Mathlib
import Submission.Work.Diff.EXT.ATower.tower_value_defs
import Submission.Work.Diff.EXT.ATower.connDiff_flip_input
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

`Work.Diff.EXT.ATower.tvdGermTs g base k` is the germ-locality of the packed tower restricted to
tuples of `SmE`(*) fields (all slots smooth).  This restriction is essential: the `k = 0` case is
`base`'s germ-locality for *smooth* tuples, which is what value-dependence of `base` (hypothesis
`hvd` of the target, for smooth fields only) supplies; the unconditional statement
`Work.Diff.EXT.ATower.tvdGermT` is **false** for a general `base` (the values of `base` on
non-smooth fields are unconstrained).  The `k = 0` case is supplied separately by the requester, so
only the induction step is asked for here.

Import `Submission.Work.Diff.EXT.covK_germ` (providing `Work.Diff.EXT.lcOf_congr_germ`,
`Work.Diff.EXT.dirF_congr_germ`, `Work.Diff.EXT.update_congr_germ`,
`Work.Diff.EXT.germ_nhds_eventually`) and `Submission.Work.Diff.GE.dRmPhi`
(`Work.Diff.GE.mvfderiv_congr_eventuallyEq`), and
`Submission.Work.Diff.EXT.ATower.connDiff_flip_input`
(`Work.Diff.EXT.ATower.lcOf_apply_smE` for the smoothness of `y ↦ lcOf g Y y (Z y)`).

(*) `SmE I M X` is `ContMDiff ∞ (T% X)`; closure under sums/products of smooth fields is in
`tower_value_defs.lean` (`tvd_smE_add`, `tvd_smE_sub`, `tvd_smE_smul`, `tvd_smE_sum`,
`tvd_smF_sum`, `tvd_smF_mul`).

The proof is the same induction as `Work.Diff.EXT.covKRmExt_congr_germ` in
`Submission/Work/Diff/EXT/covK_germ.lean` (and as the already-proved unconditional
`Work.Diff.EXT.ATower.tvd_germ_step`), with the `SmE` hypotheses carried along so that the induction
hypothesis can be applied to the tuples with the inserted fields
`fun y => lcOf g (F (Fin.succ j)) y (F 0 y)` (smooth by `lcOf_apply_smE`).  Unfold one step via
`Work.Diff.EXT.ATower.tvdP_succ`; the `mvfderiv` term uses
`Work.Diff.GE.mvfderiv_congr_eventuallyEq` (the level-`k` function is eventually equal near `x` by
the induction hypothesis applied at every nearby point, using `germ_nhds_eventually`), the
direction uses `(h 0).eq_of_nhds`, and each correction term uses the induction hypothesis together
with `dirF_congr_germ` and `update_congr_germ`.
-/
theorem tvd_germs_step
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (hG : Work.Diff.EXT.ATower.tvdGermTs (I := I) (M := M) g base k) :
    Work.Diff.EXT.ATower.tvdGermTs (I := I) (M := M) g base (k + 1) := by
  intro F F' x hF hF' h
  -- smoothness of the `Fin.succ`-shifted tuples
  have hFSm : ∀ j : Fin (k + 3), SmE I M ((fun i : Fin (k + 3) => F (Fin.succ i)) j) :=
    fun j => hF (Fin.succ j)
  have hF'Sm : ∀ j : Fin (k + 3), SmE I M ((fun i : Fin (k + 3) => F' (Fin.succ i)) j) :=
    fun j => hF' (Fin.succ j)
  -- the germ equalities of the shifted tuples, at `x` and at every nearby point
  have hsucc : ∀ j : Fin (k + 3), (fun i : Fin (k + 3) => F (Fin.succ i)) j
      =ᶠ[𝓝 x] (fun i : Fin (k + 3) => F' (Fin.succ i)) j :=
    fun j => h (Fin.succ j)
  have hFF : ∀ᶠ y in 𝓝 x, ∀ j : Fin (k + 3),
      (fun i : Fin (k + 3) => F (Fin.succ i)) j =ᶠ[𝓝 y]
        (fun i : Fin (k + 3) => F' (Fin.succ i)) j :=
    Filter.eventually_all.mpr (fun j => germ_nhds_eventually (hsucc j))
  -- the level-`k` packed tower is eventually equal near `x` (induction hypothesis at nearby points)
  have hlev : tvdP g base k (fun i : Fin (k + 3) => F (Fin.succ i))
      =ᶠ[𝓝 x] tvdP g base k (fun i : Fin (k + 3) => F' (Fin.succ i)) := by
    filter_upwards [hFF] with y hy
    exact hG _ _ y hFSm hF'Sm hy
  -- the `mvfderiv` term
  have hter : (mvfderiv I (tvdP g base k (fun i : Fin (k + 3) => F (Fin.succ i))) x) (F 0 x)
      = (mvfderiv I (tvdP g base k (fun i : Fin (k + 3) => F' (Fin.succ i))) x) (F' 0 x) := by
    rw [Work.Diff.GE.mvfderiv_congr_eventuallyEq (I := I) hlev, (h 0).eq_of_nhds]
  -- smoothness of the inserted fields
  have hins : ∀ j : Fin (k + 3),
      SmE I M (fun y : M => lcOf g (F (Fin.succ j)) y (F 0 y)) :=
    fun j => lcOf_apply_smE hLC g (F (Fin.succ j)) (F 0) (hF (Fin.succ j)) (hF 0)
  have hins' : ∀ j : Fin (k + 3),
      SmE I M (fun y : M => lcOf g (F' (Fin.succ j)) y (F' 0 y)) :=
    fun j => lcOf_apply_smE hLC g (F' (Fin.succ j)) (F' 0) (hF' (Fin.succ j)) (hF' 0)
  -- each correction term: the induction hypothesis applied to the tuple with the inserted field
  have hsum : (∑ j : Fin (k + 3), tvdP g base k
        (Function.update (fun i : Fin (k + 3) => F (Fin.succ i)) j
          (fun y => lcOf g (F (Fin.succ j)) y (F 0 y))) x)
      = (∑ j : Fin (k + 3), tvdP g base k
        (Function.update (fun i : Fin (k + 3) => F' (Fin.succ i)) j
          (fun y => lcOf g (F' (Fin.succ j)) y (F' 0 y))) x) := by
    refine Finset.sum_congr rfl (fun j _ => ?_)
    refine hG _ _ x (fun i => ?_) (fun i => ?_)
      (update_congr_germ hsucc (dirF_congr_germ g (h (Fin.succ j)) (h 0)))
    · rcases eq_or_ne i j with heq | hij
      · rw [heq, Function.update_self]; exact hins j
      · rw [Function.update_of_ne hij]; exact hFSm i
    · rcases eq_or_ne i j with heq | hij
      · rw [heq, Function.update_self]; exact hins' j
      · rw [Function.update_of_ne hij]; exact hF'Sm i
  rw [tvdP_succ, tvdP_succ]
  simp only [tvdStepP]
  rw [hter, hsum]

end Work.Diff.EXT.ATower
