import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.TInvDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov.RicFlip

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

-- Locality (germ) step of the induction `PInv g base k → PInv g base (k+1)`, third clause.
-- Unfold `packTower g base (k+1)` with `packStep`.  For `y` near `x`:
--   * `Work.Diff.GE.mvfderiv_congr_eventuallyEq` (`Submission/Work/Diff/GE/dRmPhi.lean`) turns the
--     two `mvfderiv`s into each other, using the induction hypothesis `h`'s locality clause at `y`
--     for the tuples `F ∘ Fin.succ` and `F' ∘ Fin.succ` (the hypotheses `∀ s, F s =ᶠ[𝓝 x] F' s`
--     are converted into `∀ᶠ y in 𝓝 x, ∀ s, F s =ᶠ[𝓝 y] F' s` with
--     `Work.Diff.EXT.eventuallyEq_nhds_eventuallyA`, `Submission/Work/Diff/EXT/ATens/Defs.lean`);
--     the direction vectors are identified with `Filter.EventuallyEq.eq_of_nhds`;
--   * each summand is handled by the same locality clause at `y` applied to the updated tuples,
--     whose inserted fields are identified through `Work.Diff.EXT.dirFA_germEq`
--     (`Submission/Work/Diff/EXT/ATens/Kit.lean`); their smoothness is
--     `Work.Diff.EXT.dirFA_smooth hLC g`;
--   * assemble with `Filter.EventuallyEq` combinators (`sub`, and `Finset.sum` after
--     `Finset.sum_apply`).
-- The same computation is the PROVED `Work.Diff.EXT.ka_locAt` in
-- `Submission/Work/Diff/EXT/covKAExt_frame_eq_smoothExt.lean`, except that here all fields are
-- globally smooth (`SmE`), so no `SmLoc` machinery is needed (apply the induction hypothesis at
-- the nearby points `y`).

theorem packTower_loc
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (h : Work.Diff.EXT.ConnCov.RicFlip.PInv g base k)
    {F F' : Fin (k + 4) → (Π y : M, TangentSpace I y)}
    (hF : ∀ s, Work.Diff.EXT.ATower.SmE I M (F s))
    (hF' : ∀ s, Work.Diff.EXT.ATower.SmE I M (F' s)) (x : M)
    (heq : ∀ s, Filter.EventuallyEq (nhds x) (F s) (F' s)) :
    Filter.EventuallyEq (nhds x) (Work.Diff.EXT.ConnCov.RicFlip.packTower g base (k + 1) F)
      (Work.Diff.EXT.ConnCov.RicFlip.packTower g base (k + 1) F') := by
  -- The shifted tuples `F ∘ Fin.succ`, `F' ∘ Fin.succ` are the level-`k` tuples the induction
  -- hypothesis applies to.
  have hFs : ∀ s, Work.Diff.EXT.ATower.SmE I M
      ((fun i : Fin (k + 3) => F i.succ) s) := fun s => hF s.succ
  have hFs' : ∀ s, Work.Diff.EXT.ATower.SmE I M
      ((fun i : Fin (k + 3) => F' i.succ) s) := fun s => hF' s.succ
  have hEQ : ∀ᶠ y in 𝓝 x, ∀ j : Fin (k + 3),
      (fun i : Fin (k + 3) => F i.succ) j =ᶠ[𝓝 y] (fun i : Fin (k + 3) => F' i.succ) j := by
    rw [Filter.eventually_all]
    exact fun j => Work.Diff.EXT.eventuallyEq_nhds_eventuallyA (heq j.succ)
  have hE0 : ∀ᶠ y in 𝓝 x, F 0 =ᶠ[𝓝 y] F' 0 :=
    Work.Diff.EXT.eventuallyEq_nhds_eventuallyA (heq 0)
  -- The `mvfderiv` term.
  have hder : (fun y : M => (mvfderiv I
        (packTower g base k (fun i : Fin (k + 3) => F i.succ)) y) (F 0 y))
      =ᶠ[𝓝 x] (fun y : M => (mvfderiv I
        (packTower g base k (fun i : Fin (k + 3) => F' i.succ)) y) (F' 0 y)) := by
    filter_upwards [hEQ, hE0] with y hE hE0y
    rw [Work.Diff.GE.mvfderiv_congr_eventuallyEq
      ((h (fun i : Fin (k + 3) => F i.succ) hFs).2.2 y
        (fun i : Fin (k + 3) => F' i.succ) hFs' hE), hE0y.eq_of_nhds]
  -- The summed connection corrections.
  have hper : ∀ᶠ y in 𝓝 x, ∀ s : Fin (k + 3),
      packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) s
          (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) y
      = packTower g base k (Function.update (fun i : Fin (k + 3) => F' i.succ) s
          (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F' i.succ) s) (F' 0))) y := by
    rw [Filter.eventually_all]
    intro s
    have hS : ∀ i, Work.Diff.EXT.ATower.SmE I M
        ((Function.update (fun i : Fin (k + 3) => F i.succ) s
          (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) i) :=
      Work.Diff.EXT.smA_update hFs
        (Work.Diff.EXT.dirFA_smooth hLC g (hFs s) (hF 0))
    have hS' : ∀ i, Work.Diff.EXT.ATower.SmE I M
        ((Function.update (fun i : Fin (k + 3) => F' i.succ) s
          (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F' i.succ) s) (F' 0))) i) :=
      Work.Diff.EXT.smA_update hFs'
        (Work.Diff.EXT.dirFA_smooth hLC g (hFs' s) (hF' 0))
    have hEqu : ∀ᶠ y in 𝓝 x, ∀ i : Fin (k + 3),
        (Function.update (fun i : Fin (k + 3) => F i.succ) s
          (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) i
        =ᶠ[𝓝 y]
        (Function.update (fun i : Fin (k + 3) => F' i.succ) s
          (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F' i.succ) s) (F' 0))) i := by
      rw [Filter.eventually_all]
      intro i
      by_cases hi : i = s
      · cases hi
        rw [Function.update_self, Function.update_self]
        exact Work.Diff.EXT.eventuallyEq_nhds_eventuallyA
          (Work.Diff.EXT.dirFA_germEq g
            (Work.Diff.EXT.smLoc_of_smA (hFs s) x)
            (Work.Diff.EXT.smLoc_of_smA (hFs' s) x) (heq s.succ) (heq 0))
      · rw [Function.update_of_ne hi, Function.update_of_ne hi]
        exact Work.Diff.EXT.eventuallyEq_nhds_eventuallyA (heq i.succ)
    filter_upwards [hEqu] with y hy
    exact ((h (Function.update (fun i : Fin (k + 3) => F i.succ) s
        (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) hS).2.2 y
      (Function.update (fun i : Fin (k + 3) => F' i.succ) s
        (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F' i.succ) s) (F' 0))) hS' hy).eq_of_nhds
  have hsum : ∀ᶠ y in 𝓝 x,
      (∑ s : Fin (k + 3), packTower g base k (Function.update (fun i : Fin (k + 3) => F i.succ) s
          (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) y)
      = ∑ s : Fin (k + 3), packTower g base k
          (Function.update (fun i : Fin (k + 3) => F' i.succ) s
            (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F' i.succ) s) (F' 0))) y := by
    filter_upwards [hper] with y hy
    exact Finset.sum_congr rfl (fun s _ => hy s)
  filter_upwards [hder, hsum] with y hy1 hy2
  show (mvfderiv I (packTower g base k (fun i : Fin (k + 3) => F i.succ)) y) (F 0 y)
      - ∑ s : Fin (k + 3), packTower g base k
          (Function.update (fun i : Fin (k + 3) => F i.succ) s
            (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) y
    = (mvfderiv I (packTower g base k (fun i : Fin (k + 3) => F' i.succ)) y) (F' 0 y)
      - ∑ s : Fin (k + 3), packTower g base k
          (Function.update (fun i : Fin (k + 3) => F' i.succ) s
            (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F' i.succ) s) (F' 0))) y
  rw [hy1, hy2]

end Work.Diff.EXT.ConnCov.RicFlip
