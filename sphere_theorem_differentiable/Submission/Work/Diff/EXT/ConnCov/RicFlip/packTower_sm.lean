import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.TInvDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov.RicFlip

set_option maxHeartbeats 800000

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter
open Commons.Geometry.Manifold.VectorField

-- Smoothness step of the induction `PInv g base k → PInv g base (k+1)`, first clause.
-- Unfold `packTower g base (k+1) F` with `packTower_succ` (definitional) / `packStep`:
--   `fun x => mvfderiv I (packTower g base k (F ∘ Fin.succ)) x (F 0 x)
--      - ∑ j, packTower g base k (Function.update (F ∘ Fin.succ) j (dirFA g ((F ∘ Fin.succ) j) (F 0))) x`.
-- The `mvfderiv` term is `Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff` of the
-- induction hypothesis's smoothness clause at `F ∘ Fin.succ` and of `hF 0`.  Each summand is the
-- same clause of `h` at the updated tuple, whose entries are smooth by `hF` and
-- `Work.Diff.EXT.dirFA_smooth hLC g` (`Submission/Work/Diff/EXT/ATens/Defs.lean`, this is where
-- `hLC` is used).  Conclude with `ContMDiff.sum` (rewrite `∑ j, Φ j` as `fun x => ∑ j, Φ j x` with
-- `Finset.sum_apply`) and `ContMDiff.sub`.
-- The same computation is the PROVED `Work.Diff.EXT.ka_smooth` in
-- `Submission/Work/Diff/EXT/covKAExt_frame_eq_smoothExt.lean` (specialised case); copy it.

theorem packTower_sm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (h : Work.Diff.EXT.ConnCov.RicFlip.PInv g base k)
    {F : Fin (k + 4) → (Π y : M, TangentSpace I y)}
    (hF : ∀ s, Work.Diff.EXT.ATower.SmE I M (F s)) :
    Work.Diff.EXT.ATower.SmF I M (Work.Diff.EXT.ConnCov.RicFlip.packTower g base (k + 1) F) := by
  -- The shifted tuple `F ∘ Fin.succ` consists of smooth fields.
  have hG : ∀ i : Fin (k + 3), SmA (I := I) (M := M) (F i.succ) := fun i => hF i.succ
  -- Induction hypothesis: the level-`k` tower is smooth at `F ∘ Fin.succ`.
  have hΦ : CMDiff ∞ (packTower g base k (fun i : Fin (k + 3) => F i.succ)) :=
    (h (fun i : Fin (k + 3) => F i.succ) hG).1
  -- The `mvfderiv` term is smooth by `mvfderiv_apply_contMDiff`.
  have h1 : CMDiff ∞ (fun y : M =>
      (mvfderiv I (packTower g base k (fun i : Fin (k + 3) => F i.succ)) y) (F 0 y)) :=
    Commons.Geometry.Manifold.VectorField.mvfderiv_apply_contMDiff hΦ (hF 0)
  -- Each summand is the smoothness clause of `h` at the tuple with the connection term inserted;
  -- its entries are smooth by `hF` and `dirFA_smooth hLC g`.
  have h2 : ∀ s : Fin (k + 3), CMDiff ∞ (fun y : M => packTower g base k
      (Function.update (fun i : Fin (k + 3) => F i.succ) s
        (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) y) := by
    intro s
    exact (h _ (Work.Diff.EXT.smA_update hG
      (Work.Diff.EXT.dirFA_smooth hLC g (hG s) (hF 0)))).1
  -- The finite sum of the summands is smooth.
  have h3 : CMDiff ∞ (fun y : M => ∑ s : Fin (k + 3), packTower g base k
      (Function.update (fun i : Fin (k + 3) => F i.succ) s
        (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) y) :=
    ContMDiff.sum (t := Finset.univ)
      (f := fun s (y : M) => packTower g base k
        (Function.update (fun i : Fin (k + 3) => F i.succ) s
          (Work.Diff.EXT.dirFA g ((fun i : Fin (k + 3) => F i.succ) s) (F 0))) y)
      (fun s _ => h2 s)
  rw [packTower_succ]
  exact h1.sub h3

end Work.Diff.EXT.ConnCov.RicFlip
