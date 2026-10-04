import Mathlib
import Submission.Work.Diff.EXT.ConnCov.RicFlip.TInvDefs

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.EXT.ConnCov.RicFlip

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

open LeanEval.Geometry.SphereTheorem Submission.Diff Submission.Diff.Alg
open scoped Manifold ContDiff Bundle Topology
open Bundle ContDiff Set VectorField CovariantDerivative Metric Filter

-- Linearity step of the induction `PInv g base k → PInv g base (k+1)`, in the *direction* slot `0`.
-- Unfold `packTower g base (k+1)` with `packStep`; the tuple `F ∘ Fin.succ` is unchanged
-- (`(Function.update F 0 Y) ∘ Fin.succ = F ∘ Fin.succ`, prove by `funext`/`Fin.succ_ne_zero`), so
--   * the `mvfderiv` term is linear in the direction (`ContinuousLinearMap.map_add`/`map_smul`,
--     i.e. `map_add`/`map_smul` for `mvfderiv I Φ x`),
--   * each inserted field is `dirFA g ((F ∘ Fin.succ) j) (f₁ • X₁ + f₂ • X₂)`, which is the
--     *direction* argument of `dirFA`; rewrite it with `Work.Diff.EXT.dirFA_add_dir`
--     (`Submission/Work/Diff/EXT/ATens/Defs.lean`) and close with the induction hypothesis `h`
--     at slot `j` (the smoothness of the two `dirFA`-fields is `Work.Diff.EXT.dirFA_smooth hLC g`),
--   * finish with `funext x` and `ring`.
-- The same computation is the PROVED `Work.Diff.EXT.ka_lin_dir` in
-- `Submission/Work/Diff/EXT/covKAExt_frame_eq_smoothExt.lean` (specialised case); copy it.

theorem packTower_lin_dir
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] [CompleteSpace E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I (⊤ : ℕ∞) M]
    [I.Boundaryless] [T2Space M]
    (hLC : Submission.Diff.LCSmooth I M) (g : Submission.Diff.SMet I M)
    (base : Work.Diff.EXT.ATower.Op3 (I := I) (M := M) 0) (k : ℕ)
    (h : Work.Diff.EXT.ConnCov.RicFlip.PInv g base k)
    {F : Fin (k + 4) → (Π y : M, TangentSpace I y)}
    (hF : ∀ s, Work.Diff.EXT.ATower.SmE I M (F s))
    {X₁ X₂ : Π y : M, TangentSpace I y}
    (hX₁ : Work.Diff.EXT.ATower.SmE I M X₁) (hX₂ : Work.Diff.EXT.ATower.SmE I M X₂)
    {f₁ f₂ : M → ℝ} (hf₁ : Work.Diff.EXT.ATower.SmF I M f₁) (hf₂ : Work.Diff.EXT.ATower.SmF I M f₂) :
    Work.Diff.EXT.ConnCov.RicFlip.packTower g base (k + 1)
        (Function.update F 0 (f₁ • X₁ + f₂ • X₂))
      = f₁ • Work.Diff.EXT.ConnCov.RicFlip.packTower g base (k + 1) (Function.update F 0 X₁)
        + f₂ • Work.Diff.EXT.ConnCov.RicFlip.packTower g base (k + 1) (Function.update F 0 X₂) := by
  -- The tuple of `k+3` slots below the direction slot `0` is unchanged by the update at `0`.
  have hconsPt : ∀ (Y : Π y : M, TangentSpace I y) (j : Fin (k + 3)),
      (Function.update F 0 Y) j.succ = F j.succ :=
    fun Y j => Function.update_of_ne (Fin.succ_ne_zero j) Y F
  have hconsLam : ∀ (Y : Π y : M, TangentSpace I y),
      (fun j : Fin (k + 3) => (Function.update F 0 Y) j.succ)
        = (fun j : Fin (k + 3) => F j.succ) :=
    fun Y => funext (fun j => hconsPt Y j)
  rw [packTower_succ, packTower_succ, packTower_succ]
  unfold packStep
  simp only [hconsLam, hconsPt, Function.update_self]
  funext x
  simp only [Pi.sub_apply, Pi.add_apply, Pi.smul_apply', Finset.sum_apply]
  -- The `mvfderiv` term is linear in the direction.
  have ht1 : (mvfderiv I (packTower g base k (fun j : Fin (k + 3) => F j.succ)) x)
        (f₁ x • X₁ x + f₂ x • X₂ x)
      = f₁ x • ((mvfderiv I (packTower g base k (fun j : Fin (k + 3) => F j.succ)) x) (X₁ x))
        + f₂ x • ((mvfderiv I (packTower g base k (fun j : Fin (k + 3) => F j.succ)) x) (X₂ x)) := by
    simp only [map_add, map_smul]
  -- Each inserted field is `dirFA g (slot j) (direction)`: linear in the direction by
  -- `dirFA_add_dir`, and then the induction hypothesis `h` at slot `j` applies.
  have hs : (∑ q : Fin (k + 3), packTower g base k
        (Function.update (fun j : Fin (k + 3) => F j.succ) q
          (dirFA g (F q.succ) (f₁ • X₁ + f₂ • X₂))) x)
      = f₁ x • (∑ q : Fin (k + 3), packTower g base k
            (Function.update (fun j : Fin (k + 3) => F j.succ) q (dirFA g (F q.succ) X₁)) x)
        + f₂ x • (∑ q : Fin (k + 3), packTower g base k
            (Function.update (fun j : Fin (k + 3) => F j.succ) q (dirFA g (F q.succ) X₂)) x) := by
    rw [Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl (fun q _ => ?_)
    rw [dirFA_add_dir]
    have hq := (h (fun j : Fin (k + 3) => F j.succ) (fun j => hF j.succ)).2.1 q
      (dirFA g (F q.succ) X₁) (dirFA g (F q.succ) X₂) f₁ f₂
      (dirFA_smooth hLC g (hF q.succ) hX₁) (dirFA_smooth hLC g (hF q.succ) hX₂) hf₁ hf₂
    rw [hq]
    simp only [Pi.add_apply, Pi.smul_apply']
  rw [ht1, hs]
  simp only [smul_sub, smul_eq_mul]
  ring

end Work.Diff.EXT.ConnCov.RicFlip
