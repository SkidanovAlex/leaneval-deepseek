import Mathlib
import Submission.Work.WilG4c.Defs

namespace Work.WilG4c

/-- The `x`-slice of the `m`-jet of a function that is `C^m` at `pt x y`, evaluated on a fixed
tuple of coordinate directions, varies continuously in `x`. -/
lemma continuousAt_pt_jet {n m : ℕ} {G : (Fin (n + 1) → ℝ) → ℝ} {v : Fin m → Fin (n + 1)}
    {y : Fin n → ℝ} {x : ℝ} (hG : ContDiffAt ℝ m G (Work.WilkG4c.pt x y)) :
    ContinuousAt (fun x' : ℝ =>
      iteratedFDeriv ℝ m G (Work.WilkG4c.pt x' y) (fun k => Pi.single (v k) 1)) x := by
  -- The affine slice `x' ↦ pt x' y` is continuous.
  have hpt : ContinuousAt (fun x' : ℝ => Work.WilkG4c.pt x' y) x := by
    apply Continuous.continuousAt
    rw [continuous_pi_iff]
    intro i
    induction i using Fin.cases with
    | zero => exact continuous_id
    | succ j => exact continuous_const
  -- The whole `m`-jet is continuous at `pt x y`, because `G` is `C^m` there.
  have hderiv : ContinuousAt (iteratedFDeriv ℝ m G) (Work.WilkG4c.pt x y) :=
    hG.continuousAt_iteratedFDeriv le_rfl
  have hcomp : ContinuousAt (fun x' : ℝ => iteratedFDeriv ℝ m G (Work.WilkG4c.pt x' y)) x :=
    ContinuousAt.comp (f := fun x' : ℝ => Work.WilkG4c.pt x' y) (x := x)
      (g := iteratedFDeriv ℝ m G) hderiv hpt
  -- Evaluation of a continuous multilinear map at a fixed tuple is continuous linear.
  have hc : ContinuousAt (fun _ : ℝ =>
      ContinuousMultilinearMap.apply ℝ (fun _ : Fin m => Fin (n + 1) → ℝ) ℝ
        (fun k => Pi.single (v k) 1)) x := continuousAt_const
  have h2 := hc.clm_apply hcomp
  simpa only [ContinuousMultilinearMap.apply_apply] using h2

end Work.WilG4c
