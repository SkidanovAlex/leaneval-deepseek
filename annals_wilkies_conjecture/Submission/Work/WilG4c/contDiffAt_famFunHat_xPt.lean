import Mathlib
import Submission.Work.WilG4c.StepHigherDefs
import Submission.Work.WilG4c.LipDefs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilkG4c

/-- Smoothness of a family member from smoothness of `famFunHat`.

`famFunHat f` reads a point of `ℝ^{p + (n+1)}` as `(l, z)` (first `p` coordinates the
parameter, last `n+1` the cube point).  Fixing the parameter `l` amounts to restricting
`famFunHat f` to the image of the affine embedding `z ↦ Fin.append l z`, whose linear part
`z ↦ Fin.append 0 z` is a continuous linear map; smoothness descends along it. -/
theorem contDiffAt_famFunHat_xPt {p n m : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ)
    (h : ContDiffAt ℝ m (Work.WilkG4c.famFunHat f) (Work.WilkG4c.xPt l x y)) :
    ContDiffAt ℝ m (f l) (Work.WilkG4c.pt x y) := by
  -- The linear map `z ↦ Fin.append 0 z`.
  let L : (Fin (n + 1) → ℝ) →ₗ[ℝ] (Fin (p + (n + 1)) → ℝ) :=
    { toFun := fun z => Fin.append (0 : Fin p → ℝ) z
      map_add' := by
        intro a b
        funext i
        induction i using Fin.addCases <;>
          simp [Fin.append_left, Fin.append_right, Pi.add_apply]
      map_smul' := by
        intro c a
        funext i
        induction i using Fin.addCases <;>
          simp [Fin.append_left, Fin.append_right, Pi.smul_apply] }
  -- Its continuous version, available as the source is finite dimensional.
  let T : (Fin (n + 1) → ℝ) →L[ℝ] (Fin (p + (n + 1)) → ℝ) :=
    LinearMap.toContinuousLinearMap L
  have hT : ∀ z : Fin (n + 1) → ℝ, T z = Fin.append (0 : Fin p → ℝ) z := fun _ => rfl
  -- `z ↦ Fin.append l z` is `z ↦ T z` plus the constant `Fin.append l 0`.
  have key : ∀ z : Fin (n + 1) → ℝ,
      Fin.append l z = Fin.append l (0 : Fin (n + 1) → ℝ) + T z := by
    intro z
    rw [hT z]
    ext i
    induction i using Fin.addCases <;>
      simp [Fin.append_left, Fin.append_right, Pi.add_apply]
  -- hence it is smooth
  have hlin : ContDiffAt ℝ m (fun z : Fin (n + 1) → ℝ => Fin.append l z) (Fin.cons x y) := by
    have hc : ContDiffAt ℝ m
        (fun _ : Fin (n + 1) → ℝ => Fin.append l (0 : Fin (n + 1) → ℝ)) (Fin.cons x y) :=
      contDiffAt_const
    have hTdiff : ContDiffAt ℝ m (fun z : Fin (n + 1) → ℝ => T z) (Fin.cons x y) :=
      (ContinuousLinearMap.contDiff T).contDiffAt
    refine (hc.add hTdiff).congr_of_eventuallyEq ?_
    exact Filter.Eventually.of_forall (fun z => key z)
  -- and composing with `famFunHat f` gives the family member in the parameter `l`
  have hcomp := ContDiffAt.comp (Fin.cons x y : Fin (n + 1) → ℝ) h hlin
  have hfun : (Work.WilkG4c.famFunHat f ∘ Fin.append l) = f l := by
    funext z
    simp [Work.WilkG4c.famFunHat, Fin.append_left, Fin.append_right]
  rwa [hfun] at hcomp

end Work.WilkG4c

/-! ## The same statement under the module-path namespace

The module is `Submission.Work.WilG4c.contDiffAt_famFunHat_xPt`, so by the workspace convention
(`Submission.Work.X.Y` ↔ namespace `Work.X`) the lemma is referred to as
`Work.WilG4c.contDiffAt_famFunHat_xPt`.  The same statement is therefore made available under
that name as well; it is the same lemma, proved once above. -/

namespace Work.WilG4c

/-- Smoothness of a family member from smoothness of `famFunHat`; see
`Work.WilkG4c.contDiffAt_famFunHat_xPt`. -/
theorem contDiffAt_famFunHat_xPt {p n m : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ)
    (h : ContDiffAt ℝ m (Work.WilkG4c.famFunHat f) (Work.WilkG4c.xPt l x y)) :
    ContDiffAt ℝ m (f l) (Work.WilkG4c.pt x y) :=
  Work.WilkG4c.contDiffAt_famFunHat_xPt f l x y h

end Work.WilG4c
