import Mathlib
import Submission.Work.WilG4c.Defs
import Submission.Work.WilG4c.StepLipDefs
import Submission.Work.WilG4c.fderiv_cons_yDir_le_of_slice_norm
import Submission.Work.WilG4c.PullXLip

namespace Work.WilG4c

/-!
# The `PY ⟹ y`-directional bound of BNZ §5.3

The predicate `PY` (see `Submission/Work/WilG4c/Defs.lean`) only controls the derivatives of a
family member in the `y`-coordinates, at fixed distinguished coordinate `x`.  The
`§5.3` reduction (`StepLipHigh`) consumes the bound in the *joint* picture: the
`y`-directional derivative of `famFunHat (F i)` at `xPt l x y` is at most `1` in absolute
value.  This file supplies exactly that transfer.

The two ingredients are already available in the area:

* `pullX_fderiv_yDir_eq` identifies the joint `y`-directional derivative of `famFunHat f` with
  the `y`-directional derivative of `f l` at `Fin.cons x y`;
* `fderiv_cons_yDir_le_of_slice_norm` bounds the latter by the operator norm of the `C¹`
  derivative of the `y`-slice, which is the quantity controlled by `hY`.

The only extra observation is that differentiability of `famFunHat f` at `xPt l x y` implies
differentiability of `f l` at `Fin.cons x y`, since the latter is the former precomposed with
the affine inclusion `z ↦ Fin.append l z`.
-/

/-- `f l` is differentiable at `Fin.cons x y` as soon as `famFunHat f` is differentiable at
the corresponding point `xPt l x y`: the former is the latter precomposed with the affine
inclusion `z ↦ Fin.append l z`. -/
theorem differentiableAt_familyAt_of_famFunHat {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ)
    (hd : DifferentiableAt ℝ (Work.WilkG4c.famFunHat f) (Work.WilkG4c.xPt l x y)) :
    DifferentiableAt ℝ (f l) (Fin.cons x y) := by
  have h2 : DifferentiableAt ℝ (fun z : Fin (n + 1) → ℝ => Fin.append l z) (Fin.cons x y) :=
    (pullX_hasFDerivAt_finAppend p (n + 1) l (Fin.cons x y)).differentiableAt
  have hcomp : DifferentiableAt ℝ
      ((Work.WilkG4c.famFunHat f) ∘ (fun z : Fin (n + 1) → ℝ => Fin.append l z))
      (Fin.cons x y) := by
    refine hd.comp (x := Fin.cons x y) (f := fun z : Fin (n + 1) → ℝ => Fin.append l z) ?_
    exact h2
  have hfun : (Work.WilkG4c.famFunHat f) ∘ (fun z : Fin (n + 1) → ℝ => Fin.append l z)
      = f l := by
    funext z
    simp [Work.WilkG4c.famFunHat, Fin.append_left, Fin.append_right]
  rwa [hfun] at hcomp

/-- **The joint `y`-directional bound.**  If the `C¹` norm of the `y`-slice of `f l` at `x` is
at most `1` at `y`, then the `j`-th `y`-directional derivative of `famFunHat f` at `xPt l x y`
is at most `1` in absolute value. -/
theorem famFunHat_yDir_le_of_slice_norm {p n : ℕ}
    (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ) (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ)
    (hY : ‖iteratedFDeriv ℝ 1 (Work.WilkG4c.slice (f l) x) y‖ ≤ 1) (j : Fin n) :
    |fderiv ℝ (Work.WilkG4c.famFunHat f) (Work.WilkG4c.xPt l x y)
      (Pi.single (Fin.natAdd p j.succ) 1)| ≤ 1 := by
  by_cases hd : DifferentiableAt ℝ (Work.WilkG4c.famFunHat f) (Work.WilkG4c.xPt l x y)
  · have hdl : DifferentiableAt ℝ (f l) (Fin.cons x y) :=
      differentiableAt_familyAt_of_famFunHat f l x y hd
    rw [pullX_fderiv_yDir_eq f l x y j hd]
    exact fderiv_cons_yDir_le_of_slice_norm (f l) x y hdl hY j
  · rw [fderiv_zero_of_not_differentiableAt hd]
    simp

theorem SlicePrimaryLe {p n k r : ℕ} (Λ : Set (Fin p → ℝ))
    (F : Work.WilkG4c.Family k p (n + 1)) (hr : 1 ≤ r)
    (hY : ∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilkG4c.I, ∀ m, m ≤ r →
      ∀ y ∈ WilkiesDesign.openCube n,
      ‖iteratedFDeriv ℝ m (Work.WilkG4c.slice (F i l) x) y‖ ≤ 1) :
    ∀ i, ∀ l ∈ Λ, ∀ x ∈ Work.WilkG4c.I, ∀ y ∈ WilkiesDesign.openCube n, ∀ j : Fin n,
      |fderiv ℝ (Work.WilkG4c.famFunHat (F i)) (Work.WilkG4c.xPt l x y)
        (Pi.single (Fin.natAdd p j.succ) 1)| ≤ 1 := by
  intro i l hl x hx y hy j
  exact famFunHat_yDir_le_of_slice_norm (F i) l x y (hY i l hl x hx 1 hr y hy) j

end Work.WilG4c
