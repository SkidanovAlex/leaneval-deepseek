import Mathlib
import Submission.Work.WilG4c.Defs

set_option autoImplicit false
noncomputable section

namespace Work.WilG4c

open Work.WilkG4c

/-! ## Auxiliary material: the affine inclusion `y ↦ pt x y = Fin.cons x y`

The two facts used below are that this inclusion is affine with linear part `incl n`
(`v ↦ Fin.cons 0 v`), and that `incl n` sends the `j`-th coordinate direction to the
`j.succ`-th coordinate direction.  From these the chain rule gives the equality between the
`j.succ`-directional derivative of `g` at `pt x y` and the `j`-directional derivative of the
slice `slice g x` at `y`, from which the bound is immediate. -/

/-- The continuous linear map `v ↦ Fin.cons 0 v : ℝⁿ → ℝⁿ⁺¹`.  It is the linear part of the
affine inclusion `y ↦ pt x y`, i.e. the derivative of that inclusion. -/
private def incl (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi
    (fun j : Fin (n + 1) => Fin.cases (0 : (Fin n → ℝ) →L[ℝ] ℝ)
      (fun i : Fin n => ContinuousLinearMap.proj i) j)

private lemma incl_apply (n : ℕ) (v : Fin n → ℝ) : incl n v = Fin.cons (0 : ℝ) v := by
  funext j
  induction j using Fin.cases with
  | zero => simp [incl]
  | succ i => simp [incl]

/-- The inclusion of `ℝⁿ` into `ℝⁿ⁺¹` as `y ↦ pt x y` carries the `i`-th coordinate direction
to the `(i+1)`-st coordinate direction. -/
private lemma incl_single {n : ℕ} (i : Fin n) :
    incl n (Pi.single i (1 : ℝ)) = (Pi.single i.succ (1 : ℝ) : Fin (n + 1) → ℝ) := by
  rw [incl_apply]
  funext j
  induction j using Fin.cases with
  | zero => simp
  | succ k =>
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun hh => h (Fin.succ_injective n hh))]

/-- The map `y ↦ pt x y = Fin.cons x y` is affine with linear part `incl n`. -/
private lemma hasFDerivAt_pt (n : ℕ) (x : ℝ) (y : Fin n → ℝ) :
    HasFDerivAt (fun w : Fin n → ℝ => pt x w) (incl n) y := by
  have hfun : (fun w : Fin n → ℝ => pt x w)
      = (fun w : Fin n → ℝ =>
          (Fin.cons x (0 : Fin n → ℝ) : Fin (n + 1) → ℝ) + incl n w) := by
    funext w
    rw [pt, incl_apply]
    funext j
    induction j using Fin.cases with
    | zero => simp
    | succ i => simp
  rw [hfun]
  exact (incl n).hasFDerivAt.const_add _

/-- **A `y`-directional derivative of `g` is a directional derivative of its slice.**
The chain rule for `slice g x = g ∘ (pt x ·)` together with the identification of the
coordinate directions under the affine inclusion. -/
theorem fderiv_cons_yDir_eq_slice_fderiv {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ)
    (x : ℝ) (y : Fin n → ℝ) (hd : DifferentiableAt ℝ g (Fin.cons x y)) (j : Fin n) :
    fderiv ℝ (Work.WilkG4c.slice g x) y (Pi.single j (1 : ℝ))
      = fderiv ℝ g (Fin.cons x y) (Pi.single j.succ 1) := by
  have hpt : HasFDerivAt (fun w : Fin n → ℝ => pt x w) (incl n) y := hasFDerivAt_pt n x y
  have hcomp : fderiv ℝ (Work.WilkG4c.slice g x) y = (fderiv ℝ g (pt x y)).comp (incl n) := by
    have h := fderiv_fun_comp (x := y) (f := fun w : Fin n → ℝ => pt x w) (g := g)
      hd hpt.differentiableAt
    rw [hpt.fderiv] at h
    exact h
  have h := congrArg (fun (L : (Fin n → ℝ) →L[ℝ] ℝ) => L (Pi.single j (1 : ℝ))) hcomp
  rw [ContinuousLinearMap.comp_apply, incl_single] at h
  exact h

theorem fderiv_cons_yDir_le_of_slice_norm {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ)
    (x : ℝ) (y : Fin n → ℝ) (hd : DifferentiableAt ℝ g (Fin.cons x y))
    (hY : ‖iteratedFDeriv ℝ 1 (Work.WilkG4c.slice g x) y‖ ≤ 1) (j : Fin n) :
    |fderiv ℝ g (Fin.cons x y) (Pi.single j.succ 1)| ≤ 1 := by
  rw [← fderiv_cons_yDir_eq_slice_fderiv g x y hd j]
  calc |fderiv ℝ (Work.WilkG4c.slice g x) y (Pi.single j (1 : ℝ))|
      = ‖fderiv ℝ (Work.WilkG4c.slice g x) y (Pi.single j (1 : ℝ))‖ :=
        (Real.norm_eq_abs _).symm
    _ ≤ ‖fderiv ℝ (Work.WilkG4c.slice g x) y‖ * ‖(Pi.single j (1 : ℝ) : Fin n → ℝ)‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ = ‖iteratedFDeriv ℝ 1 (Work.WilkG4c.slice g x) y‖ * 1 := by
        rw [← norm_iteratedFDeriv_one (f := Work.WilkG4c.slice g x), Pi.norm_single, norm_one]
    _ = ‖iteratedFDeriv ℝ 1 (Work.WilkG4c.slice g x) y‖ := mul_one _
    _ ≤ 1 := hY

end Work.WilG4c
