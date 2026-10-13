import Mathlib
import Submission.Work.WilG4c.LipDefs
import Submission.Work.WilG4c.PullXLip
import Submission.Work.WilG4c.LipOnCubeOfBound
import Submission.Work.WilG4c.norm_iteratedFDeriv_le_of_dirs

set_option autoImplicit false
noncomputable section
open Classical

namespace Work.WilG4c

open WilkiesDesign
open Work.WilkG4c

/-! ## The linear part of the inclusion `y ↦ xPt l x y`

The point `xPt l x y` of `ℝ^{p + (n+1)}` is `Fin.append l (Fin.cons x y)`.  We show that
`y ↦ xPt l x y` is affine, with linear part `appCLM p n ∘L inclY n`, where `inclY n` is the
inclusion `v ↦ Fin.cons 0 v : ℝⁿ → ℝⁿ⁺¹`.  Inserting the distinguished coordinate `x` is the
constant `Fin.cons x 0`, so it disappears in the derivative.

The whole point is that `inclY n` sends the `j`-th coordinate direction to the `j.succ`-th
one, which after `appCLM_single` becomes the `(p + j.succ)`-th direction of `ℝ^{p+(n+1)}`,
i.e. exactly the `y`-direction on which `hyb` gives a bound. -/

/-- The continuous linear map `v ↦ Fin.cons 0 v : ℝⁿ → ℝⁿ⁺¹`. -/
private def inclY (n : ℕ) : (Fin n → ℝ) →L[ℝ] (Fin (n + 1) → ℝ) :=
  ContinuousLinearMap.pi
    (fun j : Fin (n + 1) => Fin.cases (0 : (Fin n → ℝ) →L[ℝ] ℝ)
      (fun i : Fin n => ContinuousLinearMap.proj i) j)

private lemma inclY_apply (n : ℕ) (v : Fin n → ℝ) : inclY n v = Fin.cons (0 : ℝ) v := by
  funext j
  induction j using Fin.cases with
  | zero => simp [inclY]
  | succ i => simp [inclY]

/-- `inclY` carries the `i`-th coordinate direction to the `i.succ`-th coordinate direction. -/
private lemma inclY_single {n : ℕ} (i : Fin n) :
    inclY n (Pi.single i (1 : ℝ)) = (Pi.single i.succ (1 : ℝ) : Fin (n + 1) → ℝ) := by
  rw [inclY_apply]
  funext j
  induction j using Fin.cases with
  | zero => simp
  | succ k =>
    by_cases h : k = i
    · subst h; simp
    · simp [Pi.single_eq_of_ne h, Pi.single_eq_of_ne (fun hh => h (Fin.succ_injective n hh))]

/-- The map `y ↦ xPt l x y` is affine, with linear part
`Work.WilG4c.appCLM p n ∘L inclY n`. -/
private lemma hasFDerivAt_xPtY {p n : ℕ} (l : Fin p → ℝ) (x : ℝ) (y : Fin n → ℝ) :
    HasFDerivAt (fun w : Fin n → ℝ => xPt l x w) (Work.WilG4c.appCLM p n ∘L inclY n) y := by
  have h1 : HasFDerivAt (fun w : Fin (n + 1) → ℝ => Fin.append l w) (Work.WilG4c.appCLM p n)
      (Fin.cons x y) := Work.WilG4c.hasFDerivAt_append p n l (Fin.cons x y)
  have h2 : HasFDerivAt (fun w : Fin n → ℝ => Fin.cons x w) (inclY n) y := by
    have hfun : (fun w : Fin n → ℝ => Fin.cons x w)
        = (fun w : Fin n → ℝ => (Fin.cons x (0 : Fin n → ℝ)) + inclY n w) := by
      funext w
      rw [inclY_apply]
      funext j
      induction j using Fin.cases with
      | zero => simp
      | succ i => simp
    rw [hfun]
    exact (inclY n).hasFDerivAt.const_add _
  have hcomp := h1.comp y h2
  have hfun : (fun w : Fin n → ℝ => xPt l x w)
      = (fun w : Fin (n + 1) → ℝ => Fin.append l w) ∘ (fun w : Fin n → ℝ => Fin.cons x w) := rfl
  rw [hfun]
  exact hcomp

/-! ## The slice bound -/

/-- **The slice of a family member in the `y`-variables is `n`-Lipschitz.**  Fixing the
parameter `l` and the distinguished coordinate `x`, the slice `y ↦ f l (pt x y)` has all `n`
coordinate `y`-derivatives bounded by `1` (`hyb`), hence operator norm at most `n` at every
point of the cube; the mean value inequality on the convex cube gives the claim.

The constant `n` is the sharp one: the `y`-gradient has `n` entries each of absolute value
`≤ 1`, and the norm on `Fin n → ℝ` is the sup norm. -/
theorem SliceLipInY {p n : ℕ} (f : (Fin p → ℝ) → (Fin (n + 1) → ℝ) → ℝ)
    (l : Fin p → ℝ) (x : ℝ)
    (hC1 : ∀ y ∈ WilkiesDesign.openCube n, ContDiffAt ℝ 1 (Work.WilkG4c.famFunHat f) (Work.WilkG4c.xPt l x y))
    (hyb : ∀ y ∈ WilkiesDesign.openCube n, ∀ j : Fin n,
      |fderiv ℝ (Work.WilkG4c.famFunHat f) (Work.WilkG4c.xPt l x y)
        (Pi.single (Fin.natAdd p j.succ) 1)| ≤ 1) :
    ∀ y ∈ WilkiesDesign.openCube n, ∀ y' ∈ WilkiesDesign.openCube n,
      |f l (Work.WilkG4c.pt x y) - f l (Work.WilkG4c.pt x y')| ≤ (n : ℝ) * dist y y' := by
  intro y hy y' hy'
  set G : (Fin n → ℝ) → ℝ := fun w => famFunHat f (xPt l x w) with hGdef
  have hG_pt : ∀ w, G w = f l (pt x w) := by
    intro w
    simp only [hGdef, famFunHat_xPt, pt]
  have hdiff : ∀ w ∈ WilkiesDesign.openCube n, DifferentiableAt ℝ G w := by
    intro w hw
    have hd : DifferentiableAt ℝ (famFunHat f) (xPt l x w) :=
      (hC1 w hw).differentiableAt_one
    have hw2 : DifferentiableAt ℝ (fun w : Fin n → ℝ => xPt l x w) w :=
      (hasFDerivAt_xPtY (p := p) l x w).differentiableAt
    rw [hGdef]
    simpa only [Function.comp_def] using hd.comp w hw2
  have hbound : ∀ w ∈ WilkiesDesign.openCube n, ‖fderiv ℝ G w‖ ≤ (n : ℝ) := by
    intro w hw
    have hd : DifferentiableAt ℝ (famFunHat f) (xPt l x w) :=
      (hC1 w hw).differentiableAt_one
    have hfam : HasFDerivAt (famFunHat f) (fderiv ℝ (famFunHat f) (xPt l x w)) (xPt l x w) :=
      hd.hasFDerivAt
    have hcomp := hfam.comp w (hasFDerivAt_xPtY (p := p) l x w)
    have hGf : fderiv ℝ G w =
        (fderiv ℝ (famFunHat f) (xPt l x w)) ∘SL (Work.WilG4c.appCLM p n ∘L inclY n) := by
      rw [hGdef]
      simpa only [Function.comp_def] using hcomp.fderiv
    rw [hGf]
    have hcoord : ∀ j : Fin n,
        |((fderiv ℝ (famFunHat f) (xPt l x w))
            ∘SL (Work.WilG4c.appCLM p n ∘L inclY n))
          (Pi.single j (1 : ℝ))| ≤ 1 := by
      intro j
      rw [ContinuousLinearMap.comp_apply, ContinuousLinearMap.comp_apply, inclY_single,
        Work.WilG4c.appCLM_single]
      exact hyb w hw j
    have hmain := Work.WilG4c.opNorm_le_coord
      ((fderiv ℝ (famFunHat f) (xPt l x w)) ∘SL (Work.WilG4c.appCLM p n ∘L inclY n))
      1 (by norm_num) hcoord
    calc ‖(fderiv ℝ (famFunHat f) (xPt l x w))
          ∘SL (Work.WilG4c.appCLM p n ∘L inclY n)‖
        ≤ 1 * (n : ℝ) := hmain
      _ = (n : ℝ) := one_mul _
  have hmvt := Convex.norm_image_sub_le_of_norm_fderiv_le hdiff hbound
    (Work.WilG4c.convex_openCube n) hy' hy
  rw [hG_pt y, hG_pt y', Real.norm_eq_abs, ← dist_eq_norm] at hmvt
  exact hmvt

end Work.WilG4c

/-! The statement is requested under the name `Work.WilG4c.SliceLipInY` (matching the
directory `WilG4c`).  Some files in this area (e.g. `GoodCellPYLip`) refer to it as
`Work.WilkG4c.SliceLipInY` — the namespace used by the neighbouring `LipDefs`/`SliceLipInX`
files — so we expose that spelling as an alias. -/

namespace Work.WilkG4c

alias SliceLipInY := Work.WilG4c.SliceLipInY

end Work.WilkG4c

