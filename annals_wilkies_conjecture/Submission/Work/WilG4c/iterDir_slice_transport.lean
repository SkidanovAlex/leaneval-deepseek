import Mathlib
import Submission.Work.WilG4c.hbdd_defs
import Submission.Work.WilG4c.IterDirAux

set_option autoImplicit false
noncomputable section
open scoped Topology

namespace Work.WilG4c

open Work.WilkG4c

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
    HasFDerivAt (fun w : Fin n → ℝ => Work.WilkG4c.pt x w) (incl n) y := by
  have hfun : (fun w : Fin n → ℝ => Work.WilkG4c.pt x w)
      = (fun w : Fin n → ℝ =>
          (Fin.cons x (0 : Fin n → ℝ) : Fin (n + 1) → ℝ) + incl n w) := by
    funext w
    rw [Work.WilkG4c.pt, incl_apply]
    funext j
    induction j using Fin.cases with
    | zero => simp
    | succ i => simp
  rw [hfun]
  exact (incl n).hasFDerivAt.const_add _

/-- **The iterated directional derivatives of `g` along `y`-directions are those of the slice
`slice g x`.**  The directions in the ambient `ℝⁿ⁺¹` are the images of the `y`-directions under
`Fin.succ`; the statement is proved by induction on the list of directions, the inductive step
being the chain rule for `y ↦ g (pt x y)` together with the eventual equality of the derivatives
of lower order. -/
theorem iterDir_slice_transport {n : ℕ} (g : (Fin (n + 1) → ℝ) → ℝ) (M : List (Fin n))
    (x : ℝ) (y : Fin n → ℝ) (h : ContDiffAt ℝ M.length g (Work.WilkG4c.pt x y)) :
    Work.WilkG4c.iterDir (M.map Fin.succ) g (Work.WilkG4c.pt x y)
      = Work.WilkG4c.iterDir M (Work.WilkG4c.slice g x) y := by
  revert g x y
  induction M with
  | nil => intro g x y _; rfl
  | cons i M' ih =>
    intro g x y h
    simp only [List.length_cons] at h
    -- `g` is `C^{|M'|+1}` at `pt x y`, hence `C^{|M'|}` on a neighbourhood of `pt x y`, hence (by
    -- continuity of `y' ↦ pt x y'`) on a neighbourhood of `y` after pulling back along that map.
    have hle : ContDiffAt ℝ ((M'.length : ℕ) : WithTop ℕ∞) g (Work.WilkG4c.pt x y) :=
      h.of_le (by simp)
    have hS : ∀ᶠ z in 𝓝 (Work.WilkG4c.pt x y),
        ContDiffAt ℝ ((M'.length : ℕ) : WithTop ℕ∞) g z :=
      hle.eventually (by simp)
    have hpt : ∀ᶠ w in 𝓝 y,
        ContDiffAt ℝ ((M'.length : ℕ) : WithTop ℕ∞) g (Work.WilkG4c.pt x w) :=
      (hasFDerivAt_pt n x y).continuousAt.eventually hS
    -- The induction hypothesis, as an eventual equality of functions.
    have h_ev : (fun w : Fin n → ℝ => iterDir (M'.map Fin.succ) g (Work.WilkG4c.pt x w))
        =ᶠ[𝓝 y] iterDir M' (Work.WilkG4c.slice g x) := by
      filter_upwards [hpt] with w hw
      exact ih g x w hw
    rw [List.map_cons]
    simp only [iterDir_cons]
    rw [← h_ev.fderiv_eq]
    -- Chain rule along the affine inclusion `y ↦ pt x y`.
    have hFdiff : DifferentiableAt ℝ (iterDir (M'.map Fin.succ) g) (Work.WilkG4c.pt x y) :=
      (Work.WilG4c.iterDir_contDiffAt g (M'.map Fin.succ) 1 (Work.WilkG4c.pt x y)
        (by simpa [List.length_map] using h)).differentiableAt (by norm_num)
    have hcomp : fderiv ℝ
          (fun w : Fin n → ℝ => iterDir (M'.map Fin.succ) g (Work.WilkG4c.pt x w)) y
        = (fderiv ℝ (iterDir (M'.map Fin.succ) g) (Work.WilkG4c.pt x y)).comp (incl n) := by
      have h₁ := fderiv_comp (x := y)
        (f := fun w : Fin n → ℝ => Work.WilkG4c.pt x w)
        (g := iterDir (M'.map Fin.succ) g) hFdiff (hasFDerivAt_pt n x y).differentiableAt
      rw [(hasFDerivAt_pt n x y).fderiv] at h₁
      exact h₁
    rw [hcomp, ContinuousLinearMap.comp_apply, incl_single]

end Work.WilG4c
