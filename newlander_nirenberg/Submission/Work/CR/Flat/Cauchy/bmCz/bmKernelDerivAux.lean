/-
Copyright: none.  Part of the `Newlander-Nirenberg` formalisation project.

# The first derivatives of the Bochner–Martinelli kernel component

This file collects the vocabulary needed to differentiate the Bochner–Martinelli kernel
component `bmKernel j x = \bar x_j / ‖x‖^{2n}` (see
`Submission/Work/CR/Flat/Cauchy/bmDefs.lean`) with respect to the real variable
`x : ℂⁿ`, `ℂⁿ = Fin n → ℂ`.

We rewrite the kernel in the form

  `bmKernel j x = \bar x_j · (s x)^{-n}`,   `s x = ∑_l ‖x_l‖² = ‖x‖²`,

where `s` is the *smooth everywhere* function `x ↦ ∑_l normSq (x_l)` (the squared Euclidean
norm, which unlike `eucNorm` does not involve a square root).  `sm` is that function and
`smDeriv x` its Fréchet derivative, which is the `ℝ`-linear map

  `smDeriv x = ∑_l 2 Re(x_l) • re_l + 2 Im(x_l) • im_l`

(the `l`-th coordinate projection followed by real/imaginary part).  Then
`bmKernelFDeriv j x` is the Fréchet derivative of `y ↦ bmKernel j y` at a point `x ≠ 0`,
written out as a continuous linear map:

  `bmKernelFDeriv j x = \bar x_j • (· ↦ (-n) ‖x‖^{-2n-2} · (smDeriv x ·)) + ‖x‖^{-2n} · (· ↦ \overline{v_j})`

(the `zpow` normalisation `(s x)^{-n} = ‖x‖^{-2n}` is `eucNorm_pow_inv_eq` below).
-/
import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCZDefs

noncomputable section

open scoped NNReal ENNReal
open MeasureTheory Set

namespace Work.CR.Flat.Cauchy.bmCz

/-! ### The squared Euclidean norm as a polynomial function -/

/-- The squared Euclidean norm on `ℂⁿ = Fin n → ℂ`, written as a sum of `normSq`s so that
it is a polynomial (hence smooth) function of the coordinates. -/
noncomputable def sm {n : ℕ} : (Fin n → ℂ) → ℝ := ∑ l, fun y => Complex.normSq (y l)

lemma sm_apply {n : ℕ} (x : Fin n → ℂ) : sm x = ∑ l, Complex.normSq (x l) := by
  simp [sm, Finset.sum_apply]

lemma sm_eq_eucNorm_sq {n : ℕ} (x : Fin n → ℂ) : sm x = eucNorm x ^ 2 := by
  rw [sm_apply, eucNorm_sq]
  exact Finset.sum_congr rfl fun l _ => Complex.normSq_eq_norm_sq (x l)

lemma sm_nonneg {n : ℕ} (x : Fin n → ℂ) : 0 ≤ sm x := by
  rw [sm_eq_eucNorm_sq]; exact sq_nonneg _

lemma sm_pos {n : ℕ} {x : Fin n → ℂ} (hx : x ≠ 0) : 0 < sm x := by
  rw [sm_eq_eucNorm_sq]
  exact pow_pos (eucNorm_pos hx) 2

lemma sm_ne_zero {n : ℕ} {x : Fin n → ℂ} (hx : x ≠ 0) : sm x ≠ 0 := ne_of_gt (sm_pos hx)

/-! ### Coordinate projections and the derivative of `sm` -/

/-- The `l`-th coordinate projection `ℂⁿ → ℂ`, as an `ℝ`-linear map. -/
noncomputable def projCLM {n : ℕ} (l : Fin n) : (Fin n → ℂ) →L[ℝ] ℂ :=
  ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin n => ℂ) l

@[simp] lemma projCLM_apply {n : ℕ} (l : Fin n) (y : Fin n → ℂ) : projCLM l y = y l := rfl

/-- The Fréchet derivative of `sm` at `x`: `v ↦ ∑_l 2 Re(x_l) Re(v_l) + 2 Im(x_l) Im(v_l)`,
i.e. `v ↦ 2 Re ⟪x, v⟫`. -/
noncomputable def smDeriv {n : ℕ} (x : Fin n → ℂ) : (Fin n → ℂ) →L[ℝ] ℝ :=
  ∑ l, ((2 * (x l).re) • (Complex.reCLM.comp (projCLM l)) +
        (2 * (x l).im) • (Complex.imCLM.comp (projCLM l)))

lemma hasFDerivAt_sm {n : ℕ} (x : Fin n → ℂ) :
    HasFDerivAt (fun y : Fin n → ℂ => sm y) (smDeriv x) x := by
  have hnorm : ∀ l : Fin n, HasFDerivAt (fun w : ℂ => Complex.normSq w)
      (((2 * (x l).re) • Complex.reCLM + (2 * (x l).im) • Complex.imCLM)) (x l) := by
    intro l
    have h1 : HasFDerivAt (fun w : ℂ => w.re * w.re)
        ((x l).re • Complex.reCLM + (x l).re • Complex.reCLM) (x l) :=
      (Complex.reCLM.hasFDerivAt (x := x l)).mul (Complex.reCLM.hasFDerivAt (x := x l))
    have h2 : HasFDerivAt (fun w : ℂ => w.im * w.im)
        ((x l).im • Complex.imCLM + (x l).im • Complex.imCLM) (x l) :=
      (Complex.imCLM.hasFDerivAt (x := x l)).mul (Complex.imCLM.hasFDerivAt (x := x l))
    have h3 := h1.add h2
    convert h3 using 1
    · ext w; simp [Complex.normSq_apply]
    · ext v; simp; ring
  have h : ∀ l : Fin n, HasFDerivAt (fun y : Fin n → ℂ => Complex.normSq (y l))
      (((2 * (x l).re) • Complex.reCLM + (2 * (x l).im) • Complex.imCLM).comp
        (projCLM l)) x := by
    intro l
    exact (hnorm l).comp x (projCLM l).hasFDerivAt
  have hsum := HasFDerivAt.sum (x := x) (u := Finset.univ)
      (A := fun l : Fin n => fun y : Fin n → ℂ => Complex.normSq (y l))
      (A' := fun l : Fin n => ((2 * (x l).re) • Complex.reCLM + (2 * (x l).im) • Complex.imCLM).comp
        (projCLM l)) (fun i _ => h i)
  have hfun : (fun y : Fin n → ℂ => sm y) = (∑ i, fun y : Fin n → ℂ => Complex.normSq (y i)) := by
    funext y; simp [sm, Finset.sum_apply]
  rw [hfun]
  convert hsum using 1
  ext v
  simp [smDeriv, ContinuousLinearMap.comp_apply]

/-! ### The kernel, its derivative, and the basic rewrites -/

/-- The Fréchet derivative of `y ↦ bmKernel j y` at `x`, as an explicit continuous linear
map (`x ≠ 0` is required for the formula to be the actual derivative). -/
noncomputable def bmKernelFDeriv {n : ℕ} (j : Fin n) (x : Fin n → ℂ) : (Fin n → ℂ) →L[ℝ] ℂ :=
  starRingEnd ℂ (x j) •
      ((ContinuousLinearMap.mul ℝ ℂ ((↑(-(n:ℤ)) : ℂ) * ((((sm x : ℝ) : ℂ))) ^ (-(n:ℤ) - 1)) :
        ℂ →L[ℝ] ℂ)).comp (Complex.ofRealCLM.comp (smDeriv x))
    + ((((sm x : ℝ) : ℂ)) ^ (-(n:ℤ))) • ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (projCLM j))

/-- `‖x‖^{-2n}` written as a power of the squared norm: the normal form in which we
differentiate the kernel. -/
lemma eucNorm_pow_inv_eq {n : ℕ} (x : Fin n → ℂ) :
    (((eucNorm x : ℝ) : ℂ) ^ (2 * n))⁻¹ = (((sm x : ℝ) : ℂ)) ^ (-(n:ℤ)) := by
  have hreal : (eucNorm x) ^ (2 * n) = (sm x) ^ n := by
    rw [pow_mul, ← sm_eq_eucNorm_sq]
  rw [← Complex.ofReal_pow (eucNorm x) (2 * n), hreal,
    Complex.ofReal_pow, zpow_neg, zpow_natCast]

/-- The Bochner–Martinelli kernel component as `\bar x_j` times a power of the squared
Euclidean norm. -/
lemma bmKernel_eq {n : ℕ} (j : Fin n) (y : Fin n → ℂ) :
    bmKernel j y = starRingEnd ℂ (y j) * (((sm y : ℝ) : ℂ) ^ (-(n:ℤ))) := by
  rw [bmKernel, div_eq_mul_inv, eucNorm_pow_inv_eq]

end Work.CR.Flat.Cauchy.bmCz
