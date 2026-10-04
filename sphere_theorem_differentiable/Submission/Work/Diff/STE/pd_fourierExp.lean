import Mathlib
import Submission.Work.Diff.STE.Torus

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

/-!
# `pd_fourierExp`: the partial derivatives of the Fourier characters

`fourierExp m` is the character `x ↦ exp (2π i ∑_j m_j x_j)` on the torus.  It is the
exponential of the (real-)linear functional `fourierLin m`, so the chain rule gives its
Fréchet derivative; evaluating on `eᵢ = Pi.single i 1` produces `2πi mᵢ` times the
character itself.
-/

open BigOperators

noncomputable section

namespace Work.Diff.STE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

/-- The real-linear functional `x ↦ 2πi ∑_j m_j x_j` whose exponential is `fourierExp m`. -/
def fourierLin (m : ι → ℤ) : (ι → ℝ) →L[ℝ] ℂ :=
  ∑ j : ι, (2 * Real.pi * Complex.I * (m j : ℂ)) •
    (Complex.ofRealCLM.comp (ContinuousLinearMap.proj j))

omit [DecidableEq ι] in
/-- The defining formula of `fourierLin`. -/
lemma fourierLin_apply (m : ι → ℤ) (x : ι → ℝ) :
    fourierLin m x = 2 * Real.pi * Complex.I * ∑ j, (m j : ℂ) * (x j : ℂ) := by
  simp only [fourierLin, sum_apply, smul_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.proj_apply, Complex.ofRealCLM_apply]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  ring

/-- `fourierLin` on the basis vector `eᵢ`. -/
lemma fourierLin_single (m : ι → ℤ) (i : ι) :
    fourierLin m (Pi.single i (1 : ℝ)) = 2 * Real.pi * Complex.I * (m i : ℂ) := by
  have h : (∑ j, (m j : ℂ) * ((Pi.single i (1 : ℝ) : ι → ℝ) j : ℂ)) = (m i : ℂ) := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj; simp [Pi.single_eq_of_ne hj]
    · intro h; exact absurd (Finset.mem_univ i) h
  rw [fourierLin_apply, h]

omit [DecidableEq ι] in
/-- `fourierExp m` is the exponential of the linear functional `fourierLin m`. -/
lemma fourierExp_eq_exp_lin (m : ι → ℤ) :
    fourierExp m = fun y => Complex.exp (fourierLin m y) := by
  funext y
  rw [fourierExp, fourierLin_apply]

/-- The `i`-th partial derivative of the character `fourierExp m`. -/
theorem pd_fourierExp {ι : Type*} [Fintype ι] [DecidableEq ι]
    (m : ι → ℤ) (i : ι) (x : ι → ℝ) :
    Work.Diff.STE.pd i (Work.Diff.STE.fourierExp m) x
      = 2 * Real.pi * Complex.I * (m i : ℂ) * Work.Diff.STE.fourierExp m x := by
  have hcomp : HasFDerivAt (fourierExp m)
      ((Complex.exp (fourierLin m x) • (1 : ℂ →L[ℝ] ℂ)).comp (fourierLin m)) x := by
    rw [fourierExp_eq_exp_lin]
    exact ((Complex.hasStrictFDerivAt_exp_real (fourierLin m x)).hasFDerivAt.comp x
      (fourierLin m).hasFDerivAt)
  rw [pd, hcomp.fderiv]
  simp only [ContinuousLinearMap.comp_apply, smul_apply, one_apply_eq_self, smul_eq_mul]
  rw [fourierLin_single, fourierExp_eq_exp_lin]
  ring

end Work.Diff.STE
