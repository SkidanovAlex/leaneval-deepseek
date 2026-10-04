import Mathlib
import Submission.Work.Diff.STE.Torus
import Submission.Work.Diff.STE.pd_fourierExp

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.Diff.STE

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [DecidableEq ι] in
/-- The Fréchet derivative of the character `fourierExp k` at `x`. -/
lemma hasFDerivAt_fourierExp (k : ι → ℤ) (x : ι → ℝ) :
    HasFDerivAt (fourierExp k)
      ((Complex.exp (fourierLin k x) • (1 : ℂ →L[ℝ] ℂ)).comp (fourierLin k)) x := by
  rw [fourierExp_eq_exp_lin]
  exact ((Complex.hasStrictFDerivAt_exp_real (fourierLin k x)).hasFDerivAt.comp x
    (fourierLin k).hasFDerivAt)

omit [DecidableEq ι] in
/-- `trigFun` as an explicit finite sum of the summands `x ↦ p k * fourierExp k x`. -/
lemma trigFun_eq_sum (p : (ι → ℤ) →₀ ℂ) :
    trigFun p = ∑ k ∈ p.support, (fun y => p k * fourierExp k y) := by
  funext y
  simp only [trigFun, Finset.sum_apply]

theorem pd_trigFun {ι : Type*} [Fintype ι] [DecidableEq ι] (i : ι) (p : (ι → ℤ) →₀ ℂ) :
    Work.Diff.STE.pd i (Work.Diff.STE.trigFun p)
      = fun x => ∑ k ∈ p.support,
          (2 * Real.pi * Complex.I * (k i : ℂ)) * p k * Work.Diff.STE.fourierExp k x := by
  funext x
  -- the Fréchet derivative of the finite sum is the sum of the Fréchet derivatives
  have hsum : HasFDerivAt (trigFun p)
      (∑ k ∈ p.support,
        (p k) • ((Complex.exp (fourierLin k x) • (1 : ℂ →L[ℝ] ℂ)).comp (fourierLin k))) x := by
    rw [trigFun_eq_sum]
    exact HasFDerivAt.sum (fun k _ => (hasFDerivAt_fourierExp (ι := ι) k x).const_mul (p k))
  rw [pd, hsum.fderiv]
  -- evaluate the resulting continuous linear map on the basis vector `eᵢ`
  simp only [ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, one_apply_eq_self, smul_eq_mul,
    fourierLin_single, fourierExp_eq_exp_lin]
  exact Finset.sum_congr rfl (fun k _ => by ring)

end Work.Diff.STE
