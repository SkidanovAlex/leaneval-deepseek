import Mathlib
import Submission.Work.CR.Flat.Cauchy.bmCz.bmKernelDerivAux

namespace Work.CR.Flat.Cauchy.bmCz

/-- The Bochner–Martinelli kernel component `y ↦ bmKernel j y` is differentiable (in the real
sense) at every point `x ≠ 0`, with derivative the explicit continuous linear map
`bmKernelFDeriv j x`.

We write `bmKernel j y = conj (y j) · ((sm y : ℝ) : ℂ) ^ (-(n : ℤ))` where `sm` is the squared
Euclidean norm (smooth everywhere), apply the product rule with

* `y ↦ conj (y j)`, whose derivative is `conjCLE ∘ projCLM j`, and
* `y ↦ ((sm y : ℝ) : ℂ) ^ (-(n : ℤ))`, obtained from the chain rule with `sm`
  (`hasFDerivAt_sm`) and the one-dimensional `zpow` derivative `hasDerivAt_zpow`. -/
theorem hasFDerivAt_bmKernel {n : ℕ} (j : Fin n) {x : Fin n → ℂ} (hx : x ≠ 0) :
    HasFDerivAt (fun y : Fin n → ℂ => Work.CR.Flat.Cauchy.bmKernel j y)
      (Work.CR.Flat.Cauchy.bmCz.bmKernelFDeriv j x) x := by
  have hne : (((sm x : ℝ) : ℂ)) ≠ 0 := Complex.ofReal_ne_zero.mpr (ne_of_gt (sm_pos hx))
  -- derivative of the anti-holomorphic coordinate `y ↦ conj (y j)`
  have hconj : HasFDerivAt (fun y : Fin n → ℂ => starRingEnd ℂ (y j))
      ((Complex.conjCLE : ℂ →L[ℝ] ℂ).comp (projCLM j)) x :=
    (Complex.conjCLE : ℂ →L[ℝ] ℂ).hasFDerivAt.comp x (projCLM j).hasFDerivAt
  -- derivative of `y ↦ ((sm y : ℝ) : ℂ)`
  have hofreal : HasFDerivAt (fun y : Fin n → ℂ => ((sm y : ℝ) : ℂ))
      (Complex.ofRealCLM.comp (smDeriv x)) x :=
    Complex.ofRealCLM.hasFDerivAt.comp x (hasFDerivAt_sm x)
  -- derivative of `z ↦ z ^ (-(n : ℤ))` at `(sm x : ℂ)`
  have hzp : HasFDerivAt (fun z : ℂ => z ^ (-(n:ℤ)))
      (ContinuousLinearMap.mul ℝ ℂ
        ((↑(-(n:ℤ)) : ℂ) * ((((sm x : ℝ) : ℂ))) ^ (-(n:ℤ) - 1))) (((sm x : ℝ) : ℂ)) := by
    have hd : HasDerivAt (fun z : ℂ => z ^ (-(n:ℤ)))
        ((↑(-(n:ℤ)) : ℂ) * (((sm x : ℝ) : ℂ)) ^ (-(n:ℤ) - 1)) (((sm x : ℝ) : ℂ)) :=
      hasDerivAt_zpow (-(n:ℤ)) _ (Or.inl hne)
    have h := hd.hasFDerivAt.restrictScalars ℝ
    have hEq : ContinuousLinearMap.restrictScalars ℝ
        (ContinuousLinearMap.toSpanSingleton ℂ
          ((↑(-(n:ℤ)) : ℂ) * (((sm x : ℝ) : ℂ)) ^ (-(n:ℤ) - 1)))
        = ContinuousLinearMap.mul ℝ ℂ
          ((↑(-(n:ℤ)) : ℂ) * (((sm x : ℝ) : ℂ)) ^ (-(n:ℤ) - 1)) := by
      ext v
      simp only [ContinuousLinearMap.coe_restrictScalars',
        ContinuousLinearMap.toSpanSingleton_apply]
      exact mul_comm v _
    rwa [hEq] at h
  -- chain rule for `y ↦ ((sm y : ℝ) : ℂ) ^ (-(n : ℤ))`, then product rule
  have hmain := (hzp.comp x hofreal).mul hconj
  convert hmain using 1
  · funext y
    simp only [Pi.mul_apply, Function.comp_apply]
    rw [bmKernel_eq]
    ring
  · rw [bmKernelFDeriv]
    simp only [Function.comp_apply]
    exact add_comm _ _

end Work.CR.Flat.Cauchy.bmCz
