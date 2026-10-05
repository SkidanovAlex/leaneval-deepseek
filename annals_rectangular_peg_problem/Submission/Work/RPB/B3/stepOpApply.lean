import Mathlib
import Submission.Work.RPB.B3.EvenTaylorDefs

namespace Work.RPB.B3

/-- `stepOp h` is the Hadamard quotient of `h`: for `C^1` `h`,
`h (p, r) - h (p, 0) = r • stepOp h (p, r)`.

This is the fundamental theorem of calculus for the slice `s ↦ h (p, s)` together with the
substitution `s = r * u`, which turns `∫_0^r ∂_r h (p, s) ds` into `r • ∫_0^1 ∂_r h (p, r u) du`. -/
theorem stepOpApply {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (h : (ℝ × ℝ) × ℝ → E) (hh : ContDiff ℝ 1 h) (z : (ℝ × ℝ) × ℝ) :
    h (z.1, z.2) - h (z.1, 0) = z.2 • Work.RPB.B3.EvenTaylor.stepOp h z := by
  obtain ⟨p, r⟩ := z
  rw [Work.RPB.B3.EvenTaylor.stepOp]
  symm
  -- `h` is differentiable, and `pdR h = ∂_r h` is continuous.
  have hdiff : Differentiable ℝ h := hh.differentiable (by norm_num)
  have hpdr_cont : Continuous (fun z : (ℝ × ℝ) × ℝ => Work.RPB.B3.EvenTaylor.pdR h z) := by
    have hc : Continuous (fderiv ℝ h) := hh.continuous_fderiv (by norm_num)
    simpa [Work.RPB.B3.EvenTaylor.pdR] using hc.clm_apply continuous_const
  have hslice_cont : Continuous (fun s : ℝ => Work.RPB.B3.EvenTaylor.pdR h (p, s)) :=
    hpdr_cont.comp (continuous_const.prodMk continuous_id)
  -- The slice `s ↦ h (p, s)` has derivative `pdR h (p, s)`.
  have hderiv : ∀ s : ℝ, HasDerivAt (fun s : ℝ => h (p, s))
      (Work.RPB.B3.EvenTaylor.pdR h (p, s)) s := by
    intro s
    have hd : DifferentiableAt ℝ h (p, s) := hdiff.differentiableAt
    have h1 : HasFDerivAt (fun s : ℝ => (p, s)) (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ) s :=
      hasFDerivAt_prodMk_right p s
    have h2 : HasFDerivAt (fun s : ℝ => h (p, s))
        ((fderiv ℝ h (p, s)).comp (ContinuousLinearMap.inr ℝ (ℝ × ℝ) ℝ)) s :=
      hd.hasFDerivAt.comp s h1
    simpa [Work.RPB.B3.EvenTaylor.pdR, Work.RPB.B3.EvenTaylor.ee, ContinuousLinearMap.inr_apply]
      using h2.hasDerivAt
  -- FTC in the form `r • ∫_0^1 ∂_r h (p, t r) dt = h (p, r) - h (p, 0)`.
  have key := intervalIntegral.integral_unitInterval_deriv_eq_sub
      (f := fun s : ℝ => h (p, s))
      (f' := fun s : ℝ => Work.RPB.B3.EvenTaylor.pdR h (p, s))
      (z₀ := 0) (z₁ := r)
      ((hslice_cont.comp (by fun_prop : Continuous fun t : ℝ => 0 + t • r)).continuousOn)
      (fun t _ => hderiv _)
  simpa only [zero_add, smul_eq_mul, mul_comm] using key

end Work.RPB.B3
