import Mathlib

namespace Work.WilE3.Taylor.CaseII

open scoped BigOperators

theorem aux_fderiv_mul_exp_sum_single {k : ℕ} {g : (Fin k → ℝ) → ℝ}
    {v y u : Fin k → ℝ} (hg : DifferentiableAt ℝ g u) (l : Fin k) :
    fderiv ℝ (fun z : Fin k → ℝ => g z * Real.exp (∑ i, v i * (z i - y i))) u (Pi.single l 1)
      = (fderiv ℝ g u (Pi.single l 1) + g u * v l) * Real.exp (∑ i, v i * (u i - y i)) := by
  -- The directional derivative of the linear phase `z ↦ ∑ i, v i * (z i - y i)` in
  -- direction `Pi.single l 1` is `v l`.
  set L : (Fin k → ℝ) →L[ℝ] ℝ :=
    ∑ i, (v i) • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ) with hLdef
  have hL : L (Pi.single l 1) = v l := by
    rw [hLdef]
    simp only [sum_apply, smul_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
    rw [Finset.sum_eq_single l]
    · simp
    · intro b _ hb; rw [Pi.single_eq_of_ne hb]; ring
    · intro h; exact absurd (Finset.mem_univ l) h
  -- The phase is differentiable with derivative `L`.
  have hfun : (∑ i, (fun z : Fin k → ℝ => v i * (z i - y i)))
      = (fun z => ∑ i, v i * (z i - y i)) := by
    funext z; simp [Finset.sum_apply]
  have hf : HasFDerivAt (fun z : Fin k → ℝ => ∑ i, v i * (z i - y i)) L u := by
    have h := HasFDerivAt.sum (u := Finset.univ)
      (A := fun i (z : Fin k → ℝ) => v i * (z i - y i))
      (A' := fun i => (v i) • (ContinuousLinearMap.proj i : (Fin k → ℝ) →L[ℝ] ℝ))
      (fun i _ => ((hasFDerivAt_apply i u).sub_const (y i)).const_mul (v i))
    rw [hLdef]
    rw [hfun] at h
    exact h
  have hfe : HasFDerivAt (fun z : Fin k → ℝ => Real.exp (∑ i, v i * (z i - y i)))
      (Real.exp (∑ i, v i * (u i - y i)) • L) u := hf.exp
  -- Product rule.
  have hmul : HasFDerivAt (fun z : Fin k → ℝ => g z * Real.exp (∑ i, v i * (z i - y i)))
      (g u • (Real.exp (∑ i, v i * (u i - y i)) • L)
        + Real.exp (∑ i, v i * (u i - y i)) • (fderiv ℝ g u)) u :=
    (hg.hasFDerivAt).mul hfe
  rw [hmul.fderiv]
  simp only [add_apply, smul_apply, smul_eq_mul, hL]
  ring

end Work.WilE3.Taylor.CaseII
