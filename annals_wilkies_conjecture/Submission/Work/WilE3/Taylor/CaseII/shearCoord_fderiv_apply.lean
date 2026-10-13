import Mathlib

namespace Work.WilE3.Taylor.CaseII

theorem shearCoord_fderiv_apply {k : ℕ} (a b : (Fin k → ℝ) → (Fin k → ℝ)) (x : Fin k → ℝ) (s : ℝ)
    (i : Fin k) (ha : HasFDerivAt a (fderiv ℝ a x) x) (hb : HasFDerivAt b (fderiv ℝ b x) x)
    (ξ : Fin k → ℝ) :
    (fderiv ℝ (fun z => a z i + b z i * s) x) ξ = (fderiv ℝ a x) ξ i + (fderiv ℝ b x) ξ i * s := by
  -- The `i`-th coordinate of `a` is the coordinate projection composed with `a`.
  have h1 : HasFDerivAt (fun z => a z i)
      ((ContinuousLinearMap.proj (R := ℝ) i).comp (fderiv ℝ a x)) x := by
    have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj (R := ℝ) i)).comp x ha
    exact h
  have h2 : HasFDerivAt (fun z => b z i)
      ((ContinuousLinearMap.proj (R := ℝ) i).comp (fderiv ℝ b x)) x := by
    have h := (ContinuousLinearMap.hasFDerivAt (ContinuousLinearMap.proj (R := ℝ) i)).comp x hb
    exact h
  -- Multiply the second one by the constant `s`, then add the two.
  have h3 : HasFDerivAt (fun z => b z i * s)
      (s • ((ContinuousLinearMap.proj (R := ℝ) i).comp (fderiv ℝ b x))) x :=
    h2.mul_const s
  have htot : HasFDerivAt (fun z => a z i + b z i * s)
      (((ContinuousLinearMap.proj (R := ℝ) i).comp (fderiv ℝ a x))
        + s • ((ContinuousLinearMap.proj (R := ℝ) i).comp (fderiv ℝ b x))) x :=
    h1.add h3
  -- Identify the `fderiv` with the explicit linear map and evaluate it on `ξ`.
  rw [htot.fderiv]
  simp only [add_apply, smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply]
  ring

end Work.WilE3.Taylor.CaseII
