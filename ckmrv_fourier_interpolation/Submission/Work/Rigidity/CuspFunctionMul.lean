import Mathlib

namespace Work.Rigidity

/-- The `cuspFunction` of a pointwise product is the pointwise product of the
`cuspFunction`s (this is `UpperHalfPlane.cuspFunction_mul`), so analyticity at
`0` is preserved by pointwise multiplication. -/
theorem CuspFunctionMul {F G : UpperHalfPlane → ℂ}
    (hF : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 F) 0)
    (hG : AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 G) 0) :
    AnalyticAt ℂ (UpperHalfPlane.cuspFunction 1 (F * G)) 0 := by
  rw [UpperHalfPlane.cuspFunction_mul (h := 1) hF.continuousAt hG.continuousAt]
  exact hF.mul hG

end Work.Rigidity
