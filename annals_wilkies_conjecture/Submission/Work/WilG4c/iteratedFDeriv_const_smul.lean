import Mathlib

namespace Work.WilG4c

/-- **The `n`-th iterated derivative of a constant multiple is the constant multiple of the
`n`-th iterated derivative**, as an identity of functions. No differentiability hypothesis is
needed: for `m ≥ 1` the junk value `0` of `fderiv` behaves compatibly because `fderiv` is
unconditionally homogeneous in the scalar (`fderiv_const_smul_field`), and for `m = 0` the
statement is pointwise. -/
private theorem iteratedFDeriv_const_smul_fun {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] (a : ℝ) (m : ℕ) (f : E → F) :
    iteratedFDeriv ℝ m (a • f) = a • iteratedFDeriv ℝ m f := by
  induction m with
  | zero =>
    ext x v
    simp [iteratedFDeriv_zero_apply]
  | succ m ih =>
    have hfd : fderiv ℝ (a • iteratedFDeriv ℝ m f)
        = a • fderiv ℝ (iteratedFDeriv ℝ m f) :=
      fderiv_const_smul_field (f := iteratedFDeriv ℝ m f) a
    ext x v
    rw [Pi.smul_apply, smul_apply]
    rw [iteratedFDeriv_succ_apply_left, ih, hfd]
    simp [Pi.smul_apply, iteratedFDeriv_succ_apply_left]

theorem iteratedFDeriv_const_smul {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (a : ℝ) (m : ℕ) (f : E → F) (x : E) :
    iteratedFDeriv ℝ m (a • f) x = a • iteratedFDeriv ℝ m f x :=
  congrFun (iteratedFDeriv_const_smul_fun a m f) x

end Work.WilG4c
