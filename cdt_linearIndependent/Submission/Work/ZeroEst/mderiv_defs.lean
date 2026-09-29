import Mathlib

/-!
# `Work.ZeroEst.mderiv_defs` — entrywise derivative of a matrix of power series
-/

namespace Work.ZeroEst

open Polynomial PowerSeries Matrix

/-- The entrywise derivative of a matrix of power series. -/
noncomputable def mderiv {ι κ : Type*} (M : Matrix ι κ (PowerSeries ℚ)) :
    Matrix ι κ (PowerSeries ℚ) := M.map (PowerSeries.derivative (R := ℚ))

@[simp]
theorem mderiv_apply {ι κ : Type*} (M : Matrix ι κ (PowerSeries ℚ)) (i : ι) (j : κ) :
    mderiv M i j = PowerSeries.derivative (R := ℚ) (M i j) := rfl

end Work.ZeroEst
