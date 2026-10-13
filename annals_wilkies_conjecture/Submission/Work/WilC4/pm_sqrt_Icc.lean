import Mathlib

namespace Work.WilC4

theorem pm_sqrt_Icc {u v : ℝ} (hu : 0 < u) (huv : u ≤ v) :
    u ≤ Real.sqrt (u * v) ∧ Real.sqrt (u * v) ≤ v := by
  have hv : 0 < v := lt_of_lt_of_le hu huv
  have h1 : u ^ 2 ≤ u * v := by nlinarith
  have h2 : u * v ≤ v ^ 2 := by nlinarith
  constructor
  · calc u = Real.sqrt (u ^ 2) := (Real.sqrt_sq hu.le).symm
      _ ≤ Real.sqrt (u * v) := Real.sqrt_le_sqrt h1
  · calc Real.sqrt (u * v) ≤ Real.sqrt (v ^ 2) := Real.sqrt_le_sqrt h2
      _ = v := Real.sqrt_sq hv.le

end Work.WilC4
