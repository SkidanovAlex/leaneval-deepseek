import Mathlib

namespace Work.FIChain

/-- For `Pz ≥ 2`, `D ≥ 1` and `D < Pz ^ b`, raising `D` to the exponent
`log 2 / log Pz` (which turns `Pz` into `2`) is bounded by `2 ^ b`. -/
theorem rpow_log_div_log_le_two_pow {Pz D b : ℕ} (hPz : 2 ≤ Pz) (hD : 1 ≤ D)
    (h : D < Pz ^ b) :
    (D : ℝ) ^ (Real.log 2 / Real.log (Pz : ℝ)) ≤ (2 : ℝ) ^ b := by
  have hPz1 : (1 : ℝ) < (Pz : ℝ) := by
    have : (1 : ℕ) < Pz := by omega
    exact_mod_cast this
  have hPzpos : (0 : ℝ) < (Pz : ℝ) := by linarith
  set α : ℝ := Real.log 2 / Real.log (Pz : ℝ) with hαdef
  have hlogPz : 0 < Real.log (Pz : ℝ) := Real.log_pos hPz1
  have hα : 0 ≤ α := by
    rw [hαdef]
    exact div_nonneg (Real.log_nonneg (by norm_num)) (le_of_lt hlogPz)
  have hD0 : (0 : ℝ) ≤ (D : ℝ) := by positivity
  have hcast : (D : ℝ) < (Pz : ℝ) ^ b := by
    have hh := (Nat.cast_lt (α := ℝ)).mpr h
    simpa [Nat.cast_pow] using hh
  have hle : (D : ℝ) ^ α ≤ ((Pz : ℝ) ^ b) ^ α :=
    Real.rpow_le_rpow hD0 (le_of_lt hcast) hα
  have hB : ((Pz : ℝ) ^ b) ^ α = (2 : ℝ) ^ b := by
    rw [← Real.rpow_natCast (Pz : ℝ) b, ← Real.rpow_mul (le_of_lt hPzpos)]
    rw [Real.rpow_def_of_pos hPzpos]
    rw [show Real.log (Pz : ℝ) * ((b : ℝ) * α) = (b : ℝ) * Real.log 2 from by
      rw [hαdef]; field_simp]
    rw [Real.exp_nat_mul, Real.exp_log (by norm_num : (0 : ℝ) < 2)]
  calc (D : ℝ) ^ α ≤ ((Pz : ℝ) ^ b) ^ α := hle
    _ = (2 : ℝ) ^ b := hB

end Work.FIChain
