import Mathlib

set_option linter.unusedVariables false

namespace Work.FIArea6V

/-- Elementary arithmetic estimate.  If `L ≥ 1`, `θ > 0`, `F > 0` with
`exp(-√L/4) L³ ≤ θ` and `exp(√L)/2 ≤ F`, then `L³/(θ F) ≤ 2 exp(-√L/4) L⁶`. -/
theorem S16TailFreqArith {L θ F : ℝ} (hL : 1 ≤ L) (hθ : 0 < θ) (hF : 0 < F)
    (hθle : Real.exp (-(Real.sqrt L / 4)) * L ^ (3 : ℕ) ≤ θ)
    (hFle : Real.exp (Real.sqrt L) / 2 ≤ F) :
    L ^ (3 : ℕ) / (θ * F) ≤ 2 * Real.exp (-(Real.sqrt L / 4)) * L ^ (6 : ℕ) := by
  have hLpos : (0:ℝ) < L := lt_of_lt_of_le one_pos hL
  have hL3pos : (0:ℝ) < L ^ (3:ℕ) := pow_pos hLpos 3
  have hBpos : 0 < Real.exp (Real.sqrt L) / 2 := by positivity
  have hApos : 0 < Real.exp (-(Real.sqrt L / 4)) * L ^ (3:ℕ) :=
    mul_pos (Real.exp_pos _) hL3pos
  have hABpos : 0 < Real.exp (-(Real.sqrt L / 4)) * L ^ (3:ℕ) * (Real.exp (Real.sqrt L) / 2) :=
    mul_pos hApos hBpos
  have hprod : Real.exp (-(Real.sqrt L / 4)) * L ^ (3:ℕ) * (Real.exp (Real.sqrt L) / 2) ≤ θ * F :=
    mul_le_mul hθle hFle (le_of_lt hBpos) (le_of_lt hθ)
  have hle1 : L ^ (3:ℕ) / (θ * F)
      ≤ L ^ (3:ℕ) / (Real.exp (-(Real.sqrt L / 4)) * L ^ (3:ℕ) * (Real.exp (Real.sqrt L) / 2)) :=
    div_le_div_of_nonneg_left (le_of_lt hL3pos) hABpos hprod
  have hAB_eq : Real.exp (-(Real.sqrt L / 4)) * L ^ (3:ℕ) * (Real.exp (Real.sqrt L) / 2)
      = Real.exp (3 * (Real.sqrt L / 4)) * L ^ (3:ℕ) / 2 := by
    have he : Real.exp (-(Real.sqrt L / 4)) * Real.exp (Real.sqrt L)
        = Real.exp (3 * (Real.sqrt L / 4)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [← he]; ring
  rw [hAB_eq] at hle1
  have hval : L ^ (3:ℕ) / (Real.exp (3 * (Real.sqrt L / 4)) * L ^ (3:ℕ) / 2)
      ≤ 2 * Real.exp (-(3 * (Real.sqrt L / 4))) := by
    rw [div_le_iff₀ (by positivity)]
    have h1 : Real.exp (-(3 * (Real.sqrt L / 4))) * Real.exp (3 * (Real.sqrt L / 4)) = 1 := by
      rw [← Real.exp_add, neg_add_cancel, Real.exp_zero]
    have hthis : 2 * Real.exp (-(3 * (Real.sqrt L / 4)))
        * (Real.exp (3 * (Real.sqrt L / 4)) * L ^ (3:ℕ) / 2) = L ^ (3:ℕ) := by
      calc 2 * Real.exp (-(3 * (Real.sqrt L / 4))) * (Real.exp (3 * (Real.sqrt L / 4)) * L ^ (3:ℕ) / 2)
          = (Real.exp (-(3 * (Real.sqrt L / 4))) * Real.exp (3 * (Real.sqrt L / 4))) * L ^ (3:ℕ) := by ring
        _ = 1 * L ^ (3:ℕ) := by rw [h1]
        _ = L ^ (3:ℕ) := by ring
    rw [hthis]
  have hfinal : 2 * Real.exp (-(3 * (Real.sqrt L / 4)))
      ≤ 2 * Real.exp (-(Real.sqrt L / 4)) * L ^ (6:ℕ) := by
    have hle1' : Real.exp (-(3 * (Real.sqrt L / 4))) ≤ Real.exp (-(Real.sqrt L / 4)) := by
      apply Real.exp_le_exp.mpr
      linarith [Real.sqrt_nonneg L]
    have hL6 : (1:ℝ) ≤ L ^ (6:ℕ) := one_le_pow₀ hL
    have h2 : 2 * Real.exp (-(3 * (Real.sqrt L / 4))) ≤ 2 * Real.exp (-(Real.sqrt L / 4)) := by
      linarith
    calc 2 * Real.exp (-(3 * (Real.sqrt L / 4)))
        ≤ 2 * Real.exp (-(Real.sqrt L / 4)) := h2
      _ = 2 * Real.exp (-(Real.sqrt L / 4)) * 1 := by ring
      _ ≤ 2 * Real.exp (-(Real.sqrt L / 4)) * L ^ (6:ℕ) :=
          mul_le_mul_of_nonneg_left hL6 (by positivity)
  calc L ^ (3:ℕ) / (θ * F)
      ≤ L ^ (3:ℕ) / (Real.exp (3 * (Real.sqrt L / 4)) * L ^ (3:ℕ) / 2) := hle1
    _ ≤ 2 * Real.exp (-(3 * (Real.sqrt L / 4))) := hval
    _ ≤ 2 * Real.exp (-(Real.sqrt L / 4)) * L ^ (6:ℕ) := hfinal

end Work.FIArea6V
