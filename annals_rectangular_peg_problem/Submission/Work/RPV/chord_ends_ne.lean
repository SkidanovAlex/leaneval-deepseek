import Mathlib
import Submission.Work.RPV.Defs

namespace Work.RPV

/-- Two parameters `t + r` and `t - r` symmetric about `t` with `0 < r < π/2` give distinct points
of the curve `CI.c τ` (`τ ∈ [0,1]`), because `CI.c τ` is injective modulo `2π`: a coincidence would
force `2r ∈ 2πℤ`, i.e. `r` an integral multiple of `π`, impossible when `0 < r < π/2`. -/
theorem chord_ends_ne (CI : CurveIsotopy) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) 1)
    {t : ℝ} {r : ℝ} (hr : r ∈ Set.Ioc (0 : ℝ) (Real.pi / 2)) :
    CI.c τ (t + r) ≠ CI.c τ (t - r) := by
  intro h
  obtain ⟨m, hm⟩ := CI.inj τ hτ (t + r) (t - r) h
  -- `hm : t - r = t + r + 2 * π * ↑m`, hence `π * (-m) = r`.
  have hrπ : r < Real.pi := lt_of_le_of_lt hr.2 (by linarith [Real.pi_pos])
  have h2 : Real.pi * (-(m : ℝ)) = r := by linarith
  have hmul : 0 < Real.pi * (-(m : ℝ)) := by rw [h2]; exact hr.1
  have hmul' : Real.pi * (-(m : ℝ)) < Real.pi * 1 := by rw [h2, mul_one]; exact hrπ
  have hpos : 0 < -(m : ℝ) := by
    rcases (mul_pos_iff.mp hmul) with ⟨-, h3⟩ | ⟨h3, -⟩
    · exact h3
    · exact absurd h3 (not_lt.mpr Real.pi_pos.le)
  have hlt : -(m : ℝ) < 1 := by nlinarith [hmul', Real.pi_pos]
  have h3 : (0 : ℤ) < -m := by exact_mod_cast hpos
  have h4 : -m < 1 := by exact_mod_cast hlt
  omega

end Work.RPV
