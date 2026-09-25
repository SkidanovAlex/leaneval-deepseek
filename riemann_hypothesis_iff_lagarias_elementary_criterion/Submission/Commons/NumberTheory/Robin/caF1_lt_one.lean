import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Commons.NumberTheory.Robin

lemma caF1_lt_one {p : ℕ} (hp : 2 ≤ p) :
    Real.log ((((p : ℝ) ^ (2 : ℕ)) - 1) / (((p : ℝ) ^ (2 : ℕ)) - (p : ℝ))) / Real.log (p : ℝ) < 1 := by
  have hp1r : (1 : ℝ) < (p : ℝ) := by exact_mod_cast (by omega : 1 < p)
  have hp0 : (0 : ℝ) < (p : ℝ) := by linarith
  have hpne : (p : ℝ) ≠ 0 := ne_of_gt hp0
  have hlogp : 0 < Real.log (p : ℝ) := Real.log_pos hp1r
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by
    have hne : (p : ℝ) ≠ 1 := by exact_mod_cast (by omega : p ≠ 1)
    exact sub_ne_zero.mpr hne
  have hmain : (((p : ℝ) ^ (2 : ℕ)) - 1) / (((p : ℝ) ^ (2 : ℕ)) - (p : ℝ)) = 1 + 1 / (p : ℝ) := by
    rw [pow_two]
    have hnum : (p : ℝ) * (p : ℝ) - 1 = ((p : ℝ) + 1) * ((p : ℝ) - 1) := by ring
    have hden : (p : ℝ) * (p : ℝ) - (p : ℝ) = (p : ℝ) * ((p : ℝ) - 1) := by ring
    rw [hnum, hden]
    field_simp
  rw [hmain]
  have hlt : Real.log (1 + 1 / (p : ℝ)) < Real.log (p : ℝ) := by
    apply Real.log_lt_log (by positivity)
    have h1p : 1 / (p : ℝ) < 1 := by
      rw [div_lt_iff₀ hp0]; linarith
    have h2 : 1 + 1 / (p : ℝ) < 2 := by linarith
    have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp
    linarith
  exact (div_lt_one hlogp).mpr hlt

end Commons.NumberTheory.Robin