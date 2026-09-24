import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.ExpLog

/-- For every `c > 0`, eventually `log X ≤ X^c` (as `X → ∞`). -/
lemma log_le_rpow_eventually {c : ℝ} (hc : 0 < c) :
    ∃ R : ℝ, 1 ≤ R ∧ ∀ X : ℝ, R ≤ X → Real.log X ≤ X ^ c := by
  let t : ℝ := (2 / c) ^ (2 / c)
  refine ⟨max 1 t, le_max_left 1 t, ?_⟩
  intro X hX
  have hX1 : 1 ≤ X := le_trans (le_max_left 1 t) hX
  have hX0 : 0 < X := lt_of_lt_of_le zero_lt_one hX1
  have hc2 : 0 < c / 2 := by positivity
  have ht0 : 0 ≤ t := by
    dsimp [t]
    exact Real.rpow_nonneg (by positivity : (0 : ℝ) ≤ 2 / c) _
  have hXt : t ≤ X := le_trans (le_max_right 1 t) hX
  have htp : t ^ (c / 2) = (2 / c : ℝ) := by
    dsimp [t]
    rw [← Real.rpow_mul (by positivity : (0 : ℝ) ≤ 2 / c)]
    have hprod : (2 / c) * (c / 2) = 1 := by field_simp [hc.ne']
    rw [hprod, Real.rpow_one]
  have h2le : (2 / c : ℝ) ≤ X ^ (c / 2) := by
    calc
      (2 / c : ℝ) = t ^ (c / 2) := htp.symm
      _ ≤ X ^ (c / 2) := Real.rpow_le_rpow ht0 hXt hc2.le
  have hlog : Real.log X ≤ X ^ (c / 2) / (c / 2) := Real.log_le_rpow_div hX0.le hc2
  calc
    Real.log X ≤ X ^ (c / 2) / (c / 2) := hlog
    _ = X ^ (c / 2) * (2 / c) := by field_simp [hc.ne']
    _ ≤ X ^ (c / 2) * X ^ (c / 2) := by
      exact mul_le_mul_of_nonneg_left h2le (Real.rpow_nonneg hX0.le _)
    _ = X ^ (c / 2 + c / 2) := (Real.rpow_add hX0 (c / 2) (c / 2)).symm
    _ = X ^ c := by congr 1; ring

end Commons.Analysis.ExpLog