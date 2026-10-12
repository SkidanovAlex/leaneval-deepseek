import Mathlib.Analysis.SpecialFunctions.Pow.Real
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseFixB1.WB

theorem rpow_window {K R p : ℝ} (hK : 0 ≤ K) (hR : 0 < R) (hp : 0 < p) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ε₀ ≤ 1 ∧ ∀ t : ℝ, 0 < t → t ≤ ε₀ → K * t ^ p ≤ R := by
  have hden : (0 : ℝ) < K + 1 := by linarith
  have hbase : (0 : ℝ) < R / (K + 1) := by positivity
  refine ⟨min 1 ((R / (K + 1)) ^ (1 / p)), ?_, ?_, ?_⟩
  · exact lt_min one_pos (Real.rpow_pos_of_pos hbase _)
  · exact min_le_left _ _
  · intro t ht hte
    have htle : t ≤ (R / (K + 1)) ^ (1 / p) := le_trans hte (min_le_right _ _)
    have htp : t ^ p ≤ R / (K + 1) := by
      have h1 : t ^ p ≤ ((R / (K + 1)) ^ (1 / p)) ^ p :=
        Real.rpow_le_rpow (le_of_lt ht) htle (le_of_lt hp)
      have h2 : ((R / (K + 1)) ^ (1 / p)) ^ p = R / (K + 1) := by
        rw [← Real.rpow_mul (le_of_lt hbase)]
        have hmul : 1 / p * p = 1 := by field_simp
        rw [hmul, Real.rpow_one]
      linarith
    calc K * t ^ p ≤ K * (R / (K + 1)) := mul_le_mul_of_nonneg_left htp hK
      _ = K * R / (K + 1) := by ring
      _ ≤ R := by
        rw [div_le_iff₀ hden]
        nlinarith [hR]

end Work.BoseFixB1.WB
