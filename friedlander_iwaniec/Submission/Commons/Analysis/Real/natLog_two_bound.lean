import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real

namespace Commons.Analysis.Real

/-- For `x ≥ 1` and `η > 0`, `log x ≤ x ^ η / η`. -/
private lemma log_le_rpow_div_of_one_le {x : ℝ} (hx : 1 ≤ x) {η : ℝ} (hη : 0 < η) :
    Real.log x ≤ x ^ η / η := by
  have hxpos : 0 < x := lt_of_lt_of_le one_pos hx
  have htpos : 0 < x ^ η := Real.rpow_pos_of_pos hxpos η
  have h1 : Real.log (x ^ η) ≤ x ^ η := by
    have := Real.log_le_sub_one_of_pos htpos
    linarith
  rw [Real.log_rpow hxpos η] at h1
  rw [le_div_iff₀ hη]
  linear_combination h1

theorem natLog_two_bound (η : ℝ) (hη : 0 < η) :
    ∃ C : ℝ, 0 < C ∧ ∀ D : ℕ, 1 ≤ D → (Nat.log 2 D : ℝ) + 1 ≤ C * (D : ℝ) ^ η := by
  have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
  refine ⟨max 1 (2 / (Real.log 2 * η)), ?_, ?_⟩
  · exact lt_of_lt_of_le one_pos (le_max_left _ _)
  · intro D hD
    rcases eq_or_lt_of_le hD with hD1 | hD2
    · subst hD1
      have hlog1 : (Nat.log 2 1 : ℝ) = 0 := by rw [Nat.log_one_right]; norm_num
      rw [hlog1]
      norm_num
    · set k := Nat.log 2 D with hk
      have hDne : D ≠ 0 := by omega
      have hpow : 2 ^ k ≤ D := Nat.pow_log_le_self 2 hDne
      have hcast : ((2 : ℝ)) ^ k ≤ (D : ℝ) := by exact_mod_cast hpow
      have hDpos : (0 : ℝ) < (D : ℝ) := by exact_mod_cast (by omega : 0 < D)
      have hD1' : (1 : ℝ) ≤ (D : ℝ) := by exact_mod_cast hD
      have h2kpos : (0 : ℝ) < (2 : ℝ) ^ k := by positivity
      have hk_le : (k : ℝ) ≤ Real.log D / Real.log 2 := by
        have hlog := Real.log_le_log h2kpos hcast
        rw [Real.log_pow] at hlog
        rw [le_div_iff₀ hlog2pos]
        exact hlog
      have hD2' : (2 : ℝ) ≤ (D : ℝ) := by exact_mod_cast (by omega : 2 ≤ D)
      have hlogD_ge : Real.log 2 ≤ Real.log D := Real.log_le_log (by norm_num) hD2'
      have hratio_ge : 1 ≤ Real.log D / Real.log 2 := by
        rw [le_div_iff₀ hlog2pos]
        linarith
      have hstep1 : (k : ℝ) + 1 ≤ 2 * (Real.log D / Real.log 2) := by linarith
      have hlogD_bound : Real.log D ≤ (D : ℝ) ^ η / η := log_le_rpow_div_of_one_le hD1' hη
      have hstep2 : 2 * (Real.log D / Real.log 2) ≤ (max 1 (2 / (Real.log 2 * η))) * (D : ℝ) ^ η := by
        have hid : 2 * (((D : ℝ) ^ η / η) / Real.log 2)
            = (2 / (Real.log 2 * η)) * (D : ℝ) ^ η := by
          field_simp
        have hTnonneg : 0 ≤ (D : ℝ) ^ η := Real.rpow_nonneg hDpos.le η
        have hleC : 2 / (Real.log 2 * η) ≤ max 1 (2 / (Real.log 2 * η)) := le_max_right _ _
        have hA : 2 * (Real.log D / Real.log 2) ≤ 2 * (((D : ℝ) ^ η / η) / Real.log 2) := by
          have h1 : Real.log D / Real.log 2 ≤ ((D : ℝ) ^ η / η) / Real.log 2 :=
            div_le_div_of_nonneg_right hlogD_bound hlog2pos.le
          linarith
        rw [hid] at hA
        nlinarith [hA, hleC, hTnonneg]
      linarith

end Commons.Analysis.Real