import Mathlib
import Submission.Commons.NumberTheory.DivisorBound.card_divisors_le_exp_log_div_loglog
import Submission.Commons.Analysis.SpecialFunctions.monotoneOn_div_log_rpow

namespace Commons.NumberTheory.ArithmeticFunction

theorem card_divisors_le_exp_log_div_loglog : ∃ C : ℝ, 0 < C ∧ ∀ n N : ℕ, 1 ≤ n → n ≤ N → ((n.divisors.card : ℝ)) ≤ Real.exp (C * Real.log (N : ℝ) / Real.log (Real.log (N : ℝ) + 2) + C) := by
  obtain ⟨C0, hC0pos, hC0⟩ := Commons.NumberTheory.DivisorBound.card_divisors_le_exp_log_div_loglog
  refine ⟨max (2 * C0) 4, ?_, ?_⟩
  · exact lt_of_lt_of_le (by norm_num : (0:ℝ) < 4) (le_max_right _ _)
  · intro n N hn hN
    have hN1 : 1 ≤ N := le_trans hn hN
    have hNreal : (1:ℝ) ≤ (N:ℝ) := by exact_mod_cast hN1
    have hlogN_nonneg : 0 ≤ Real.log (N:ℝ) := Real.log_nonneg hNreal
    have hlogNp2 : 0 < Real.log (Real.log (N:ℝ) + 2) := Real.log_pos (by linarith)
    have hfN_nonneg : 0 ≤ Real.log (N:ℝ) / Real.log (Real.log (N:ℝ) + 2) :=
      div_nonneg hlogN_nonneg (le_of_lt hlogNp2)
    have hC4 : (4:ℝ) ≤ max (2 * C0) 4 := le_max_right _ _
    have hC_nonneg : (0:ℝ) ≤ max (2 * C0) 4 := le_trans (by norm_num) hC4
    by_cases hn9 : n ≤ 9
    · -- small n
      have hdn : (n.divisors.card : ℝ) ≤ (n:ℝ) := by
        exact_mod_cast Nat.card_divisors_le_self n
      have hn9R : (n:ℝ) ≤ 9 := by exact_mod_cast hn9
      have hlog9 : Real.log (9:ℝ) ≤ 4 := by
        have h3 : Real.log (3:ℝ) ≤ (3:ℝ) - 1 := Real.log_le_sub_one_of_pos (by norm_num)
        have h9 : Real.log (9:ℝ) = 2 * Real.log 3 := by
          rw [show (9:ℝ) = 3 ^ 2 by norm_num, Real.log_pow]
          norm_num
        rw [h9]; linarith
      have hlog9C : Real.log (9:ℝ) ≤ max (2 * C0) 4 := le_trans hlog9 hC4
      have h9le : (9:ℝ) ≤ Real.exp (max (2 * C0) 4) := by
        calc (9:ℝ) = Real.exp (Real.log 9) := (Real.exp_log (by norm_num)).symm
          _ ≤ Real.exp (max (2 * C0) 4) := Real.exp_le_exp.mpr hlog9C
      have hexp : Real.exp (max (2 * C0) 4) ≤
          Real.exp (max (2 * C0) 4 * Real.log (N:ℝ) / Real.log (Real.log (N:ℝ) + 2) + max (2 * C0) 4) := by
        apply Real.exp_le_exp.mpr
        have hnn : 0 ≤ max (2 * C0) 4 * Real.log (N:ℝ) / Real.log (Real.log (N:ℝ) + 2) :=
          div_nonneg (mul_nonneg hC_nonneg hlogN_nonneg) (le_of_lt hlogNp2)
        linarith
      linarith [hdn, hn9R, h9le, hexp]
    · -- large n
      have hn9' : 9 < n := not_le.mp hn9
      have hn3 : 3 ≤ n := by omega
      have hnpos : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
      have hnR : (10:ℝ) ≤ (n:ℝ) := by exact_mod_cast (by omega : 10 ≤ n)
      have hbound := hC0 n hn3
      have hLpos : 0 < Real.log (n:ℝ) := Real.log_pos (by linarith : (1:ℝ) < (n:ℝ))
      have hexp2 : Real.exp 2 < 10 := by
        rw [show (2:ℝ) = 1 + 1 by norm_num, Real.exp_add]
        nlinarith [Real.exp_one_lt_three, Real.exp_pos 1]
      have hlog10 : (2:ℝ) < Real.log 10 :=
        (Real.lt_log_iff_exp_lt (by norm_num : (0:ℝ) < 10)).mpr hexp2
      have hLgt2 : (2:ℝ) < Real.log (n:ℝ) :=
        lt_of_lt_of_le hlog10 (Real.log_le_log (by norm_num) hnR)
      have hLlpos : 0 < Real.log (Real.log (n:ℝ)) := Real.log_pos (by linarith)
      have hLsq : Real.log (n:ℝ) + 2 ≤ (Real.log (n:ℝ))^2 := by
        have hfac : 0 ≤ (Real.log (n:ℝ) - 2) * (Real.log (n:ℝ) + 1) :=
          mul_nonneg (by linarith) (by linarith)
        nlinarith [hfac]
      have hdenpos : 0 < Real.log (Real.log (n:ℝ) + 2) := Real.log_pos (by linarith)
      have hlogden : Real.log (Real.log (n:ℝ) + 2) ≤ 2 * Real.log (Real.log (n:ℝ)) := by
        have h1 : Real.log (Real.log (n:ℝ) + 2) ≤ Real.log ((Real.log (n:ℝ))^2) :=
          Real.log_le_log (by linarith) hLsq
        rw [Real.log_pow] at h1
        simpa using h1
      have hratio : Real.log (n:ℝ) / Real.log (Real.log (n:ℝ))
          ≤ 2 * (Real.log (n:ℝ) / Real.log (Real.log (n:ℝ) + 2)) := by
        rw [show 2 * (Real.log (n:ℝ) / Real.log (Real.log (n:ℝ) + 2))
              = 2 * Real.log (n:ℝ) / Real.log (Real.log (n:ℝ) + 2) by ring]
        rw [div_le_div_iff₀ hLlpos hdenpos]
        have h := mul_le_mul_of_nonneg_left hlogden (le_of_lt hLpos)
        nlinarith [h]
      have hphi : Real.log (n:ℝ) / Real.log (Real.log (n:ℝ) + 2)
          ≤ Real.log (N:ℝ) / Real.log (Real.log (N:ℝ) + 2) := by
        have hlogle : Real.log (n:ℝ) ≤ Real.log (N:ℝ) :=
          Real.log_le_log hnpos (by exact_mod_cast hN)
        have hmono := Commons.Analysis.SpecialFunctions.monotoneOn_div_log_rpow 1 le_rfl
        have h1 : Real.log (n:ℝ) ∈ Set.Ici (0:ℝ) := le_of_lt hLpos
        have h2 : Real.log (N:ℝ) ∈ Set.Ici (0:ℝ) := hlogN_nonneg
        have key := hmono h1 h2 hlogle
        simp only [Real.rpow_one] at key
        rw [show (2:ℝ) + Real.log (n:ℝ) = Real.log (n:ℝ) + 2 by ring,
            show (2:ℝ) + Real.log (N:ℝ) = Real.log (N:ℝ) + 2 by ring] at key
        exact key
      have hExpArg : C0 * Real.log (n:ℝ) / Real.log (Real.log (n:ℝ))
          ≤ max (2 * C0) 4 * Real.log (N:ℝ) / Real.log (Real.log (N:ℝ) + 2) := by
        have h1 : C0 * Real.log (n:ℝ) / Real.log (Real.log (n:ℝ))
            = C0 * (Real.log (n:ℝ) / Real.log (Real.log (n:ℝ))) := mul_div_assoc _ _ _
        have h2 : max (2 * C0) 4 * Real.log (N:ℝ) / Real.log (Real.log (N:ℝ) + 2)
            = max (2 * C0) 4 * (Real.log (N:ℝ) / Real.log (Real.log (N:ℝ) + 2)) :=
          mul_div_assoc _ _ _
        rw [h1, h2]
        calc C0 * (Real.log (n:ℝ) / Real.log (Real.log (n:ℝ)))
            ≤ C0 * (2 * (Real.log (n:ℝ) / Real.log (Real.log (n:ℝ) + 2))) :=
              mul_le_mul_of_nonneg_left hratio hC0pos.le
          _ = 2 * C0 * (Real.log (n:ℝ) / Real.log (Real.log (n:ℝ) + 2)) := by ring
          _ ≤ 2 * C0 * (Real.log (N:ℝ) / Real.log (Real.log (N:ℝ) + 2)) :=
              mul_le_mul_of_nonneg_left hphi (by linarith [hC0pos])
          _ ≤ max (2 * C0) 4 * (Real.log (N:ℝ) / Real.log (Real.log (N:ℝ) + 2)) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) hfN_nonneg
      calc (n.divisors.card : ℝ)
          ≤ Real.exp (C0 * Real.log (n:ℝ) / Real.log (Real.log (n:ℝ))) := hbound
        _ ≤ Real.exp (max (2 * C0) 4 * Real.log (N:ℝ) / Real.log (Real.log (N:ℝ) + 2)) :=
            Real.exp_le_exp.mpr hExpArg
        _ ≤ Real.exp (max (2 * C0) 4 * Real.log (N:ℝ) / Real.log (Real.log (N:ℝ) + 2) + max (2 * C0) 4) :=
            Real.exp_le_exp.mpr (le_add_of_nonneg_right hC_nonneg)

end Commons.NumberTheory.ArithmeticFunction
