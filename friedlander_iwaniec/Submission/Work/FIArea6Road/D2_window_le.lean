import Submission.Work.FIArea6Road.DivisorWindowDefs

namespace Work.FIArea6Road

open Finset
open scoped BigOperators

/-- A window bound for `D2(x) = ∑_{n ≤ x} τ(n)`: the number of divisors in an interval.
It is `(length) · log + O(√q)`, obtained from the Dirichlet-hyperbola asymptotic
`∑_{n≤x} τ(n) = x log x + (2γ-1)x + O(√x)`. -/
theorem D2_window_le :
    ∃ C : ℝ, 0 < C ∧ ∀ p q : ℕ, p ≤ q →
      D2 q - D2 p ≤ C * (((q : ℝ) - (p : ℝ)) + 1) * Real.log ((q : ℝ) + 2)
        + C * Real.sqrt (q : ℝ) := by
  obtain ⟨C₀, hC₀pos, hC₀⟩ := Commons.NumberTheory.DivisorSum.sum_divisor_count_asymptotic
  refine ⟨2 * C₀ + |2 * Real.eulerMascheroniConstant - 1| + 3, by positivity, ?_⟩
  intro p q hpq
  have hpR : (p : ℝ) ≤ (q : ℝ) := by exact_mod_cast hpq
  have hsq_le : Real.sqrt (p : ℝ) ≤ Real.sqrt (q : ℝ) := Real.sqrt_le_sqrt hpR
  -- upper bound for `D2 q`
  have hq_ub : D2 q ≤ (q : ℝ) * Real.log q + (2 * Real.eulerMascheroniConstant - 1) * (q : ℝ)
      + C₀ * Real.sqrt (q : ℝ) := by
    rcases Nat.eq_zero_or_pos q with hq0 | hq1
    · subst hq0; simp [D2_zero]
    · have h := (abs_le.mp (hC₀ q hq1)).2
      simp only [D2, tauR] at h ⊢
      linarith
  -- lower bound for `D2 p`
  have hp_lb : (p : ℝ) * Real.log p + (2 * Real.eulerMascheroniConstant - 1) * (p : ℝ)
      - C₀ * Real.sqrt (p : ℝ) ≤ D2 p := by
    rcases Nat.eq_zero_or_pos p with hp0 | hp1
    · subst hp0; simp [D2_zero]
    · have h := (abs_le.mp (hC₀ p hp1)).1
      simp only [D2, tauR] at h ⊢
      linarith
  -- bound on the difference of the main terms
  have hkey : (q : ℝ) * Real.log q - (p : ℝ) * Real.log p
      ≤ ((q : ℝ) - (p : ℝ)) * (Real.log ((q : ℝ) + 2) + 1) := by
    rcases Nat.eq_zero_or_pos p with hp0 | hp1
    · subst hp0
      have hqnn : (0 : ℝ) ≤ (q : ℝ) := by positivity
      have hle : Real.log (q : ℝ) ≤ Real.log ((q : ℝ) + 2) := by
        rcases Nat.eq_zero_or_pos q with hq0 | hq1
        · subst hq0
          simp only [Nat.cast_zero, Real.log_zero, zero_add]
          exact Real.log_nonneg (by norm_num)
        · exact Real.log_le_log (by positivity) (by linarith [show (1:ℝ) ≤ (q:ℝ) by exact_mod_cast hq1])
      have h1 : (q : ℝ) * Real.log (q : ℝ) ≤ (q : ℝ) * Real.log ((q : ℝ) + 2) :=
        mul_le_mul_of_nonneg_left hle hqnn
      simp only [Nat.cast_zero, mul_zero, Real.log_zero, sub_zero]
      nlinarith [h1, hqnn]
    · have hp1R : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp1
      have hq1R : (1 : ℝ) ≤ (q : ℝ) := le_trans hp1R hpR
      have hppos : (0 : ℝ) < (p : ℝ) := by linarith
      have hqpos : (0 : ℝ) < (q : ℝ) := by linarith
      have hratio : 0 < (q : ℝ) / (p : ℝ) := by positivity
      have hlogdiv : Real.log ((q : ℝ) / (p : ℝ)) = Real.log q - Real.log p :=
        Real.log_div (ne_of_gt hqpos) (ne_of_gt hppos)
      have hsplit : (q : ℝ) * Real.log q - (p : ℝ) * Real.log p
          = ((q : ℝ) - (p : ℝ)) * Real.log q + (p : ℝ) * Real.log ((q : ℝ) / (p : ℝ)) := by
        rw [hlogdiv]; ring
      have hb1 : (p : ℝ) * Real.log ((q : ℝ) / (p : ℝ)) ≤ (q : ℝ) - (p : ℝ) := by
        have h := Real.log_le_sub_one_of_pos hratio
        have h2 := mul_le_mul_of_nonneg_left h (le_of_lt hppos)
        have hpp : (p : ℝ) * ((q : ℝ) / (p : ℝ)) = (q : ℝ) := by field_simp
        nlinarith [h2, hpp]
      have hb2 : ((q : ℝ) - (p : ℝ)) * Real.log q
          ≤ ((q : ℝ) - (p : ℝ)) * Real.log ((q : ℝ) + 2) := by
        apply mul_le_mul_of_nonneg_left _
        · exact (by linarith : (0 : ℝ) ≤ (q : ℝ) - (p : ℝ))
        · exact Real.log_le_log hqpos (by linarith)
      rw [hsplit]
      nlinarith [hb1, hb2]
  -- combine
  rcases Nat.eq_zero_or_pos q with hq0 | hq1
  · subst hq0
    have hpz : p = 0 := Nat.le_zero.mp hpq
    subst hpz
    have hD : D2 0 - D2 0 = 0 := by rw [D2_zero]; ring
    rw [hD]
    have hCnn : (0:ℝ) ≤ 2 * C₀ + |2 * Real.eulerMascheroniConstant - 1| + 3 := by
      linarith [hC₀pos, abs_nonneg (2 * Real.eulerMascheroniConstant - 1)]
    refine add_nonneg (mul_nonneg (mul_nonneg hCnn ?_) ?_) (mul_nonneg hCnn (Real.sqrt_nonneg _))
    · norm_num
    · apply Real.log_nonneg; norm_num
  have hq1R : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq1
  have hlogq_ge1 : 1 ≤ Real.log ((q : ℝ) + 2) := by
    rw [Real.le_log_iff_exp_le (by positivity)]
    linarith [Real.exp_one_lt_three, hq1R]
  have hlogq_nonneg : 0 ≤ Real.log ((q : ℝ) + 2) := le_trans zero_le_one hlogq_ge1
  have hlen_nonneg : (0 : ℝ) ≤ (q : ℝ) - (p : ℝ) := by linarith
  -- the difference of sums
  have hdiff : D2 q - D2 p
      ≤ ((q : ℝ) - (p : ℝ)) * (Real.log ((q : ℝ) + 2) + 1)
        + |2 * Real.eulerMascheroniConstant - 1| * ((q : ℝ) - (p : ℝ))
        + C₀ * (Real.sqrt (q : ℝ) + Real.sqrt (p : ℝ)) := by
    have h1 : D2 q - D2 p
        ≤ ((q : ℝ) * Real.log q - (p : ℝ) * Real.log p)
          + (2 * Real.eulerMascheroniConstant - 1) * ((q : ℝ) - (p : ℝ))
          + C₀ * (Real.sqrt (q : ℝ) + Real.sqrt (p : ℝ)) := by
      nlinarith [hq_ub, hp_lb]
    refine le_trans h1 ?_
    have h2 : (2 * Real.eulerMascheroniConstant - 1) * ((q : ℝ) - (p : ℝ))
        ≤ |2 * Real.eulerMascheroniConstant - 1| * ((q : ℝ) - (p : ℝ)) :=
      mul_le_mul_of_nonneg_right (le_abs_self _) hlen_nonneg
    linarith [hkey, h2]
  -- final assembly
  have hsqrt_sum : Real.sqrt (q : ℝ) + Real.sqrt (p : ℝ) ≤ 2 * Real.sqrt (q : ℝ) := by linarith
  have hstep1 : ((q : ℝ) - (p : ℝ)) * (Real.log ((q : ℝ) + 2) + 1)
        + |2 * Real.eulerMascheroniConstant - 1| * ((q : ℝ) - (p : ℝ))
      ≤ ((q : ℝ) - (p : ℝ)) * ((|2 * Real.eulerMascheroniConstant - 1| + 2) * Real.log ((q : ℝ) + 2)) := by
    have : Real.log ((q : ℝ) + 2) + 1 + |2 * Real.eulerMascheroniConstant - 1|
        ≤ (|2 * Real.eulerMascheroniConstant - 1| + 2) * Real.log ((q : ℝ) + 2) := by
      nlinarith [hlogq_ge1, abs_nonneg (2 * Real.eulerMascheroniConstant - 1)]
    nlinarith [hlen_nonneg, this]
  have hK1 : |2 * Real.eulerMascheroniConstant - 1| + 2
      ≤ 2 * C₀ + |2 * Real.eulerMascheroniConstant - 1| + 3 := by
    linarith [hC₀pos]
  have hK2 : 2 * C₀ ≤ 2 * C₀ + |2 * Real.eulerMascheroniConstant - 1| + 3 := by
    linarith [abs_nonneg (2 * Real.eulerMascheroniConstant - 1)]
  have hKnn : (0 : ℝ) ≤ 2 * C₀ + |2 * Real.eulerMascheroniConstant - 1| + 3 := by
    linarith [hC₀pos, abs_nonneg (2 * Real.eulerMascheroniConstant - 1)]
  have hfin : ((q : ℝ) - (p : ℝ)) * ((|2 * Real.eulerMascheroniConstant - 1| + 2) * Real.log ((q : ℝ) + 2))
        + C₀ * (2 * Real.sqrt (q : ℝ))
      ≤ (2 * C₀ + |2 * Real.eulerMascheroniConstant - 1| + 3) * (((q : ℝ) - (p : ℝ)) + 1)
          * Real.log ((q : ℝ) + 2)
        + (2 * C₀ + |2 * Real.eulerMascheroniConstant - 1| + 3) * Real.sqrt (q : ℝ) := by
    have ha : ((q : ℝ) - (p : ℝ)) * ((|2 * Real.eulerMascheroniConstant - 1| + 2) * Real.log ((q : ℝ) + 2))
        ≤ (2 * C₀ + |2 * Real.eulerMascheroniConstant - 1| + 3) * (((q : ℝ) - (p : ℝ)) + 1)
            * Real.log ((q : ℝ) + 2) := by
      have h1 : ((q : ℝ) - (p : ℝ)) * ((|2 * Real.eulerMascheroniConstant - 1| + 2) * Real.log ((q : ℝ) + 2))
          ≤ ((q : ℝ) - (p : ℝ)) * ((2 * C₀ + |2 * Real.eulerMascheroniConstant - 1| + 3) * Real.log ((q : ℝ) + 2)) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hK1 hlogq_nonneg) hlen_nonneg
      have h2 : ((q : ℝ) - (p : ℝ)) * ((2 * C₀ + |2 * Real.eulerMascheroniConstant - 1| + 3) * Real.log ((q : ℝ) + 2))
          ≤ (2 * C₀ + |2 * Real.eulerMascheroniConstant - 1| + 3) * (((q : ℝ) - (p : ℝ)) + 1)
              * Real.log ((q : ℝ) + 2) := by
        nlinarith [hKnn, hlogq_nonneg]
      linarith [h1, h2]
    have hb : C₀ * (2 * Real.sqrt (q : ℝ))
        ≤ (2 * C₀ + |2 * Real.eulerMascheroniConstant - 1| + 3) * Real.sqrt (q : ℝ) := by
      have := mul_le_mul_of_nonneg_right hK2 (Real.sqrt_nonneg (q : ℝ))
      nlinarith
    linarith [ha, hb]
  calc D2 q - D2 p
      ≤ ((q : ℝ) - (p : ℝ)) * ((|2 * Real.eulerMascheroniConstant - 1| + 2) * Real.log ((q : ℝ) + 2))
          + C₀ * (2 * Real.sqrt (q : ℝ)) := by
        have hss : C₀ * (Real.sqrt (q : ℝ) + Real.sqrt (p : ℝ)) ≤ C₀ * (2 * Real.sqrt (q : ℝ)) :=
          mul_le_mul_of_nonneg_left hsqrt_sum (le_of_lt hC₀pos)
        linarith [hdiff, hstep1, hss]
    _ ≤ (2 * C₀ + |2 * Real.eulerMascheroniConstant - 1| + 3) * (((q : ℝ) - (p : ℝ)) + 1)
          * Real.log ((q : ℝ) + 2)
        + (2 * C₀ + |2 * Real.eulerMascheroniConstant - 1| + 3) * Real.sqrt (q : ℝ) := hfin

end Work.FIArea6Road
