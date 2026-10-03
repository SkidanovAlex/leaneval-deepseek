import Mathlib

namespace Work.FIArea7

/-- The summand of the series. -/
private noncomputable def F (n : ℕ) : ℝ := 1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2)

/-- Auxiliary comparison sequence `1 / log ((j : ℝ) + 2)`, whose first difference
dominates `F (j+2)`. -/
private noncomputable def G (j : ℕ) : ℝ := 1 / Real.log ((j : ℝ) + 2)

/-- For `x ≥ 2`, `1/((x+1) log(x+1)^2) ≤ 1/log x - 1/log (x+1)`. -/
private lemma key_ineq (x : ℝ) (hx : 2 ≤ x) :
    1 / ((x + 1) * Real.log (x + 1) ^ 2) ≤ 1 / Real.log x - 1 / Real.log (x + 1) := by
  have hx1 : (1 : ℝ) < x := by linarith
  have hx0 : (0 : ℝ) < x := by linarith
  have hxne : x ≠ 0 := ne_of_gt hx0
  have hx1ne : x + 1 ≠ 0 := by positivity
  have hlx : 0 < Real.log x := Real.log_pos hx1
  have hlx1 : 0 < Real.log (x + 1) := Real.log_pos (by linarith)
  have hlog := Real.one_sub_inv_le_log_of_pos (show (0:ℝ) < (x + 1) / x by positivity)
  have hsimp : 1 - ((x + 1) / x)⁻¹ = 1 / (x + 1) := by
    rw [inv_div]; field_simp; ring
  rw [hsimp, Real.log_div hx1ne hxne] at hlog
  have hstep : 1 ≤ (x + 1) * (Real.log (x + 1) - Real.log x) := by
    have h := mul_le_mul_of_nonneg_left hlog (by linarith : (0:ℝ) ≤ x + 1)
    have hone : (x + 1) * (1 / (x + 1)) = 1 := by
      rw [mul_one_div, div_self hx1ne]
    linarith [h, hone]
  have hB : Real.log x ≤ Real.log (x + 1) := Real.log_le_log hx0 (by linarith)
  have hcross : Real.log x ≤ (x + 1) * (Real.log (x + 1) - Real.log x) * Real.log (x + 1) := by
    have hmul := mul_le_mul_of_nonneg_right hstep (le_of_lt hlx1)
    rw [one_mul] at hmul
    linarith [hB, hmul]
  have hden : (0 : ℝ) < (x + 1) * Real.log (x + 1) ^ 2 :=
    mul_pos (by linarith) (pow_pos hlx1 2)
  rw [div_le_iff₀ hden]
  have hfac : (1 / Real.log x - 1 / Real.log (x + 1)) * ((x + 1) * Real.log (x + 1) ^ 2)
      = (x + 1) * (Real.log (x + 1) - Real.log x) * Real.log (x + 1) / Real.log x := by
    field_simp
  rw [hfac, le_div_iff₀ hlx]
  linarith [hcross]

/-- The series `∑_{n ≥ 2} 1/(n (log n)^2)` is bounded by an absolute constant.
(A dyadic grouping, or the integral test `AntitoneOn.sum_le_integral` with the antiderivative
`-1/log`, gives a constant such as `8`.) -/
theorem psiLogSeries : ∃ C : ℝ, 0 < C ∧ ∀ N : ℕ,
      ∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2) ≤ C := by
  have h2 : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  have hC : (0:ℝ) < 1 / (2 * Real.log 2 ^ 2) + 1 / Real.log 2 := by
    apply add_pos
    · apply div_pos one_pos
      exact mul_pos (by norm_num) (pow_pos h2 2)
    · exact div_pos one_pos h2
  refine ⟨1 / (2 * Real.log 2 ^ 2) + 1 / Real.log 2, hC, ?_⟩
  intro N
  have hF : ∀ n, F n = 1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2) := fun n => rfl
  rw [show (∑ n ∈ Finset.Icc 2 N, 1 / ((n : ℝ) * Real.log (n : ℝ) ^ 2))
        = ∑ n ∈ Finset.Icc 2 N, F n from
      Finset.sum_congr rfl (fun n _ => (hF n).symm)]
  rcases lt_or_ge N 2 with hN | hN
  · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
    exact hC.le
  · have hsum : ∑ n ∈ Finset.Icc 2 N, F n
        = ∑ k ∈ Finset.range (N - 2), F (2 + (k + 1)) + F 2 := by
      rw [← Finset.Ico_add_one_right_eq_Icc 2 N]
      rw [Finset.sum_Ico_eq_sum_range]
      rw [show N + 1 - 2 = N - 1 by omega,
          show N - 1 = (N - 2) + 1 by omega,
          Finset.sum_range_succ' (fun k => F (2 + k)) (N - 2)]
    have hpt : ∀ k ∈ Finset.range (N - 2), F (2 + (k + 1)) ≤ G k - G (k + 1) := by
      intro k _
      have hk2 : (2:ℝ) ≤ (k:ℝ) + 2 := by
        have : (0:ℝ) ≤ (k:ℝ) := Nat.cast_nonneg k
        linarith
      have key := key_ineq ((k:ℝ) + 2) hk2
      have e1 : ((2 + (k + 1) : ℕ) : ℝ) = (k:ℝ) + 3 := by push_cast; ring
      have e2 : (((k + 1 : ℕ) : ℝ) + 2) = (k:ℝ) + 3 := by push_cast; ring
      have e3 : (k:ℝ) + 2 + 1 = (k:ℝ) + 3 := by ring
      rw [e3] at key
      dsimp only [F, G]
      rw [e1, e2]
      exact key
    have htel : ∑ k ∈ Finset.range (N - 2), (G k - G (k + 1))
        = 1 / Real.log 2 - 1 / Real.log (N:ℝ) := by
      rw [Finset.sum_range_sub']
      have h0 : G 0 = 1 / Real.log 2 := by dsimp only [G]; norm_num
      have hN2 : G (N - 2) = 1 / Real.log (N:ℝ) := by
        have hcast : ((N - 2 : ℕ) : ℝ) + 2 = (N:ℝ) := by
          rw [Nat.cast_sub hN]; ring
        dsimp only [G]
        rw [hcast]
      rw [h0, hN2]
    rw [hsum]
    have hbound : ∑ k ∈ Finset.range (N - 2), F (2 + (k + 1))
        ≤ ∑ k ∈ Finset.range (N - 2), (G k - G (k + 1)) := Finset.sum_le_sum hpt
    rw [htel] at hbound
    calc ∑ k ∈ Finset.range (N - 2), F (2 + (k + 1)) + F 2
        ≤ (1 / Real.log 2 - 1 / Real.log (N:ℝ)) + F 2 := by linarith [hbound]
      _ ≤ 1 / (2 * Real.log 2 ^ 2) + 1 / Real.log 2 := by
          have hF2 : F 2 = 1 / (2 * Real.log 2 ^ 2) := by dsimp only [F]; norm_num
          have hlogN : (0:ℝ) ≤ 1 / Real.log (N:ℝ) :=
            div_nonneg zero_le_one
              (Real.log_nonneg (by exact_mod_cast (show (1:ℕ) ≤ N by omega)))
          rw [hF2]
          linarith [hlogN]

end Work.FIArea7
