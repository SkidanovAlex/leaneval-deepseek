import Mathlib

namespace Work.LinnikAreas2.S3HardAux

/-- Pointwise bound: `1/(q·√q) ≤ 4(1/√q − 1/√(q+1))` for `q ≥ 1`.
The right-hand side telescopes, and `4(1 − 1/√(Q+1)) ≤ 4`. -/
lemma inv_sqrt_three_halves_step (q : ℕ) (hq : 1 ≤ q) :
    1 / ((q : ℝ) * Real.sqrt (q : ℝ)) ≤
      4 * (1 / Real.sqrt (q : ℝ) - 1 / Real.sqrt ((q + 1 : ℕ) : ℝ)) := by
  have hqR : (0 : ℝ) < (q : ℝ) := by exact_mod_cast hq
  have hq1 : (1 : ℝ) ≤ (q : ℝ) := by exact_mod_cast hq
  have hspos : 0 < Real.sqrt (q : ℝ) := Real.sqrt_pos.2 hqR
  have hs2 : Real.sqrt (q : ℝ) ^ 2 = (q : ℝ) := Real.sq_sqrt (le_of_lt hqR)
  have ht2 : Real.sqrt ((q + 1 : ℕ) : ℝ) ^ 2 = (q : ℝ) + 1 := by
    rw [Real.sq_sqrt (by positivity)]; push_cast; ring
  have key : 4 * (1 / Real.sqrt (q : ℝ) - 1 / Real.sqrt ((q + 1 : ℕ) : ℝ))
      = 4 / (Real.sqrt (q : ℝ) * Real.sqrt ((q + 1 : ℕ) : ℝ)
              * (Real.sqrt (q : ℝ) + Real.sqrt ((q + 1 : ℕ) : ℝ))) := by
    field_simp
    nlinarith [hs2, ht2]
  rw [key]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  have hts_sq : (Real.sqrt ((q + 1 : ℕ) : ℝ) * Real.sqrt (q : ℝ)) ^ 2
      ≤ ((q : ℝ) + 1) ^ 2 := by
    rw [mul_pow, ht2, hs2]; nlinarith [hqR]
  have hts : Real.sqrt ((q + 1 : ℕ) : ℝ) * Real.sqrt (q : ℝ) ≤ (q : ℝ) + 1 := by
    have h1 : |Real.sqrt ((q + 1 : ℕ) : ℝ) * Real.sqrt (q : ℝ)| ≤ |(q : ℝ) + 1| :=
      (sq_le_sq).mp hts_sq
    rwa [abs_of_nonneg (by positivity), abs_of_nonneg (by positivity)] at h1
  have hmain : Real.sqrt ((q + 1 : ℕ) : ℝ)
        * (Real.sqrt (q : ℝ) + Real.sqrt ((q + 1 : ℕ) : ℝ)) ≤ 4 * (q : ℝ) := by
    have hexp : Real.sqrt ((q + 1 : ℕ) : ℝ)
          * (Real.sqrt (q : ℝ) + Real.sqrt ((q + 1 : ℕ) : ℝ))
        = Real.sqrt ((q + 1 : ℕ) : ℝ) * Real.sqrt (q : ℝ)
          + Real.sqrt ((q + 1 : ℕ) : ℝ) ^ 2 := by ring
    rw [hexp]; nlinarith [hts, ht2, hq1]
  have := mul_le_mul_of_nonneg_left hmain (le_of_lt hspos)
  nlinarith [this]

theorem sum_inv_sqrt_three_halves_le (Q : ℕ) :
    (∑ q ∈ Finset.Icc 1 Q, 1 / ((q : ℝ) * Real.sqrt (q : ℝ))) ≤ 4 := by
  rcases Q with _ | Q
  · simp
  · have hstep := fun q hq => inv_sqrt_three_halves_step q hq
    calc (∑ q ∈ Finset.Icc 1 (Q + 1), 1 / ((q : ℝ) * Real.sqrt (q : ℝ)))
        ≤ ∑ q ∈ Finset.Icc 1 (Q + 1),
            ((fun i : ℕ => -(4 / Real.sqrt (i : ℝ))) (q + 1)
              - (fun i : ℕ => -(4 / Real.sqrt (i : ℝ))) q) := by
          apply Finset.sum_le_sum
          intro q hq
          rw [Finset.mem_Icc] at hq
          have h := hstep q hq.1
          have heq : (fun i : ℕ => -(4 / Real.sqrt (i : ℝ))) (q + 1)
                - (fun i : ℕ => -(4 / Real.sqrt (i : ℝ))) q
              = 4 * (1 / Real.sqrt (q : ℝ) - 1 / Real.sqrt ((q + 1 : ℕ) : ℝ)) := by
            simp only []; ring
          rw [heq]; exact h
      _ = (fun i : ℕ => -(4 / Real.sqrt (i : ℝ))) (Q + 1 + 1)
            - (fun i : ℕ => -(4 / Real.sqrt (i : ℝ))) 1 :=
          Finset.sum_Icc_sub (m := 1) (n := Q + 1) (by omega)
            (fun i : ℕ => -(4 / Real.sqrt (i : ℝ)))
      _ ≤ 4 := by
          simp only []
          rw [show Real.sqrt (((1 : ℕ) : ℝ)) = 1 by norm_num]
          have hpos : (0 : ℝ) ≤ 4 / Real.sqrt (((Q + 1) + 1 : ℕ) : ℝ) := by positivity
          linarith

end Work.LinnikAreas2.S3HardAux
