import Mathlib

namespace Work.TMC16Core.Assembly

/-- Arithmetic core for the "bad" (small `j`) branch of the Ten Martini counting:
if `j ≤ 5 qn / 8`, `5 d < qn` with `d = min j (qn - j)`, and the logarithmic
budget `hlog` holds, then the exponential comparison goes through. -/
theorem res_arith_bad {L εf C : ℝ} (hL : 0 < L) (hεf : 0 < εf) (hC : 0 ≤ C) {qn j d : ℕ}
    (hj : (j : ℝ) ≤ 5 * (qn : ℝ) / 8)
    (hd : (d : ℝ) = min (j : ℝ) ((qn : ℝ) - (j : ℝ)))
    (hbad : 5 * (d : ℝ) < (qn : ℝ))
    (hlog : Real.log (2 * C * (1 + 2 * (qn : ℝ))) ≤
      (19 / 80) * L * (qn : ℝ) + (14 / 5) * εf * (qn : ℝ) + L + εf) :
    2 * (C * (1 + 2 * (qn : ℝ))) * Real.exp (((qn : ℝ) - 1 + (j : ℝ)) * (L + εf)) ≤
      Real.exp ((2 * (qn : ℝ)) * (23 * L / 32 + 2 * εf)) := by
  have hQ0 : (0:ℝ) ≤ (qn : ℝ) := by positivity
  have hLf : 0 < L + εf := by linarith
  -- `hbad` forces `j < qn / 5`: `min j (qn - j) < qn/5` and `qn - j ≥ 3 qn / 8 > qn / 5`.
  have hQJ : 3 * (qn:ℝ) / 8 ≤ (qn:ℝ) - (j:ℝ) := by linarith [hj]
  have hDlt : (d:ℝ) < (qn:ℝ) / 5 := by linarith [hbad]
  have hmD5 : min (j:ℝ) ((qn:ℝ) - (j:ℝ)) < (qn:ℝ) / 5 := by
    rw [hd] at hDlt; exact hDlt
  have hmD : min (j:ℝ) ((qn:ℝ) - (j:ℝ)) < (qn:ℝ) - (j:ℝ) := by
    linarith [hmD5, hQ0, hQJ]
  have hJmin : (j:ℝ) = min (j:ℝ) ((qn:ℝ) - (j:ℝ)) := by
    by_cases h : (j:ℝ) ≤ (qn:ℝ) - (j:ℝ)
    · exact (min_eq_left h).symm
    · exfalso
      have hlt : (qn:ℝ) - (j:ℝ) < (j:ℝ) := not_le.mp h
      have hh : min (j:ℝ) ((qn:ℝ) - (j:ℝ)) = (qn:ℝ) - (j:ℝ) := min_eq_right (le_of_lt hlt)
      rw [hh] at hmD
      exact absurd hmD (lt_irrefl _)
  have hJle : (j:ℝ) ≤ (qn:ℝ) / 5 := by
    have h := hmD5
    rw [← hJmin] at h
    linarith
  have h6 : (qn:ℝ) + (j:ℝ) ≤ (6:ℝ)/5 * (qn:ℝ) := by linarith [hJle]
  -- Bound the prefactor by `exp` of the logarithmic budget.
  have hleG : 2 * (C * (1 + 2*(qn:ℝ))) ≤
      Real.exp ((19/80)*L*(qn:ℝ) + (14/5)*εf*(qn:ℝ) + L + εf) := by
    rcases eq_or_lt_of_le hC with hC0 | hCpos
    · rw [← hC0]
      simp only [mul_zero, zero_mul]
      exact (Real.exp_pos _).le
    · have hpos : 0 < 2 * C * (1 + 2*(qn:ℝ)) := by positivity
      have h1 : 2 * C * (1 + 2*(qn:ℝ)) ≤ Real.exp ((19/80)*L*(qn:ℝ) + (14/5)*εf*(qn:ℝ) + L + εf) :=
        (Real.log_le_iff_le_exp hpos).mp hlog
      have h2 : 2 * C * (1 + 2*(qn:ℝ)) = 2 * (C * (1 + 2*(qn:ℝ))) := by ring
      exact h2 ▸ h1
  -- The exponents combine to exactly the desired bound.
  have hGB : ((19/80)*L*(qn:ℝ) + (14/5)*εf*(qn:ℝ) + L + εf)
        + (((qn:ℝ) - 1 + (j:ℝ)) * (L + εf))
        ≤ (2 * (qn:ℝ)) * (23*L/32 + 2*εf) := by
    have hkey : L + εf + ((qn:ℝ) - 1 + (j:ℝ)) * (L + εf) = ((qn:ℝ) + (j:ℝ)) * (L + εf) := by ring
    have hmul : ((qn:ℝ) + (j:ℝ)) * (L + εf) ≤ (6/5) * (qn:ℝ) * (L + εf) :=
      mul_le_mul_of_nonneg_right h6 hLf.le
    nlinarith [hmul, hkey]
  calc
    2 * (C * (1 + 2*(qn:ℝ))) * Real.exp (((qn:ℝ) - 1 + (j:ℝ)) * (L + εf))
        ≤ Real.exp ((19/80)*L*(qn:ℝ) + (14/5)*εf*(qn:ℝ) + L + εf)
            * Real.exp (((qn:ℝ) - 1 + (j:ℝ)) * (L + εf)) :=
          mul_le_mul_of_nonneg_right hleG (Real.exp_pos _).le
    _ = Real.exp (((19/80)*L*(qn:ℝ) + (14/5)*εf*(qn:ℝ) + L + εf)
            + ((qn:ℝ) - 1 + (j:ℝ)) * (L + εf)) := by rw [← Real.exp_add]
    _ ≤ Real.exp ((2 * (qn:ℝ)) * (23*L/32 + 2*εf)) := Real.exp_le_exp.mpr hGB

end Work.TMC16Core.Assembly
