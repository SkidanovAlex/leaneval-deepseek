import Mathlib

namespace Work.LinnikAreas.FarRepel

/-- The series `∑_{n≥0} (-1)^{m+1} m! (1/(w+n))^{m+1}` is summable for `m ≥ 1` and `Re w > 0`
(absolute convergence: `‖(1/(w+n))^{m+1}‖ = 1/‖w+n‖^{m+1} ≲ n^{-(m+1)}` and `m+1 > 1`). -/
theorem digammaDerivSeriesSummable (m : ℕ) (hm : 1 ≤ m) {w : ℂ} (hw : 0 < w.re) :
    Summable (fun n : ℕ => (-1 : ℂ)^(m+1) * (m.factorial : ℂ) * (1 / (w + (n:ℂ)))^(m+1)) := by
  -- The constant factor `(-1)^(m+1) * m!` is irrelevant for convergence:
  -- it suffices to prove summability of the pure power series `∑ (1/(w+n))^(m+1)`.
  have hcore : Summable (fun n : ℕ => (1 / (w + (n:ℂ)))^(m+1)) := by
    -- Shift the index by `1`; then `‖w + n‖ ≥ n ≥ 1` for every term.
    rw [← summable_nat_add_iff 1]
    -- Dominating summable series `∑ 1/(n+1)^(m+1)`, which converges since `m + 1 > 1`.
    refine Summable.of_norm_bounded (g := fun n : ℕ => (1:ℝ)/((n:ℝ)+1)^(m+1)) ?_ ?_
    · have h := (summable_nat_add_iff (f := fun k : ℕ => (1:ℝ)/(k:ℝ)^(m+1)) 1).mpr
        ((Real.summable_one_div_nat_pow (p := m+1)).mpr (by omega : 1 < m+1))
      simpa [Nat.cast_add, Nat.cast_one] using h
    · intro n
      -- `n + 1 ≤ ‖w + (n+1)‖` because `Re (w + (n+1)) ≥ n + 1 > 0` and `|Re z| ≤ ‖z‖`.
      have hbound : ((n:ℝ)+1) ≤ ‖w + ((n+1:ℕ):ℂ)‖ := by
        have h2 : (w + ((n+1:ℕ):ℂ)).re = w.re + ((n+1:ℕ):ℝ) := by simp [Complex.add_re]
        have h3 : (0:ℝ) < w.re + ((n+1:ℕ):ℝ) := by
          have : (0:ℝ) ≤ ((n+1:ℕ):ℝ) := by positivity
          linarith
        calc ((n:ℝ)+1) = ((n+1:ℕ):ℝ) := by push_cast; ring
          _ ≤ w.re + ((n+1:ℕ):ℝ) := by linarith
          _ = |(w + ((n+1:ℕ):ℂ)).re| := by rw [h2, abs_of_pos h3]
          _ ≤ ‖w + ((n+1:ℕ):ℂ)‖ := Complex.abs_re_le_norm _
      have hle : (1:ℝ)/‖w + ((n+1:ℕ):ℂ)‖ ≤ 1/((n:ℝ)+1) :=
        one_div_le_one_div_of_le (by positivity) hbound
      have hpow := pow_le_pow_left₀ (by positivity : (0:ℝ) ≤ 1/‖w + ((n+1:ℕ):ℂ)‖) hle (m+1)
      rw [norm_pow, norm_div, norm_one, ← one_div_pow]
      exact hpow
  -- Put the constant factor back in.
  have hconst : Summable (fun n : ℕ => ((-1:ℂ)^(m+1) * (m.factorial:ℂ)) * (1/(w+(n:ℂ)))^(m+1)) :=
    hcore.mul_left _
  simpa [mul_assoc] using hconst

end Work.LinnikAreas.FarRepel
