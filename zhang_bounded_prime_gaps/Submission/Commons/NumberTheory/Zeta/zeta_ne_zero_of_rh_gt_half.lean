import Mathlib.NumberTheory.LSeries.Nonvanishing
import Submission.Commons.NumberTheory.Zeta.zeta_lower_re_two

open Complex

namespace Commons.NumberTheory.Zeta

/-- Assuming the Riemann hypothesis, the Riemann zeta function does not vanish on the open
half-plane `1 / 2 < re s`.  (Real part `≥ 1` is covered by Euler-product nonvanishing; in the
strip `1 / 2 < re s < 1` the Riemann hypothesis forces every zero onto the critical line.) -/
theorem zeta_ne_zero_of_rh_gt_half (h : RiemannHypothesis) {s : ℂ}
    (hs : (1 / 2 : ℝ) < s.re) : riemannZeta s ≠ 0 := by
  intro h0
  by_cases hge : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re hge h0
  · have hlt : s.re < 1 := lt_of_not_ge hge
    have hs1 : s ≠ 1 := by
      intro hs1
      have hs_re : s.re = (1 : ℂ).re := by rw [hs1]
      rw [hs_re] at hlt
      norm_num at hlt
    have htriv : ¬∃ n : ℕ, s = -2 * (n + 1) := by
      rintro ⟨n, hn⟩
      rw [hn] at hs
      have hre : ((-2 : ℂ) * ((n : ℂ) + 1)).re = -2 * ((n : ℝ) + 1) := by
        norm_num
      rw [hre] at hs
      have hn0 : (0 : ℝ) ≤ n + 1 := by positivity
      nlinarith
    have hhalf : s.re = 1 / 2 := h s h0 htriv hs1
    linarith

end Commons.NumberTheory.Zeta
