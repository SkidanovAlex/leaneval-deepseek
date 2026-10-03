import Mathlib

namespace Work.FIArea6Hecke.R

/-- If `2 ≤ z.re` then `2 + |z.im| ≤ ‖z‖ ^ 2`.  Indeed `‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 ≥ 4 + z.im ^ 2`
and `4 + y ^ 2 - (2 + |y|) = 2 + |y| ^ 2 - |y| > 0`. -/
private lemma two_add_abs_im_le_normSq (z : ℂ) (hz : 2 ≤ z.re) :
    2 + |z.im| ≤ ‖z‖ ^ 2 := by
  have hs : ‖z‖ ^ 2 = z.re ^ 2 + z.im ^ 2 := by
    rw [Complex.sq_norm, Complex.normSq_apply]; ring
  rw [hs]
  have hz4 : (4 : ℝ) ≤ z.re ^ 2 := by nlinarith
  nlinarith [sq_abs z.im, abs_nonneg z.im, hz4]

/-- **Lower bound for `‖Complex.log (4 d (s+2))‖` on the strip `0 ≤ Re s ≤ 1`.**

The modulus of a complex logarithm dominates its real part `log ‖4 d (s+2)‖`
`= log (4d) + log ‖s + 2‖`, and `log ‖s + 2‖ ≥ (1/2) log (2 + |Im s|)` because
`2 + |Im s| ≤ ‖s + 2‖ ^ 2` (here `Re (s + 2) ≥ 2`).  Since `4d ≥ 4 ≥ 1`, the term
`log (4d)` may be halved, giving the claim. -/
theorem clogLowerStrip :
    ∀ (d : ℕ), 1 ≤ d → ∀ (s : ℂ), 0 ≤ s.re → s.re ≤ 1 →
      (1 / 2 : ℝ) * Real.log (4 * (d : ℝ) * (2 + |s.im|)) ≤
        ‖Complex.log (((4 * (d : ℝ)) : ℂ) * (s + 2))‖ := by
  intro d hd s hs0 _hs1
  have hd1 : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have h4d : (0 : ℝ) < 4 * (d : ℝ) := by linarith
  have h4d1 : (1 : ℝ) ≤ 4 * (d : ℝ) := by linarith
  have hy : (0 : ℝ) < 2 + |s.im| := by
    have := abs_nonneg s.im; linarith
  have hs22 : (2 : ℝ) ≤ ‖s + 2‖ := by
    have h1 : |(s + 2).re| ≤ ‖s + 2‖ := Complex.abs_re_le_norm _
    have h2 : (s + 2).re = s.re + 2 := by simp
    rw [h2, abs_of_nonneg (by linarith : (0 : ℝ) ≤ s.re + 2)] at h1
    linarith
  have hs2pos : (0 : ℝ) < ‖s + 2‖ := by linarith
  -- the key real inequality `2 + |Im s| ≤ ‖s + 2‖ ^ 2`
  have hkey : 2 + |s.im| ≤ ‖s + 2‖ ^ 2 := by
    have h2 : (s + 2).re = s.re + 2 := by simp
    have h3 : (2 : ℝ) ≤ (s + 2).re := by rw [h2]; linarith
    have h4 : (s + 2).im = s.im := by simp
    simpa [h4] using two_add_abs_im_le_normSq (s + 2) h3
  -- hence `log (2 + |Im s|) ≤ 2 log ‖s + 2‖`
  have hlog2 : Real.log (2 + |s.im|) ≤ 2 * Real.log ‖s + 2‖ := by
    have h := Real.log_le_log hy hkey
    rw [Real.log_pow] at h
    norm_num at h
    exact h
  -- the modulus of the point at which the logarithm is taken
  have hcast : ‖(((4 * (d : ℝ)) : ℂ))‖ = 4 * (d : ℝ) := by
    rw [show ‖(((4 * (d : ℝ)) : ℂ))‖ = |4 * (d : ℝ)| by simp]
    exact abs_of_nonneg (le_of_lt h4d)
  have hnormz : ‖(((4 * (d : ℝ)) : ℂ)) * (s + 2)‖ = 4 * (d : ℝ) * ‖s + 2‖ := by
    rw [norm_mul, hcast]
  have hznorm1 : (1 : ℝ) ≤ ‖(((4 * (d : ℝ)) : ℂ)) * (s + 2)‖ := by
    rw [hnormz]; nlinarith [hs22, hd1]
  have hlogz : Real.log ‖(((4 * (d : ℝ)) : ℂ)) * (s + 2)‖
      = Real.log (4 * (d : ℝ)) + Real.log ‖s + 2‖ := by
    rw [hnormz, Real.log_mul (ne_of_gt h4d) (ne_of_gt hs2pos)]
  -- `Real.log ‖w‖ ≤ ‖Complex.log w‖` since `‖w‖ ≥ 1`
  have hle1 : Real.log ‖(((4 * (d : ℝ)) : ℂ)) * (s + 2)‖ ≤
      ‖Complex.log ((((4 * (d : ℝ)) : ℂ)) * (s + 2))‖ := by
    have h := Complex.abs_re_le_norm (Complex.log ((((4 * (d : ℝ)) : ℂ)) * (s + 2)))
    rw [Complex.log_re, abs_of_nonneg (Real.log_nonneg hznorm1)] at h
    exact h
  have hL : 0 ≤ Real.log (4 * (d : ℝ)) := Real.log_nonneg h4d1
  have hgoal : (1 / 2) * (Real.log (4 * (d : ℝ)) + Real.log (2 + |s.im|)) ≤
      ‖Complex.log ((((4 * (d : ℝ)) : ℂ)) * (s + 2))‖ := by
    linarith [hle1, hlogz, hlog2, hL]
  have hlog3 : Real.log (4 * (d : ℝ) * (2 + |s.im|)) =
      Real.log (4 * (d : ℝ)) + Real.log (2 + |s.im|) := by
    rw [Real.log_mul (ne_of_gt h4d) (ne_of_gt hy)]
  rw [hlog3]
  exact hgoal

end Work.FIArea6Hecke.R
