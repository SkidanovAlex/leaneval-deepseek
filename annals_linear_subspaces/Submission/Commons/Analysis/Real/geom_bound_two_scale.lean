import Mathlib.Analysis.Complex.Exponential

namespace Commons.Analysis.Real

theorem geom_bound_two_scale (l m : ℕ) (hl : 0 < l) (hm : 0 < m) {ε : ℝ} (hε : 0 ≤ ε)
    (hεl : ε ≤ 1 / (l : ℝ)) (n : ℕ) :
    (2 * (2 * Real.exp (((n : ℝ) + 1) * (1 / (l : ℝ) - ε))) + 1) ^ l *
      (2 * (Real.sqrt (2 + (l : ℝ) * (m : ℝ)) * Real.exp (-((n : ℝ) * (1 / (m : ℝ) + ε))))) ^ m
    ≤ (5 ^ l * Real.exp (1 - (l : ℝ) * ε) * (2 * Real.sqrt (2 + (l : ℝ) * (m : ℝ))) ^ m) *
      (Real.exp (-(ε * ((l : ℝ) + (m : ℝ))))) ^ n := by
  have hε0 : 0 ≤ ε := hε
  have hlR : (0 : ℝ) < (l : ℝ) := by exact_mod_cast hl
  have hmR : (0 : ℝ) < (m : ℝ) := by exact_mod_cast hm
  set a : ℝ := 1 / (l : ℝ) - ε with ha
  have ha_nonneg : 0 ≤ a := by
    rw [ha]; exact sub_nonneg.mpr hεl
  have hx_nonneg : 0 ≤ ((n : ℝ) + 1) * a :=
    mul_nonneg (by positivity) ha_nonneg
  have hkey : 4 * Real.exp (((n : ℝ) + 1) * a) + 1 ≤ 5 * Real.exp (((n : ℝ) + 1) * a) := by
    have h1 : 1 ≤ Real.exp (((n : ℝ) + 1) * a) := Real.one_le_exp hx_nonneg
    linarith
  have hF1 : (4 * Real.exp (((n : ℝ) + 1) * a) + 1) ^ l
      ≤ (5 * Real.exp (((n : ℝ) + 1) * a)) ^ l :=
    pow_le_pow_left₀ (by positivity) hkey l
  have hfirst : 2 * (2 * Real.exp (((n : ℝ) + 1) * a)) + 1
      = 4 * Real.exp (((n : ℝ) + 1) * a) + 1 := by ring
  have hstep1 :
      (2 * (2 * Real.exp (((n : ℝ) + 1) * a)) + 1) ^ l *
        (2 * (Real.sqrt (2 + (l : ℝ) * (m : ℝ)) * Real.exp (-((n : ℝ) * (1 / (m : ℝ) + ε))))) ^ m
      ≤ (5 * Real.exp (((n : ℝ) + 1) * a)) ^ l *
        (2 * (Real.sqrt (2 + (l : ℝ) * (m : ℝ)) * Real.exp (-((n : ℝ) * (1 / (m : ℝ) + ε))))) ^ m := by
    rw [hfirst]
    exact mul_le_mul_of_nonneg_right hF1 (by positivity)
  have hE :
      Real.exp (((n : ℝ) + 1) * a) ^ l * Real.exp (-((n : ℝ) * (1 / (m : ℝ) + ε))) ^ m
      = Real.exp (1 - (l : ℝ) * ε) * Real.exp (-(ε * ((l : ℝ) + (m : ℝ)))) ^ n := by
    rw [← Real.exp_nat_mul, ← Real.exp_nat_mul, ← Real.exp_nat_mul]
    rw [← Real.exp_add, ← Real.exp_add, Real.exp_eq_exp]
    rw [ha]
    field_simp
    ring
  have hstep2 :
      (5 * Real.exp (((n : ℝ) + 1) * a)) ^ l *
        (2 * (Real.sqrt (2 + (l : ℝ) * (m : ℝ)) * Real.exp (-((n : ℝ) * (1 / (m : ℝ) + ε))))) ^ m
      = (5 ^ l * Real.exp (1 - (l : ℝ) * ε) * (2 * Real.sqrt (2 + (l : ℝ) * (m : ℝ))) ^ m) *
        (Real.exp (-(ε * ((l : ℝ) + (m : ℝ))))) ^ n := by
    simp only [mul_pow]
    have hX : (5 ^ l * Real.exp (((n : ℝ) + 1) * a) ^ l) *
          (2 ^ m * (Real.sqrt (2 + (l : ℝ) * (m : ℝ)) ^ m *
            Real.exp (-((n : ℝ) * (1 / (m : ℝ) + ε))) ^ m))
        = (5 ^ l * 2 ^ m * Real.sqrt (2 + (l : ℝ) * (m : ℝ)) ^ m) *
          (Real.exp (((n : ℝ) + 1) * a) ^ l *
            Real.exp (-((n : ℝ) * (1 / (m : ℝ) + ε))) ^ m) := by ring
    have hY : (5 ^ l * Real.exp (1 - (l : ℝ) * ε) *
            (2 ^ m * Real.sqrt (2 + (l : ℝ) * (m : ℝ)) ^ m)) *
          Real.exp (-(ε * ((l : ℝ) + (m : ℝ)))) ^ n
        = (5 ^ l * 2 ^ m * Real.sqrt (2 + (l : ℝ) * (m : ℝ)) ^ m) *
          (Real.exp (1 - (l : ℝ) * ε) *
            Real.exp (-(ε * ((l : ℝ) + (m : ℝ)))) ^ n) := by ring
    rw [hX, hY, hE]
  calc
    (2 * (2 * Real.exp (((n : ℝ) + 1) * (1 / (l : ℝ) - ε))) + 1) ^ l *
        (2 * (Real.sqrt (2 + (l : ℝ) * (m : ℝ)) * Real.exp (-((n : ℝ) * (1 / (m : ℝ) + ε))))) ^ m
        = (2 * (2 * Real.exp (((n : ℝ) + 1) * a)) + 1) ^ l *
          (2 * (Real.sqrt (2 + (l : ℝ) * (m : ℝ)) * Real.exp (-((n : ℝ) * (1 / (m : ℝ) + ε))))) ^ m := by rw [ha]
    _ ≤ (5 * Real.exp (((n : ℝ) + 1) * a)) ^ l *
          (2 * (Real.sqrt (2 + (l : ℝ) * (m : ℝ)) * Real.exp (-((n : ℝ) * (1 / (m : ℝ) + ε))))) ^ m := hstep1
    _ = (5 ^ l * Real.exp (1 - (l : ℝ) * ε) * (2 * Real.sqrt (2 + (l : ℝ) * (m : ℝ))) ^ m) *
        (Real.exp (-(ε * ((l : ℝ) + (m : ℝ))))) ^ n := hstep2

end Commons.Analysis.Real