import Mathlib

namespace Work.FIArea6Road

/-- Rewrite the complex power `n ^ (-(σ + i t))` (with `n ≥ 1` a natural number) as a
product of the constant `exp (-(log n * σ))` and the pure exponential
`exp (-(log n) * i * t)`.  This exposes the `t`-dependence as a plain exponential so that
`intervalIntegral.integral_exp_mul_complex` can be applied. -/
private lemma cpow_factor (n : ℕ) (hn : n ≠ 0) (σ t : ℝ) :
    (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))
      = Complex.exp (-((Real.log (n:ℝ) : ℂ) * (σ : ℂ))) *
        Complex.exp ((-((Real.log (n:ℝ) : ℂ)) * Complex.I) * (t : ℂ)) := by
  rw [Complex.cpow_def_of_ne_zero (by exact_mod_cast hn), ← Complex.natCast_log]
  have h : (↑(Real.log ↑n) : ℂ) * (-((σ : ℂ) + (t : ℂ) * Complex.I))
      = -((Real.log ↑n : ℂ) * (σ : ℂ)) + ((-(Real.log ↑n : ℂ)) * Complex.I) * (t : ℂ) := by
    push_cast
    ring
  rw [h, Complex.exp_add]

theorem ZsfunTermIntegralBound (a : ℕ → ℂ) {σ T : ℝ} (hσ : 1 < σ) (hT : 0 < T) {n : ℕ} (hn : 2 ≤ n) :
    ‖∫ t in (0 : ℝ)..T, a n * (n : ℂ) ^ (-((σ : ℂ) + (t : ℂ) * Complex.I))‖
      ≤ ‖a n‖ * (n : ℝ) ^ (-σ) * (2 / Real.log 2) := by
  have hn0 : n ≠ 0 := by omega
  have hnr : (0:ℝ) < (n:ℝ) := by exact_mod_cast (by omega : 0 < n)
  have hL : 0 < Real.log (n:ℝ) := Real.log_pos (by exact_mod_cast (by omega : 1 < n))
  have hL2 : Real.log 2 ≤ Real.log (n:ℝ) := Real.log_le_log (by norm_num) (by exact_mod_cast hn)
  have hLpos : (0:ℝ) < Real.log 2 := Real.log_pos (by norm_num)
  set L : ℝ := Real.log (n:ℝ) with hLdef
  set c : ℂ := (-(L:ℂ)) * Complex.I with hcdef
  have hL' : 0 < L := by rw [hLdef]; exact hL
  have hL2' : Real.log 2 ≤ L := by rw [hLdef]; exact hL2
  -- the frequency `c = -log n · i` is nonzero
  have hc : c ≠ 0 := by
    rw [hcdef]
    intro h
    have h1 : (-(L:ℂ)) = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · exact h'
      · exact absurd h' Complex.I_ne_zero
    have h2 : L = 0 := by
      have := congrArg Complex.re h1
      simpa using this
    exact hL'.ne' h2
  -- exact value of the exponential integral
  have hInt : ∫ t in (0:ℝ)..T, Complex.exp (c * (t:ℂ)) = (Complex.exp (c*(T:ℂ)) - 1)/c := by
    rw [integral_exp_mul_complex hc]
    norm_num
  have hreT : (c * (T:ℂ)).re = 0 := by
    rw [hcdef]
    simp only [Complex.mul_re, Complex.mul_im, Complex.neg_re, Complex.neg_im, Complex.ofReal_re,
      Complex.ofReal_im, Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, neg_zero]
  have hnum : ‖Complex.exp (c * (T:ℂ)) - 1‖ ≤ 2 := by
    calc ‖Complex.exp (c * (T:ℂ)) - 1‖
        ≤ ‖Complex.exp (c * (T:ℂ))‖ + ‖(1:ℂ)‖ := norm_sub_le _ _
      _ = Real.exp ((c*(T:ℂ)).re) + 1 := by rw [Complex.norm_exp]; norm_num
      _ = 2 := by rw [hreT, Real.exp_zero]; norm_num
  have hcL : ‖c‖ = L := by
    rw [hcdef, norm_mul, Complex.norm_I, mul_one]
    simp [abs_of_pos hL']
  have hbnd : ‖∫ t in (0:ℝ)..T, Complex.exp (c * (t:ℂ))‖ ≤ 2 / L := by
    rw [hInt, norm_div, hcL]
    exact div_le_div_of_nonneg_right hnum hL'.le
  -- the constant has norm exactly `n ^ (-σ)`
  have hnk : ‖Complex.exp (-((L:ℂ)*(σ:ℂ)))‖ = (n:ℝ)^(-σ) := by
    rw [Complex.norm_exp]
    have hre : (-((L:ℂ)*(σ:ℂ))).re = -(L*σ) := by
      simp [Complex.mul_re]
    rw [hre, hLdef, Real.rpow_def_of_pos hnr]
    congr 1
    ring
  have hf : (∫ t in (0:ℝ)..T, (n:ℂ)^(-((σ:ℂ)+(t:ℂ)*Complex.I)))
      = Complex.exp (-((L:ℂ)*(σ:ℂ))) * ∫ t in (0:ℝ)..T, Complex.exp (c*(t:ℂ)) := by
    rw [← intervalIntegral.integral_const_mul]
    apply intervalIntegral.integral_congr
    intro t ht
    dsimp only
    rw [cpow_factor n hn0 σ t, hcdef, hLdef]
  have hmain : ‖∫ t in (0:ℝ)..T, (n:ℂ)^(-((σ:ℂ)+(t:ℂ)*Complex.I))‖
      ≤ (n:ℝ)^(-σ) * (2/Real.log 2) := by
    calc ‖∫ t in (0:ℝ)..T, (n:ℂ)^(-((σ:ℂ)+(t:ℂ)*Complex.I))‖
        = ‖Complex.exp (-((L:ℂ)*(σ:ℂ))) * ∫ t in (0:ℝ)..T, Complex.exp (c*(t:ℂ))‖ := by rw [hf]
      _ = ‖Complex.exp (-((L:ℂ)*(σ:ℂ)))‖ * ‖∫ t in (0:ℝ)..T, Complex.exp (c*(t:ℂ))‖ := norm_mul _ _
      _ ≤ (n:ℝ)^(-σ) * (2/Real.log 2) := by
          rw [hnk]
          calc (n:ℝ)^(-σ) * ‖∫ t in (0:ℝ)..T, Complex.exp (c*(t:ℂ))‖
              ≤ (n:ℝ)^(-σ) * (2/L) := mul_le_mul_of_nonneg_left hbnd (Real.rpow_nonneg hnr.le _)
            _ ≤ (n:ℝ)^(-σ) * (2/Real.log 2) := by
                apply mul_le_mul_of_nonneg_left _ (Real.rpow_nonneg hnr.le _)
                exact div_le_div_of_nonneg_left (by norm_num) hLpos hL2'
  have hfactor : (∫ t in (0:ℝ)..T, a n * (n:ℂ)^(-((σ:ℂ)+(t:ℂ)*Complex.I)))
      = a n * ∫ t in (0:ℝ)..T, (n:ℂ)^(-((σ:ℂ)+(t:ℂ)*Complex.I)) :=
    intervalIntegral.integral_const_mul (a n) _
  rw [hfactor, norm_mul]
  calc ‖a n‖ * ‖∫ t in (0:ℝ)..T, (n:ℂ)^(-((σ:ℂ)+(t:ℂ)*Complex.I))‖
      ≤ ‖a n‖ * ((n:ℝ)^(-σ) * (2/Real.log 2)) := mul_le_mul_of_nonneg_left hmain (norm_nonneg _)
    _ = ‖a n‖ * (n:ℝ)^(-σ) * (2/Real.log 2) := by ring

end Work.FIArea6Road
