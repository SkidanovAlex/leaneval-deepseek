import Mathlib

namespace Work.FIArea6Hecke.R

/-- A crude but sufficient bound for the log of a point `4d·(σ+2+iτ)` of the right half plane
with `1 ≤ d`, `1/2 ≤ σ ≤ 1`: the 8-th power of `‖log(4d·(σ+2+iτ))‖` is dominated by
`4^8·(log(4d(2+|τ|)))^8`.  The proof only uses `‖log z‖ ≤ |log ‖z‖| + |arg z|`,
`‖z‖ ≤ 16·d·(2+|τ|)` and the numerical facts `π < 4`, `log 2 > 0.693…`. -/
theorem heckeStripWLog8 (d : ℕ) (hd : 1 ≤ d) (σ τ : ℝ) (hσ1 : 1 / 2 ≤ σ) (hσ2 : σ ≤ 1) :
    ‖Complex.log (((4 * (d : ℝ)) : ℂ) * (((σ : ℂ) + (τ : ℂ) * Complex.I) + 2))‖ ^ (8 : ℕ) ≤
      (4 : ℝ) ^ (8 : ℕ) * (Real.log (4 * (d : ℝ) * (2 + |τ|))) ^ (8 : ℕ) := by
  have hd1R : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := by linarith
  have hdpos : (0 : ℝ) < (d : ℝ) := by linarith
  set z : ℂ := ((4 * (d : ℝ)) : ℂ) * (((σ : ℂ) + (τ : ℂ) * Complex.I) + 2) with hzdef
  set L : ℝ := Real.log (4 * (d : ℝ) * (2 + |τ|)) with hLdef
  have hzform : z = ((4 * (d : ℝ) * (σ + 2) : ℝ) : ℂ) +
      ((4 * (d : ℝ) * τ : ℝ) : ℂ) * Complex.I := by
    rw [hzdef]; push_cast; ring
  have hre : z.re = 4 * (d : ℝ) * (σ + 2) := by rw [hzform]; simp
  have him : z.im = 4 * (d : ℝ) * τ := by rw [hzform]; simp
  have hA_nonneg : (0 : ℝ) ≤ 4 * (d : ℝ) * (σ + 2) := by nlinarith [hd0, hσ1]
  have hznorm_le : ‖z‖ ≤ 6 * (d : ℝ) * (2 + |τ|) := by
    have h1 := Complex.norm_le_abs_re_add_abs_im z
    rw [hre, him] at h1
    have hAabs : |4 * (d : ℝ) * (σ + 2)| = 4 * (d : ℝ) * (σ + 2) := abs_of_nonneg hA_nonneg
    have hBabs : |4 * (d : ℝ) * τ| = 4 * (d : ℝ) * |τ| := by
      rw [abs_mul, abs_of_nonneg (by linarith : (0 : ℝ) ≤ 4 * (d : ℝ))]
    rw [hAabs, hBabs] at h1
    nlinarith [h1, hσ2, abs_nonneg τ, hd0]
  have hnorm_ge_one : (1 : ℝ) ≤ ‖z‖ := by
    have h := Complex.abs_re_le_norm z
    rw [hre] at h
    rw [abs_of_nonneg hA_nonneg] at h
    nlinarith [h, hd1R, hσ1]
  have hz16 : ‖z‖ ≤ 16 * (d : ℝ) * (2 + |τ|) := by
    nlinarith [hznorm_le, abs_nonneg τ, hd0]
  have hpos : (0 : ℝ) < ‖z‖ := by linarith
  have hlog : Real.log ‖z‖ ≤ Real.log 4 + L := by
    have h1 : Real.log ‖z‖ ≤ Real.log (16 * (d : ℝ) * (2 + |τ|)) := Real.log_le_log hpos hz16
    have h2 : Real.log (16 * (d : ℝ) * (2 + |τ|)) = Real.log 4 + L := by
      have hsplit : Real.log (16 * (d : ℝ) * (2 + |τ|))
          = Real.log 4 + Real.log (4 * (d : ℝ) * (2 + |τ|)) := by
        rw [show 16 * (d : ℝ) * (2 + |τ|) = 4 * (4 * (d : ℝ) * (2 + |τ|)) by ring]
        nth_rewrite 1 [Real.log_mul (by norm_num) (by positivity)]
        rfl
      rw [hLdef]; exact hsplit
    linarith
  have hlog4 : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 * 2 by norm_num, Real.log_mul (by norm_num) (by norm_num)]
    ring
  have hnum : Real.log 4 + Real.pi ≤ 9 * Real.log 2 := by
    rw [hlog4]
    nlinarith [Real.pi_lt_four, Real.log_two_gt_d9]
  have hlog8 : Real.log 8 = 3 * Real.log 2 := by
    rw [show (8 : ℝ) = 2 ^ 3 by norm_num, Real.log_pow]
    norm_num
  have hL_ge : Real.log 8 ≤ L := by
    rw [hLdef]
    apply Real.log_le_log (by norm_num)
    nlinarith [hd1R, abs_nonneg τ]
  have hL_lower : 9 * Real.log 2 ≤ 3 * L := by
    nlinarith [hL_ge, hlog8]
  have hmain : ‖Complex.log z‖ ≤ 4 * L := by
    have h1 := Complex.norm_le_abs_re_add_abs_im (Complex.log z)
    rw [Complex.log_re, Complex.log_im] at h1
    rw [abs_of_nonneg (Real.log_nonneg hnorm_ge_one)] at h1
    have harg : |z.arg| ≤ Real.pi :=
      abs_le.mpr ⟨(Complex.neg_pi_lt_arg z).le, Complex.arg_le_pi z⟩
    linarith [h1, harg, hlog, hnum, hL_lower]
  rw [← mul_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) hmain 8

end Work.FIArea6Hecke.R
