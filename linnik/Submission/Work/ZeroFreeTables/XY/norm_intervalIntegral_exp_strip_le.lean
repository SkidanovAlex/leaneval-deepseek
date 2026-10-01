import Mathlib

namespace Work.ZeroFreeTables.XY

/-- For `|u| ≤ 1` and `t ∈ [0,b]`, the exponential factor
`exp(-((u + v i) t))` has norm at most `exp b`. -/
lemma norm_exp_strip_le {u v t b : ℝ} (hu : |u| ≤ 1) (ht0 : 0 ≤ t) (htb : t ≤ b) :
    ‖Complex.exp (-(((u : ℂ) + (v : ℂ) * Complex.I) * (t : ℂ)))‖ ≤ Real.exp b := by
  rw [Complex.norm_exp]
  apply Real.exp_le_exp.mpr
  have h1 : (-(((u : ℂ) + (v : ℂ) * Complex.I) * (t : ℂ))).re = -(u * t) := by
    simp [Complex.mul_re, Complex.add_re, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im]
  rw [h1]
  have h2 : |u * t| ≤ b := by
    rw [abs_mul, abs_of_nonneg ht0]
    calc |u| * t ≤ 1 * t := by nlinarith [hu, ht0]
      _ = t := by ring
      _ ≤ b := htb
  calc -(u * t) ≤ |u * t| := neg_le_abs _
    _ ≤ b := h2

theorem norm_intervalIntegral_exp_strip_le {u v b : ℝ} (hb : 0 ≤ b) (hu : |u| ≤ 1)
    {h : ℝ → ℂ} (hcont : ContinuousOn h (Set.Icc (0:ℝ) b)) (M : ℝ) (hMnn : 0 ≤ M)
    (hM : ∀ t ∈ Set.Icc (0:ℝ) b, ‖h t‖ ≤ M) :
    ‖∫ t in (0:ℝ)..b, Complex.exp (-(((u : ℂ) + (v : ℂ) * Complex.I) * (t : ℂ))) * h t‖
      ≤ Real.exp b * M * b := by
  have hbound : ∀ t ∈ Set.uIoc (0:ℝ) b,
      ‖Complex.exp (-(((u : ℂ) + (v : ℂ) * Complex.I) * (t : ℂ))) * h t‖
        ≤ Real.exp b * M := by
    intro t ht
    rw [Set.uIoc_of_le hb] at ht
    have htI : t ∈ Set.Icc (0:ℝ) b := ⟨le_of_lt ht.1, ht.2⟩
    rw [norm_mul]
    exact mul_le_mul (norm_exp_strip_le hu (le_of_lt ht.1) ht.2) (hM t htI)
      (norm_nonneg _) (Real.exp_pos b).le
  have h2 := intervalIntegral.norm_integral_le_of_norm_le_const hbound
  rw [sub_zero, abs_of_nonneg hb] at h2
  calc _ ≤ (Real.exp b * M) * b := h2
    _ = Real.exp b * M * b := by ring

end Work.ZeroFreeTables.XY
