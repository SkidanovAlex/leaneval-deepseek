import Mathlib.NumberTheory.LSeries.RiemannZeta

namespace Commons.NumberTheory.Zeta

theorem norm_riemannZeta_le_re {s : ℂ} (hs : 1 < s.re) :
    ‖riemannZeta s‖ ≤ (riemannZeta ((s.re : ℝ) : ℂ)).re := by
  have hre : s.re ≠ 0 := ne_of_gt (lt_trans zero_lt_one hs)
  have hσ : 1 < (((s.re : ℝ)) : ℂ).re := by simpa using hs
  have hsum : Summable (fun n : ℕ => 1 / (n : ℂ) ^ s) :=
    Complex.summable_one_div_nat_cpow.mpr hs
  have hsum' : Summable (fun n : ℕ => 1 / (n : ℂ) ^ (((s.re : ℝ)) : ℂ)) :=
    Complex.summable_one_div_nat_cpow.mpr hσ
  have hterm : ∀ n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ = 1 / (n : ℝ) ^ s.re := by
    intro n
    rw [norm_div, norm_one, Complex.norm_natCast_cpow_of_re_ne_zero n hre]
  have hterm' : ∀ n : ℕ, (1 / (n : ℂ) ^ (((s.re : ℝ)) : ℂ)).re = 1 / (n : ℝ) ^ s.re := by
    intro n
    rcases eq_or_ne n 0 with hn | hn
    · subst hn
      have hz : (((s.re : ℝ)) : ℂ) ≠ 0 := by
        simpa using hre
      simp [Complex.zero_cpow hz, Real.zero_rpow hre]
    · have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
      have h1 : (n : ℂ) ^ (((s.re : ℝ)) : ℂ) = (((n : ℝ) ^ s.re : ℝ) : ℂ) := by
        rw [← Complex.ofReal_natCast, Complex.ofReal_cpow (le_of_lt hnpos) s.re]
      rw [h1, ← Complex.ofReal_one, ← Complex.ofReal_div, Complex.ofReal_re]
  calc ‖riemannZeta s‖
      = ‖∑' n : ℕ, 1 / (n : ℂ) ^ s‖ := by rw [zeta_eq_tsum_one_div_nat_cpow hs]
    _ ≤ ∑' n : ℕ, ‖(1 : ℂ) / (n : ℂ) ^ s‖ :=
        norm_tsum_le_tsum_norm (summable_norm_iff.mpr hsum)
    _ = ∑' n : ℕ, 1 / (n : ℝ) ^ s.re := by simp only [hterm]
    _ = ∑' n : ℕ, (1 / (n : ℂ) ^ (((s.re : ℝ)) : ℂ)).re := by
        exact tsum_congr fun n => (hterm' n).symm
    _ = (∑' n : ℕ, 1 / (n : ℂ) ^ (((s.re : ℝ)) : ℂ)).re := (Complex.re_tsum hsum').symm
    _ = (riemannZeta ((s.re : ℝ) : ℂ)).re := by rw [zeta_eq_tsum_one_div_nat_cpow hσ]

end Commons.NumberTheory.Zeta