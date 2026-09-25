import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.Zeta

open Complex
open scoped Real

/-- The Riemann zeta function has no zeros in the closed vertical strip `-1 ≤ re s ≤ 0`.
Indeed, for such `s` the reflection `1 - s` has real part in `[1, 2]`, so `ζ (1 - s) ≠ 0` and
`Γ (1 - s) ≠ 0`; the functional equation then forces `ζ s ≠ 0` unless `cos (π (1 - s) / 2)`
vanishes, which can only happen at `s = 0`, where `ζ 0 = -1 / 2 ≠ 0`. -/
theorem riemannZeta_ne_zero_of_re_neg_one_le_zero {s : ℂ}
    (hlo : -(1 : ℝ) ≤ s.re) (hhi : s.re ≤ 0) : riemannZeta s ≠ 0 := by
  rcases eq_or_ne s 0 with rfl | hs0
  · rw [riemannZeta_zero]; norm_num
  · intro hz
    set S : ℂ := 1 - s with hS
    have hSre : S.re = 1 - s.re := by simp [hS]
    have hS_ne_one : S ≠ 1 := by
      intro h
      apply hs0
      have h1 : (1 : ℂ) - s = 1 := h
      linear_combination -h1
    have hsn : ∀ n : ℕ, S ≠ -(n : ℂ) := by
      intro n hn
      have hre : S.re = (-(n : ℂ)).re := by rw [hn]
      rw [hSre, Complex.neg_re, Complex.natCast_re] at hre
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hfe := riemannZeta_one_sub hsn hS_ne_one
    have h1S : (1 : ℂ) - S = s := by simp [hS]
    rw [h1S, hz] at hfe
    have hSre_ge : (1 : ℝ) ≤ S.re := by rw [hSre]; linarith
    have hcos : cos (π * S / 2) ≠ 0 := by
      rw [Complex.cos_ne_zero_iff]
      intro k hk
      have hpi : (π : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      have hS_eq : S = 2 * (k : ℂ) + 1 := by
        have h := hk
        rw [div_eq_div_iff two_ne_zero two_ne_zero] at h
        rw [mul_comm (2 * (k : ℂ) + 1) π] at h
        exact mul_left_cancel₀ hpi (mul_right_cancel₀ two_ne_zero h)
      have hs_eq : s = -2 * (k : ℂ) := by
        have h2 : (1 : ℂ) - s = 2 * (k : ℂ) + 1 := by rw [← hS]; exact hS_eq
        linear_combination -h2
      have hre_int : s.re = -2 * (k : ℝ) := by rw [hs_eq]; simp
      have h1 : ((-1 : ℤ) : ℝ) ≤ -2 * k := by
        rw [show ((-1 : ℤ) : ℝ) = -(1 : ℝ) from by norm_num, ← hre_int]
        exact hlo
      have h2 : -2 * k ≤ ((0 : ℤ) : ℝ) := by
        rw [show ((0 : ℤ) : ℝ) = (0 : ℝ) from by norm_num, ← hre_int]
        exact hhi
      have h1' : (-1 : ℤ) ≤ -2 * k := by exact_mod_cast h1
      have h2' : -2 * k ≤ (0 : ℤ) := by exact_mod_cast h2
      have hk0 : k = 0 := by omega
      exact hs0 (by rw [hs_eq, hk0]; norm_num)
    have hne : 2 * (2 * π) ^ (-S) * Gamma S * cos (π * S / 2) * riemannZeta S ≠ 0 :=
      mul_ne_zero
        (mul_ne_zero
          (mul_ne_zero
            (mul_ne_zero (by norm_num) (Complex.cpow_ne_zero_iff.mpr (Or.inl
              (mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)))))
            (Complex.Gamma_ne_zero_of_re_pos (by linarith)))
          hcos)
        (riemannZeta_ne_zero_of_one_le_re hSre_ge)
    exact hne hfe.symm

theorem zeta1_ne_zero_re_neg_one_le_zero {s : ℂ} (hlo : -(1 : ℝ) ≤ s.re) (hhi : s.re ≤ 0) :
    riemannZeta₁ s ≠ 0 := by
  have hs1 : s ≠ 1 := by
    intro h
    rw [h] at hhi
    norm_num at hhi
  intro h0
  apply riemannZeta_ne_zero_of_re_neg_one_le_zero hlo hhi
  rw [riemannZeta_eq_inv_sub_mul hs1, h0, mul_zero]

end Commons.NumberTheory.Zeta