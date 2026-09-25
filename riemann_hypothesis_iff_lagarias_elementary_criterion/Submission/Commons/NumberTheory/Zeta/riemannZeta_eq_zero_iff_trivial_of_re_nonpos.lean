import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.RingTheory.SimpleRing.Principal

namespace Commons.NumberTheory.Zeta

open Complex
open scoped Real

/-- For `re s ≤ 0`, the zeros of the Riemann zeta function are exactly the trivial zeros
`s = -2 * (n + 1)`.  The forward direction uses the functional equation
`ζ(1 - s) = 2 * (2π) ^ (-s) * Γ s * cos (π s / 2) * ζ s` with `s` replaced by `1 - s`: all
factors other than the cosine are nonzero, so the cosine vanishes, forcing `s` to be an even
negative integer.  The reverse direction is the trivial zero
`riemannZeta_neg_two_mul_nat_add_one`. -/
theorem riemannZeta_eq_zero_iff_trivial_of_re_nonpos {s : ℂ} (hre : s.re ≤ 0) :
    riemannZeta s = 0 ↔ ∃ n : ℕ, s = -2 * (n + 1) := by
  constructor
  · intro hz
    have hs0 : s ≠ 0 := by
      intro h
      rw [h, riemannZeta_zero] at hz
      norm_num at hz
    set S : ℂ := 1 - s with hS
    have hSre : S.re = 1 - s.re := by simp [hS]
    have hS_ne_one : S ≠ 1 := by
      intro h
      apply hs0
      have h1 : (1 : ℂ) - s = 1 := h
      linear_combination -h1
    have hsn : ∀ n : ℕ, S ≠ -(n : ℂ) := by
      intro n hn
      have hre' : S.re = (-(n : ℂ)).re := by rw [hn]
      rw [hSre, Complex.neg_re, Complex.natCast_re] at hre'
      have hn0 : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
      linarith
    have hfe := riemannZeta_one_sub (s := S) hsn hS_ne_one
    have h1S : (1 : ℂ) - S = s := by simp [hS]
    rw [h1S] at hfe
    have hS1 : (1 : ℝ) ≤ S.re := by rw [hSre]; linarith
    have hzetaS : riemannZeta S ≠ 0 := riemannZeta_ne_zero_of_one_le_re hS1
    have hGammaS : Gamma S ≠ 0 := Complex.Gamma_ne_zero_of_re_pos (by linarith)
    have hcpow : (2 * (π : ℂ)) ^ (-S) ≠ 0 := by
      rw [Complex.cpow_ne_zero_iff]
      left
      exact mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hcos0 : cos (π * S / 2) = 0 := by
      have h3 : 2 * (2 * (π : ℂ)) ^ (-S) * Gamma S * cos (π * S / 2) * riemannZeta S = 0 := by
        rw [← hfe]
        exact hz
      exact (mul_eq_zero.mp ((mul_eq_zero.mp h3).resolve_right hzetaS)).resolve_left
        (mul_ne_zero (mul_ne_zero two_ne_zero hcpow) hGammaS)
    obtain ⟨k, hk⟩ := Complex.cos_eq_zero_iff.mp hcos0
    have hS_eq : S = 2 * (k : ℂ) + 1 := by
      have h := hk
      rw [div_eq_div_iff two_ne_zero two_ne_zero] at h
      rw [mul_comm (2 * (k : ℂ) + 1) (π : ℂ)] at h
      exact mul_left_cancel₀ (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
        (mul_right_cancel₀ two_ne_zero h)
    have hs_eq : s = -2 * (k : ℂ) := by
      have h2 : (1 : ℂ) - s = 2 * (k : ℂ) + 1 := by rw [← hS]; exact hS_eq
      linear_combination -h2
    have hs_re : s.re = -2 * (k : ℝ) := by
      rw [hs_eq]
      norm_num
    have hkR : (0 : ℝ) ≤ (k : ℝ) := by
      rw [hs_re] at hre
      linarith
    have hk_nonneg : (0 : ℤ) ≤ k := by exact_mod_cast hkR
    have hk_ne : k ≠ 0 := by
      intro hk0
      exact hs0 (by rw [hs_eq, hk0]; norm_num)
    obtain ⟨m, hm⟩ : ∃ m : ℕ, k = (m : ℤ) :=
      ⟨k.natAbs, (Int.natAbs_of_nonneg hk_nonneg).symm⟩
    have hm_ne : m ≠ 0 := by
      intro h
      exact hk_ne (by rw [hm, h]; norm_num)
    refine ⟨m - 1, ?_⟩
    have hsplit : m - 1 + 1 = m := Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hm_ne)
    have hcast : (((m - 1 : ℕ) : ℂ) + 1) = (m : ℂ) := by
      have h2 : (((m - 1 + 1 : ℕ)) : ℂ) = (m : ℂ) := by rw [hsplit]
      simpa using h2
    rw [hs_eq, hm, hcast]
    norm_num
  · rintro ⟨n, rfl⟩
    exact riemannZeta_neg_two_mul_nat_add_one n

end Commons.NumberTheory.Zeta