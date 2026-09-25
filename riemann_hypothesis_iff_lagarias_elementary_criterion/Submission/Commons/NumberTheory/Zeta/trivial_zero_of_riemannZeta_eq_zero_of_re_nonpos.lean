import Mathlib.NumberTheory.LSeries.Nonvanishing
import Mathlib.RingTheory.SimpleRing.Principal

open scoped Real

namespace Commons.NumberTheory.Zeta

theorem trivial_zero_of_riemannZeta_eq_zero_of_re_nonpos {s : ℂ} (hz : riemannZeta s = 0)
    (hre : s.re ≤ 0) : ∃ n : ℕ, s = -2 * (n + 1) := by
  have hs0 : s ≠ 0 := by
    rintro rfl
    rw [riemannZeta_zero] at hz
    norm_num at hz
  have hsne : ∀ n : ℕ, (1 - s) ≠ -(n : ℂ) := by
    intro n h
    have hre' : (1 - s).re = (-(n : ℂ)).re := by rw [h]
    rw [Complex.sub_re, Complex.one_re, Complex.neg_re, Complex.natCast_re] at hre'
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    linarith
  have hs1 : (1 - s) ≠ 1 := by
    intro h
    exact hs0 (by linear_combination -h)
  have hfe := riemannZeta_one_sub (s := 1 - s) hsne hs1
  simp only [sub_sub_cancel] at hfe
  have hprod := hfe.symm.trans hz
  have hre1 : (1 : ℝ) ≤ (1 - s).re := by
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hE : riemannZeta (1 - s) ≠ 0 := riemannZeta_ne_zero_of_one_le_re hre1
  have hC : Complex.Gamma (1 - s) ≠ 0 := by
    apply Complex.Gamma_ne_zero_of_re_pos
    simp only [Complex.sub_re, Complex.one_re]; linarith
  have hB : (2 * π : ℂ) ^ (-(1 - s)) ≠ 0 := by
    rw [Complex.cpow_ne_zero_iff]
    left
    exact mul_ne_zero (by norm_num) (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
  have h2 : (2 : ℂ) ≠ 0 := by norm_num
  have hcos : Complex.cos (π * (1 - s) / 2) = 0 := by
    have h := hprod
    rw [mul_eq_zero] at h
    rcases h with h | h
    · rw [mul_eq_zero] at h
      rcases h with h | h
      · exact absurd h (mul_ne_zero (mul_ne_zero h2 hB) hC)
      · exact h
    · exact absurd h hE
  rw [Complex.cos_eq_zero_iff] at hcos
  obtain ⟨k, hk⟩ := hcos
  have hk2 : (1 - s) = (2 * (k : ℂ) + 1) := by
    have hpi2 : (π / 2 : ℂ) ≠ 0 := by
      apply div_ne_zero
      · exact Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
      · norm_num
    have h := hk
    rw [show π * (1 - s) / 2 = (π / 2) * (1 - s) from by ring,
        show (2 * (k : ℂ) + 1) * π / 2 = (π / 2) * (2 * (k : ℂ) + 1) from by ring] at h
    exact mul_left_cancel₀ hpi2 h
  have hs_eq : s = -(2 * (k : ℂ)) := by linear_combination -hk2
  have hsr : s.re = -2 * (k : ℝ) := by
    rw [hs_eq, Complex.neg_re, Complex.mul_re]
    simp
  have hk_nonneg : (0 : ℤ) ≤ k := by
    rw [hsr] at hre
    have : (0 : ℝ) ≤ (k : ℝ) := by linarith
    exact_mod_cast this
  have hkge1 : 1 ≤ k := by
    have hk_ne : k ≠ 0 := by
      intro h
      apply hs0
      rw [hs_eq, h]
      norm_num
    omega
  refine ⟨k.toNat - 1, ?_⟩
  have hkcast : ((k.toNat : ℕ) : ℂ) = (k : ℂ) := by
    have hh : (((k.toNat : ℕ) : ℤ) : ℂ) = (k : ℂ) := by
      rw [Int.toNat_of_nonneg hk_nonneg]
    rwa [Int.cast_natCast] at hh
  have hktoNat1 : 1 ≤ k.toNat := by
    have hh : ((k.toNat : ℤ)) = k := Int.toNat_of_nonneg hk_nonneg
    omega
  have h1 : (((k.toNat - 1 : ℕ) : ℂ) + 1) = (k : ℂ) := by
    rw [← hkcast, Nat.cast_sub hktoNat1]
    ring
  rw [h1, hs_eq]
  ring

end Commons.NumberTheory.Zeta