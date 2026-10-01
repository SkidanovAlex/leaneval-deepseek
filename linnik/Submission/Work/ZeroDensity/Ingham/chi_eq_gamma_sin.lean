import Mathlib
import Submission.Work.ZeroDensity.Ingham.zetaAfeDefs

namespace Work.ZeroDensity.Ingham

open Work.ZeroDensity.Ingham
open Complex MeasureTheory Set
open scoped Topology BigOperators Real

/-- The functional-equation factor `χ(z) = Γℝ(1-z)/Γℝ z` written as the classical expression
`z·Γ(-z)·sin(-πz/2)·(2π)^z/π` (equivalently `2^z π^{z-1} sin(πz/2) Γ(1-z)`).  This is the constant
`c₀(2π)^s/π` of the Euler–Maclaurin + sawtooth computation of the approximate functional
equation, multiplied by the factor `s` coming from the `-s ∫ ({u}-1/2)u^{-s-1}du` term. -/
theorem chi_eq_gamma_sin (z : ℂ) (hz0 : 0 < z.re) (hz1 : z.re < 1) :
    zetaChi z =
      z * Complex.Gamma (-z) * Complex.sin (-(Real.pi : ℂ) * z / 2) *
        (2 * (Real.pi : ℂ)) ^ z / (Real.pi : ℂ) := by
  have hzne : z ≠ 0 := by
    intro h; rw [h] at hz0; simp at hz0
  -- `1 - z` is never a negative odd integer, because `0 < Re z < 1`
  have hcond : ∀ n : ℕ, (1 : ℂ) - z ≠ -(2 * (n : ℂ) + 1) := by
    intro n h
    have hre : (1 - z).re = (-(2 * (n : ℂ) + 1)).re := by rw [h]
    simp at hre
    have hn : (0 : ℝ) ≤ (n : ℝ) := Nat.cast_nonneg n
    nlinarith [hz1, hn]
  -- reflection formula in the form supplied by Mathlib for `Gammaℝ`
  have hmain : zetaChi z =
      Complex.Gammaℂ (1 - z) * Complex.cos ((Real.pi : ℂ) * (1 - z) / 2) := by
    have key := Complex.Gammaℝ_div_Gammaℝ_one_sub (s := (1 : ℂ) - z) hcond
    have h1 : (1 : ℂ) - (1 - z) = z := by ring
    rw [h1] at key
    simpa [zetaChi] using key
  have hcos : Complex.cos ((Real.pi : ℂ) * (1 - z) / 2) =
      Complex.sin ((Real.pi : ℂ) * z / 2) := by
    have h : (Real.pi : ℂ) * (1 - z) / 2 =
        (Real.pi : ℂ) / 2 - (Real.pi : ℂ) * z / 2 := by ring
    rw [h, Complex.cos_pi_div_two_sub]
  have hGℂ : Complex.Gammaℂ (1 - z) =
      2 * (2 * (Real.pi : ℂ)) ^ (z - 1) * Complex.Gamma (1 - z) := by
    rw [Complex.Gammaℂ_def, show -(1 - z) = z - 1 by ring]
  have hL : zetaChi z = 2 * (2 * (Real.pi : ℂ)) ^ (z - 1) *
      (Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z / 2)) := by
    rw [hmain, hcos, hGℂ]
    ring
  -- rewrite `z * Γ(-z)` and `sin (-πz/2)` using the functional equations
  have hGam : z * Complex.Gamma (-z) = - Complex.Gamma (1 - z) := by
    have h := Complex.Gamma_add_one (-z) (neg_ne_zero.mpr hzne)
    rw [show (-z + 1 : ℂ) = 1 - z by ring] at h
    rw [h]; ring
  have hsin : Complex.sin (-(Real.pi : ℂ) * z / 2) =
      - Complex.sin ((Real.pi : ℂ) * z / 2) := by
    rw [show -(Real.pi : ℂ) * z / 2 = -((Real.pi : ℂ) * z / 2) by ring, Complex.sin_neg]
  have hcf : (2 * (Real.pi : ℂ)) ^ z / (Real.pi : ℂ) =
      2 * (2 * (Real.pi : ℂ)) ^ (z - 1) := by
    have hx : (2 * (Real.pi : ℂ)) ≠ 0 :=
      mul_ne_zero two_ne_zero (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)
    have hpi : (Real.pi : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr Real.pi_ne_zero
    have h2π : (2 * (Real.pi : ℂ)) ^ z =
        (2 * (Real.pi : ℂ)) ^ (z - 1) * (2 * (Real.pi : ℂ)) := by
      conv_lhs => rw [show z = (z - 1) + 1 by ring]
      rw [Complex.cpow_add (z - 1) 1 hx, Complex.cpow_one]
    rw [h2π]
    field_simp
  have hR : z * Complex.Gamma (-z) * Complex.sin (-(Real.pi : ℂ) * z / 2) *
        (2 * (Real.pi : ℂ)) ^ z / (Real.pi : ℂ) =
      2 * (2 * (Real.pi : ℂ)) ^ (z - 1) *
        (Complex.Gamma (1 - z) * Complex.sin ((Real.pi : ℂ) * z / 2)) := by
    have hrw : z * Complex.Gamma (-z) * Complex.sin (-(Real.pi : ℂ) * z / 2) *
          (2 * (Real.pi : ℂ)) ^ z / (Real.pi : ℂ) =
        (z * Complex.Gamma (-z)) * Complex.sin (-(Real.pi : ℂ) * z / 2) *
          ((2 * (Real.pi : ℂ)) ^ z / (Real.pi : ℂ)) := by ring
    rw [hrw, hGam, hsin, hcf]
    ring
  rw [hL, hR]

end Work.ZeroDensity.Ingham
