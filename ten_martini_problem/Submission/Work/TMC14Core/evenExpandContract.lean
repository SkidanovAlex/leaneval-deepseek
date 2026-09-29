import Mathlib

namespace Work.TMC14Core

open Polynomial

/-- An even polynomial (as a function on `ℂ`) has only even-degree coefficients, so
contracting then expanding by `2` returns it. -/
theorem evenExpandContract (p : Polynomial ℂ) (heven : ∀ z : ℂ, p.eval (-z) = p.eval z) :
    p = Polynomial.expand ℂ 2 (Polynomial.contract 2 p) := by
  -- Evenness forces `p(-X) = p` as polynomials, since they agree as functions on `ℂ`.
  have hcomp : p.comp (-X) = p := by
    apply Polynomial.funext
    intro z
    simp only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X]
    exact heven z
  -- Hence `p.coeff n = p.coeff n * (-1)^n` for every `n`.
  have hcoeff : ∀ n, p.coeff n = p.coeff n * ((-1 : ℂ) ^ n) := by
    intro n
    have h1 : (p.comp (-X)).coeff n = p.coeff n * ((-1 : ℂ) ^ n) := by
      have hh := Polynomial.comp_C_mul_X_coeff (p := p) (r := (-1 : ℂ)) (n := n)
      simpa using hh
    have h2 : (p.comp (-X)).coeff n = p.coeff n := by rw [hcomp]
    exact h2.symm.trans h1
  ext n
  rw [Polynomial.coeff_expand (by norm_num : (0 : ℕ) < 2),
    Polynomial.coeff_contract (by norm_num : (2 : ℕ) ≠ 0)]
  by_cases h : 2 ∣ n
  · rw [if_pos h, Nat.div_mul_cancel h]
  · rw [if_neg h]
    -- Odd-degree coefficients vanish.
    have hodd : Odd n := Nat.not_even_iff_odd.mp (fun he => h (even_iff_two_dvd.mp he))
    have hh := hcoeff n
    simp only [hodd.neg_one_pow, mul_neg, mul_one] at hh
    have h2 : (2 : ℂ) * p.coeff n = 0 := by
      rw [two_mul]
      nth_rewrite 2 [hh]
      rw [add_neg_cancel]
    exact (mul_eq_zero.mp h2).resolve_left (by norm_num)

end Work.TMC14Core
