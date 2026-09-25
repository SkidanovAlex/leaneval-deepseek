import Mathlib
import Submission.Work.NN.Core.poly_interp_bound
import Submission.Work.NN.Core.taylor_remainder_bound

namespace Work.NN.Core

open Polynomial

/-! # The one-dimensional finite-difference interpolation inequality

For `j ≤ k` there are constants `A, D ≥ 0` such that every `C^k` map `ψ : ℝ → ℂ` whose values and
whose `k`-th derivative are bounded by `S₀` and `S_k` on the interval `[0, k h]` satisfies

  `‖ψ^{(j)}(0)‖ ≤ A / h ^ j * S₀ + D * h ^ (k - j) * S_k`.

The proof uses the Taylor polynomial `P_ψ` of `ψ` at `0` of degree `k - 1`: its `j`-th coefficient
is `ψ^{(j)}(0)`, and its values at the `k` points `0, h, …, (k-1)h` differ from those of `ψ` by the
Taylor remainder, bounded in terms of `S_k`.  The pure polynomial interpolation bound
`poly_interp_bound` then controls `(P_ψ)^{(j)}(0)` by those `k` values. -/

/-- The formal Taylor polynomial of `ψ` at `0` of degree `k - 1`, as an element of `ℂ[X]`. -/
noncomputable def taylorPolynomial (k : ℕ) (ψ : ℝ → ℂ) : Polynomial ℂ :=
  ∑ l ∈ Finset.range k, Polynomial.C (iteratedDeriv l ψ 0 / (l.factorial : ℂ)) * Polynomial.X ^ l

/-- The `j`-th formal derivative of the Taylor polynomial evaluated at `0` recovers the `j`-th
derivative of `ψ` at `0`, for `j < k`. -/
lemma taylorPolynomial_deriv_eval {k j : ℕ} (hjk : j < k) (ψ : ℝ → ℂ) :
    (Polynomial.derivative^[j] (taylorPolynomial k ψ)).eval 0 = iteratedDeriv j ψ 0 := by
  rw [taylorPolynomial, Polynomial.iterate_derivative_sum]
  simp only [Polynomial.iterate_derivative_C_mul, Polynomial.iterate_derivative_X_pow_eq_C_mul]
  rw [Polynomial.eval_finsetSum]
  simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]
  rw [Finset.sum_eq_single j]
  · simp only [Nat.descFactorial_self, Nat.sub_self, pow_zero, mul_one]
    rw [div_mul_cancel₀ _ (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero j))]
  · intro l hl hne
    rcases lt_or_gt_of_ne hne with h | h
    · rw [Nat.descFactorial_eq_zero_iff_lt.mpr h]; simp
    · rw [zero_pow (by omega : l - j ≠ 0)]; ring
  · intro h; exact absurd (Finset.mem_range.mpr hjk) h

/-- Evaluating the Taylor polynomial at `t` gives the usual Taylor sum. -/
lemma taylorPolynomial_eval (k : ℕ) (ψ : ℝ → ℂ) (t : ℝ) :
    (taylorPolynomial k ψ).eval (t : ℂ)
      = ∑ l ∈ Finset.range k, ((l.factorial : ℝ)⁻¹ * t ^ l) • iteratedDeriv l ψ 0 := by
  rw [taylorPolynomial]
  simp only [Polynomial.eval_finsetSum, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X]
  apply Finset.sum_congr rfl
  intro x hx
  rw [Complex.real_smul, Complex.ofReal_mul, Complex.ofReal_inv, Complex.ofReal_natCast,
    Complex.ofReal_pow]
  ring

theorem oneDim_finitediff_interp {k j : ℕ} (hjk : j ≤ k) :
    ∃ A D : ℝ, 0 ≤ A ∧ 0 ≤ D ∧
      ∀ (ψ : ℝ → ℂ) (h : ℝ), 0 < h → ContDiff ℝ k ψ →
        ∀ (S0 Sk : ℝ), 0 ≤ S0 → 0 ≤ Sk →
          (∀ t ∈ Set.Icc 0 (k * h), ‖ψ t‖ ≤ S0) →
          (∀ t ∈ Set.Icc 0 (k * h), ‖iteratedDeriv k ψ t‖ ≤ Sk) →
          ‖iteratedDeriv j ψ 0‖ ≤ A / h ^ j * S0 + D * h ^ (k - j) * Sk
:= by
  rcases eq_or_lt_of_le hjk with hjk_eq | hjk_lt
  · subst j
    refine ⟨0, 1, le_refl 0, zero_le_one, ?_⟩
    intro ψ h hh hψ S0 Sk hS0 hSk h0 hk
    have hmem : (0:ℝ) ∈ Set.Icc 0 (k * h) := ⟨le_refl _, by positivity⟩
    have hb : ‖iteratedDeriv k ψ 0‖ ≤ Sk := hk 0 hmem
    have hpow : h ^ (k - k) = 1 := by simp
    calc ‖iteratedDeriv k ψ 0‖ ≤ Sk := hb
      _ = 0 / h ^ k * S0 + 1 * h ^ (k - k) * Sk := by rw [hpow]; ring
  · obtain ⟨C, hC0, hC⟩ := poly_interp_bound hjk_lt
    have hk1 : 1 ≤ k := by omega
    have hD0 : 0 ≤ C * (k:ℝ) * (k:ℝ)^k / ((k-1).factorial : ℝ) :=
      div_nonneg (mul_nonneg (mul_nonneg hC0 (by positivity)) (by positivity)) (by positivity)
    refine ⟨C * (k:ℝ), C * (k:ℝ) * (k:ℝ)^k / ((k-1).factorial : ℝ), by positivity, hD0, ?_⟩
    intro ψ h hh hψ S0 Sk hS0 hSk h0 hk
    have hPdeg : (taylorPolynomial k ψ).degree < k := by
      rw [taylorPolynomial, ← Polynomial.mem_degreeLT]
      apply Submodule.sum_mem
      intro l hl
      rw [Polynomial.mem_degreeLT]
      exact lt_of_le_of_lt (Polynomial.degree_C_mul_X_pow_le l _)
        (by exact_mod_cast (Finset.mem_range.mp hl))
    have hderiv : (Polynomial.derivative^[j] (taylorPolynomial k ψ)).eval 0 = iteratedDeriv j ψ 0 :=
      taylorPolynomial_deriv_eval hjk_lt ψ
    have hinterp := hC (taylorPolynomial k ψ) h hh hPdeg
    rw [hderiv] at hinterp
    have hterm0 : ∀ i ∈ Finset.range k,
        ‖(taylorPolynomial k ψ).eval (((i:ℝ) * h : ℝ) : ℂ)‖
          ≤ S0 + (((i:ℝ)*h)^k / ((k-1).factorial:ℝ)) * Sk := by
      intro i hi
      have hik : (i:ℝ) ≤ (k:ℝ) := by exact_mod_cast (le_of_lt (Finset.mem_range.mp hi))
      have ht : ((i:ℝ)*h) ∈ Set.Icc 0 (k * h) :=
        ⟨by positivity, by exact mul_le_mul_of_nonneg_right hik (le_of_lt hh)⟩
      have hb := taylor_remainder_bound hk1 ψ h hh hψ Sk hSk hk ((i:ℝ)*h) ht
      rw [taylorPolynomial_eval]
      calc ‖∑ l ∈ Finset.range k, ((l.factorial : ℝ)⁻¹ * ((i:ℝ)*h) ^ l) • iteratedDeriv l ψ 0‖
          = ‖ψ ((i:ℝ)*h) - (ψ ((i:ℝ)*h) - ∑ l ∈ Finset.range k,
              ((l.factorial : ℝ)⁻¹ * ((i:ℝ)*h) ^ l) • iteratedDeriv l ψ 0)‖ := by
              congr 1; ring
        _ ≤ ‖ψ ((i:ℝ)*h)‖ + ‖ψ ((i:ℝ)*h) - ∑ l ∈ Finset.range k,
              ((l.factorial : ℝ)⁻¹ * ((i:ℝ)*h) ^ l) • iteratedDeriv l ψ 0‖ := norm_sub_le _ _
        _ ≤ S0 + (((i:ℝ)*h)^k / ((k-1).factorial:ℝ)) * Sk := add_le_add (h0 _ ht) hb
    have hterm : ∀ i ∈ Finset.range k,
        ‖(taylorPolynomial k ψ).eval (((i:ℝ) * h : ℝ) : ℂ)‖
          ≤ S0 + (((k:ℝ)*h)^k / ((k-1).factorial:ℝ)) * Sk := by
      intro i hi
      have hik : (i:ℝ) ≤ (k:ℝ) := by exact_mod_cast (le_of_lt (Finset.mem_range.mp hi))
      have hle : ((i:ℝ)*h)^k ≤ ((k:ℝ)*h)^k :=
        pow_le_pow_left₀ (by positivity) (mul_le_mul_of_nonneg_right hik (le_of_lt hh)) k
      have hXY : (((i:ℝ)*h)^k / ((k-1).factorial:ℝ)) * Sk
          ≤ (((k:ℝ)*h)^k / ((k-1).factorial:ℝ)) * Sk :=
        mul_le_mul_of_nonneg_right (div_le_div_of_nonneg_right hle (by positivity)) hSk
      linarith [hterm0 i hi]
    have hsum : (∑ i ∈ Finset.range k, ‖(taylorPolynomial k ψ).eval (((i:ℝ)*h:ℝ):ℂ)‖)
        ≤ (k:ℝ) * (S0 + (((k:ℝ)*h)^k / ((k-1).factorial:ℝ)) * Sk) := by
      calc ∑ i ∈ Finset.range k, ‖(taylorPolynomial k ψ).eval (((i:ℝ)*h:ℝ):ℂ)‖
          ≤ ∑ i ∈ Finset.range k, (S0 + (((k:ℝ)*h)^k / ((k-1).factorial:ℝ)) * Sk) :=
              Finset.sum_le_sum hterm
        _ = (k:ℝ) * (S0 + (((k:ℝ)*h)^k / ((k-1).factorial:ℝ)) * Sk) := by
              rw [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    calc ‖iteratedDeriv j ψ 0‖
        ≤ (C * ∑ i ∈ Finset.range k, ‖(taylorPolynomial k ψ).eval (((i:ℝ)*h:ℝ):ℂ)‖) / h^j :=
            hinterp
      _ ≤ (C * ((k:ℝ) * (S0 + (((k:ℝ)*h)^k / ((k-1).factorial:ℝ)) * Sk))) / h^j := by
            apply div_le_div_of_nonneg_right _ (by positivity)
            exact mul_le_mul_of_nonneg_left hsum hC0
      _ = C * (k:ℝ) / h^j * S0 + C * (k:ℝ) * (k:ℝ)^k / ((k-1).factorial:ℝ) * h^(k-j) * Sk := by
            rw [pow_sub₀ h hh.ne' (le_of_lt hjk_lt)]
            field_simp
            ring

end Work.NN.Core
