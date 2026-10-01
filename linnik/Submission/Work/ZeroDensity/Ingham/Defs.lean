import Mathlib

/-!
# The Ingham zero-density chapter for the Riemann zeta function — vocabulary

This module is the vocabulary of the formalisation of **Ingham's zero-density estimate for the
Riemann zeta function**,

`N(σ,T) ≤ C_ε T^{3(1-σ)/(2-σ)+ε}`  for  `1/2 ≤ σ ≤ 1`, `T ≥ 1`,

i.e. of the `q = Q = 1` case of the Montgomery–Vaughan proof (Montgomery–Vaughan,
*Multiplicative Number Theory*, Chapter 28, (28.30)); the route is §28.4.1 of that book.

With `H` a large multiple of `T` and parameters `C ≤ K ≤ H`, `Y ≥ 1`, `Z = Y (log H)²` one
considers the truncated Möbius mollifier `M_K` of (28.7) and the coefficients `a_K(n)` of (28.35),
which satisfy

`ζ(s)·M_K(s) = Σ_{n≥1} a_K(n) n^{-s}`   (`Re s > 1`),

`a_K(1) = 1`, and `a_K(n) = 0` for `2 ≤ n ≤ K`.  At a zero `ρ` of `ζ` the identity
`ζ(ρ) M_K(ρ) = 0` produces the *zero detector* (28.39): the tail
`Σ_{K < n ≤ Z} a_K(n) n^{-ρ} e^{-n/Y}` is large, or the critical-line integral
`∫ ζ(1/2+iγ+iv) M_K(1/2+iγ+iv) Y^{1/2-β+iv} Γ(1/2-β+iv) dv` is large.

This file contains the definitions and their elementary properties; nothing deep.
-/

open scoped Classical BigOperators

namespace Work.ZeroDensity.Ingham

/-- **The truncated Möbius coefficient** `a_K(n) = Σ_{d | n, d ≤ K} μ(d)` (M&V (28.35)). -/
noncomputable def mCoef (K : ℕ) (n : ℕ) : ℂ :=
  ∑ d ∈ (Nat.divisors n).filter (fun d => d ≤ K), (ArithmeticFunction.moebius d : ℂ)

/-- **The truncated Möbius polynomial** `M_K(s) = Σ_{n=1}^{K} μ(n) n^{-s}` (M&V (28.7)). -/
noncomputable def MK (K : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s)

lemma MK_apply (K : ℕ) (s : ℂ) :
    MK K s = ∑ n ∈ Finset.Icc 1 K, (ArithmeticFunction.moebius n : ℂ) * (n : ℂ) ^ (-s) := rfl

/-- The Dirichlet convolution of `μ` with the constant-`1` series: `Σ_{d | n} μ(d) = [n = 1]`. -/
lemma sum_moebius_divisors_castC (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℂ)) = if n = 1 then 1 else 0 := by
  have h := congrArg (fun f : ArithmeticFunction ℂ => f n)
      (ArithmeticFunction.coe_moebius_mul_coe_zeta (R := ℂ))
  rw [ArithmeticFunction.coe_mul_zeta_apply, ArithmeticFunction.one_apply] at h
  exact h

lemma mCoef_one (K : ℕ) (hK : 1 ≤ K) : mCoef K 1 = 1 := by
  rw [mCoef]
  have hset : (Nat.divisors 1).filter (fun d => d ≤ K) = {1} := by
    ext d
    simp only [Nat.divisors_one, Finset.mem_filter, Finset.mem_singleton]
    constructor
    · rintro ⟨h, -⟩; exact h
    · intro h; subst h; exact ⟨rfl, hK⟩
  rw [hset, Finset.sum_singleton]
  norm_num

/-- For `2 ≤ n ≤ K` the truncated Möbius coefficient vanishes: `a_K(n) = Σ_{d|n} μ(d) = [n = 1]`. -/
lemma mCoef_eq_zero {K n : ℕ} (hn : 2 ≤ n) (hnK : n ≤ K) : mCoef K n = 0 := by
  rw [mCoef]
  have hfilt : (Nat.divisors n).filter (fun d => d ≤ K) = Nat.divisors n := by
    refine Finset.filter_true_of_mem ?_
    intro d hd
    exact le_trans (Nat.le_of_dvd (by omega) (Nat.mem_divisors.mp hd).1) hnK
  rw [hfilt, sum_moebius_divisors_castC n]
  simp [show n ≠ 1 by omega]

/-- The truncated Möbius coefficient is bounded by the divisor function. -/
lemma norm_mCoef_le_tau (K n : ℕ) : ‖mCoef K n‖ ≤ ((Nat.divisors n).card : ℝ) := by
  rw [mCoef]
  refine le_trans (norm_sum_le _ _) ?_
  have h1 : ∀ d ∈ (Nat.divisors n).filter (fun d => d ≤ K),
      ‖(ArithmeticFunction.moebius d : ℂ)‖ ≤ 1 := by
    intro d _
    rw [Complex.norm_intCast]
    by_cases h : Squarefree d
    · rw [ArithmeticFunction.moebius_apply_of_squarefree h]
      norm_num
    · rw [ArithmeticFunction.moebius_eq_zero_of_not_squarefree h]
      norm_num
  calc ∑ d ∈ (Nat.divisors n).filter (fun d => d ≤ K), ‖(ArithmeticFunction.moebius d : ℂ)‖
      ≤ ∑ _d ∈ (Nat.divisors n).filter (fun d => d ≤ K), (1 : ℝ) := Finset.sum_le_sum h1
    _ = (((Nat.divisors n).filter (fun d => d ≤ K)).card : ℝ) := by simp
    _ ≤ ((Nat.divisors n).card : ℝ) := by
        exact_mod_cast Finset.card_le_card (Finset.filter_subset _ _)

end Work.ZeroDensity.Ingham
