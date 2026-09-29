import Mathlib

/-!
# TMC14Core: the even local expansion `p = c₀ + X²·b`

Let `p : ℂ[X]` be an even polynomial, `p(-z) = p(z)` for all `z : ℂ`.  Then every
odd-degree coefficient of `p` vanishes, so that `p - C (p 0)` is divisible by `X²`:
there is `b` with `p = C c₀ + X²·b`, and the constant term of `b` is the coefficient of
`X²` in `p`, namely `p''(0)/2`.

* `evenCoeffOdd`: the parity statement — an even complex polynomial has no odd-degree
  coefficients.  It is proved by differentiating the polynomial identity `p(-X) = p`:
  the `k`-th derivative of an even polynomial is even for even `k` and odd for odd `k`,
  hence every odd derivative vanishes at `0`; dividing by `k!` (using
  `Polynomial.coeff_iterate_derivative`) gives the vanishing of the odd coefficients.
* `evenLocalExpansion`: the expansion used by the local analysis of `disc p q lam` at
  the origin (see `evenLocalBound`).
-/

namespace Work.TMC14Core

/-- **Even polynomials over `ℂ` have no odd coefficients.**

If `p(-z) = p(z)` for all `z : ℂ`, then `p.coeff n = 0` for every odd `n`. -/
theorem evenCoeffOdd (p : Polynomial ℂ) (heven : ∀ z : ℂ, p.eval (-z) = p.eval z) :
    ∀ n : ℕ, Odd n → p.coeff n = 0 := by
  -- evenness is an identity of polynomials
  have hcomp : p.comp (-Polynomial.X) = p := by
    apply Polynomial.funext
    intro z
    simpa using heven z
  -- the `k`-th derivative picks up the sign `(-1)^k` under `X ↦ -X`
  have key : ∀ k : ℕ,
      ((Polynomial.derivative^[k] p).comp (-Polynomial.X)) =
        (-1 : ℂ) ^ k • (Polynomial.derivative^[k] p) := by
    intro k
    induction k with
    | zero => simpa using hcomp
    | succ k ih =>
      have hone : (Polynomial.derivative^[k+1] p)
          = Polynomial.derivative (Polynomial.derivative^[k] p) :=
        Function.iterate_succ_apply' Polynomial.derivative k p
      have h := congrArg Polynomial.derivative ih
      rw [Polynomial.derivative_comp, Polynomial.derivative_neg, Polynomial.derivative_X,
        Polynomial.derivative_smul, neg_one_mul, neg_eq_iff_eq_neg] at h
      rw [hone, h, pow_succ, ← neg_smul,
        show -((-1 : ℂ) ^ k) = (-1 : ℂ) ^ k * (-1) from by
          rw [neg_eq_neg_one_mul, mul_comm]]
  intro n hn
  -- every odd derivative vanishes at the origin
  have hq : ((Polynomial.derivative^[n] p).eval 0) = 0 := by
    have h := key n
    rw [hn.neg_one_pow] at h
    have h2 := congrArg (fun q : Polynomial ℂ => q.eval (0 : ℂ)) h
    simp only [Polynomial.eval_comp, Polynomial.eval_neg, Polynomial.eval_X, neg_zero,
      Polynomial.smul_eq_C_mul, Polynomial.eval_C_mul, neg_one_mul] at h2
    have h3 : (Polynomial.derivative^[n] p).eval 0 + (Polynomial.derivative^[n] p).eval 0 = 0 :=
      eq_neg_iff_add_eq_zero.mp h2
    have h4 : (2 : ℂ) * ((Polynomial.derivative^[n] p).eval 0) = 0 := by
      rw [two_mul]; exact h3
    exact (mul_eq_zero.mp h4).resolve_left (by norm_num)
  -- the `n`-th derivative at `0` is `n!` times the `n`-th coefficient
  have hcoeff : ((Polynomial.derivative^[n] p)).coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]; exact hq
  have hcd := Polynomial.coeff_iterate_derivative (k := n) p 0
  rw [hcoeff, Nat.zero_add, Nat.descFactorial_self, nsmul_eq_mul] at hcd
  exact (mul_eq_zero.mp hcd.symm).resolve_left
    (Nat.cast_ne_zero.mpr (Nat.factorial_ne_zero n))

/-- **TMC14Core: expansion of an even complex polynomial around `0`.**

An even polynomial `p : ℂ[X]` with `p(0) = c₀` and `p''(0) = c₂` (`c₀ c₂ : ℝ`) can be
written `p = C c₀ + X²·b` with `b(0) = c₂/2`. -/
theorem evenLocalExpansion (p : Polynomial ℂ)
    (heven : ∀ z : ℂ, p.eval (-z) = p.eval z)
    (c0 c2 : ℝ) (hc0 : p.eval (0 : ℂ) = (c0 : ℂ))
    (hc2 : (Polynomial.derivative (Polynomial.derivative p)).eval 0 = (c2 : ℂ)) :
    ∃ b : Polynomial ℂ, p = Polynomial.C (c0 : ℂ) + Polynomial.X ^ 2 * b ∧
      b.eval 0 = ((c2 / 2 : ℝ) : ℂ) := by
  have hodd : ∀ n : ℕ, Odd n → p.coeff n = 0 := evenCoeffOdd p heven
  -- the second derivative at `0` is twice the coefficient of `X²`
  have hd2 : (Polynomial.derivative (Polynomial.derivative p)).coeff 0 = 2 * p.coeff 2 := by
    rw [Polynomial.coeff_derivative, Polynomial.coeff_derivative]
    ring_nf
  have hcoeff0 : p.coeff 0 = (c0 : ℂ) := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hc0]
  -- `p - C c₀` has vanishing coefficients in degrees `0` and `1`, hence `X² ∣ p - C c₀`
  have hq0 : (p - Polynomial.C (c0 : ℂ)).coeff 0 = 0 := by
    rw [Polynomial.coeff_sub, Polynomial.coeff_C_zero, hcoeff0, sub_self]
  have hq1 : (p - Polynomial.C (c0 : ℂ)).coeff 1 = 0 := by
    rw [Polynomial.coeff_sub, hodd 1 ⟨0, by norm_num⟩, Polynomial.coeff_C,
      if_neg (by norm_num : ¬ ((1:ℕ) = 0)), sub_zero]
  have hdvd : Polynomial.X ^ 2 ∣ p - Polynomial.C (c0 : ℂ) := by
    rw [Polynomial.X_pow_dvd_iff]
    intro d hd
    interval_cases d
    · exact hq0
    · exact hq1
  obtain ⟨b, hb⟩ := hdvd
  refine ⟨b, ?_, ?_⟩
  · rw [sub_eq_iff_eq_add] at hb
    exact hb.trans (add_comm _ _)
  · have hbcoeff : b.coeff 0 = p.coeff 2 := by
      have h := congrArg (fun q : Polynomial ℂ => q.coeff 2) hb
      rw [Polynomial.coeff_sub, Polynomial.coeff_C] at h
      rw [if_neg (by norm_num : ¬ ((2:ℕ) = 0)), sub_zero] at h
      have he : (Polynomial.X ^ 2 * b).coeff 2 = b.coeff 0 := by
        simpa using Polynomial.coeff_X_pow_mul b 2 0
      exact he.symm.trans h.symm
    have h2 : (2 : ℂ) * p.coeff 2 = (c2 : ℂ) := by
      have h := hc2
      rw [← Polynomial.coeff_zero_eq_eval_zero, hd2] at h
      exact h
    have hpc2 : p.coeff 2 = (c2 : ℂ) / 2 := by
      rw [eq_div_iff (by norm_num : (2 : ℂ) ≠ 0), mul_comm]
      exact h2
    have hcast : ((c2 / 2 : ℝ) : ℂ) = (c2 : ℂ) / 2 := by
      push_cast
      ring
    rw [← Polynomial.coeff_zero_eq_eval_zero, hbcoeff, hpc2]
    exact hcast.symm

end Work.TMC14Core
