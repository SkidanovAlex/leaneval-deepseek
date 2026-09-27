import Mathlib
import Submission.Work.EQ.Defs
import Submission.Work.EQ.germ_value_defs

/-!
# Non-vanishing of `P2p N D ℓ` at `ℓ = eqLam a`

`P2p N D ℓ = N(ℓu)·D(u) - N(u)·D(ℓu)` is the common denominator of the semi-projective
`x`-coordinate `X = Λ/P2` of the germ (see `germ_value_defs`).  The point of the present file
is that under the standing hypotheses on `N` and `D` (`N(0) = 0`, `N'(0) ≠ 0`, `D(0) ≠ 0`) and
with `ℓ = λ(a) = (1-a)/(1+a)`, `a > 0`, this denominator is *not* the zero polynomial.

The mechanism is completely explicit: the coefficient of `u` in `P2p N D ℓ` is
`(N' (0) · D(0) - N(0) · D'(0)) · (ℓ - 1)`, the bracket being `N.coeff 1 * D.coeff 0 -
N.coeff 0 * D.coeff 1`.  The hypotheses make the first factor nonzero and `ℓ ≠ 1` (indeed
`ℓ - 1 = -2a/(1+a) ≠ 0` for `a > 0`, so that also the degenerate case `a = 1`, `ℓ = 0`, is
covered).
-/

namespace Work.EQ

open Polynomial

/-- Coefficient formula for the dilation `p ↦ p.comp (C ℓ * X) = p(ℓ·X)`: the coefficient of
`X^n` is the coefficient of `X^n` in `p`, scaled by `ℓ^n`. -/
lemma P2p_comp_coeff (p : Polynomial ℂ) (ℓ : ℂ) (n : ℕ) :
    (p.comp (Polynomial.C ℓ * Polynomial.X)).coeff n = p.coeff n * ℓ ^ n := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
      simp only [Polynomial.add_comp, Polynomial.coeff_add]
      rw [hp, hq]; ring
  | monomial m a =>
      rw [Polynomial.monomial_comp, Polynomial.coeff_C_mul, Polynomial.coeff_monomial]
      have h1 : Polynomial.C ℓ * Polynomial.X = Polynomial.monomial 1 ℓ := by
        rw [← pow_one Polynomial.X, Polynomial.C_mul_X_pow_eq_monomial]
      rw [h1, Polynomial.monomial_pow, one_mul, Polynomial.coeff_monomial]
      by_cases h : m = n
      · subst h; simp
      · simp [h]

/-- The coefficient of `X` in `P2p N D ℓ = N(ℓX)·D - N·D(ℓX)`:
`(N.coeff 1 * D.coeff 0 - N.coeff 0 * D.coeff 1) * (ℓ - 1)`. -/
lemma P2p_coeff_one (N D : Polynomial ℂ) (ℓ : ℂ) :
    (P2p N D ℓ).coeff 1
      = (N.coeff 1 * D.coeff 0 - N.coeff 0 * D.coeff 1) * (ℓ - 1) := by
  rw [P2p, Polynomial.coeff_sub, Polynomial.mul_coeff_one, Polynomial.mul_coeff_one]
  simp only [P2p_comp_coeff, pow_zero, pow_one, mul_one]
  ring

theorem P2p_ne_zero {a : ℝ} (ha0 : 0 < a) {N D : Polynomial ℂ}
    (hN0 : Polynomial.eval 0 N = 0) (hNd : Polynomial.eval 0 (Polynomial.derivative N) ≠ 0)
    (hD0 : Polynomial.eval 0 D ≠ 0) :
    Work.EQ.P2p N D (Work.EQ.eqLam a : ℂ) ≠ 0 := by
  -- `N(0) = 0`, `N'(0) ≠ 0`, `D(0) ≠ 0` in coefficient form.
  have hN0c : N.coeff 0 = 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero, hN0]
  have hn1 : N.coeff 1 ≠ 0 := by
    have hd : (Polynomial.derivative N).coeff 0 = N.coeff 1 := by
      rw [Polynomial.coeff_derivative]; ring
    have hev : Polynomial.eval 0 (Polynomial.derivative N) = N.coeff 1 := by
      rw [← Polynomial.coeff_zero_eq_eval_zero, hd]
    intro h1; exact hNd (by rw [hev, h1])
  have hd0 : D.coeff 0 ≠ 0 := by
    rw [Polynomial.coeff_zero_eq_eval_zero]; exact hD0
  -- `eqLam a ≠ 1` because `eqLam a - 1 = -2a/(1+a)` with `a > 0`.
  have hℓ : ((Work.EQ.eqLam a : ℝ) : ℂ) - 1 ≠ 0 := by
    rw [sub_ne_zero]
    intro hc
    have hr : Work.EQ.eqLam a = 1 := Complex.ofReal_injective (by simpa using hc)
    rw [Work.EQ.eqLam] at hr
    have h1a : (1 + a) ≠ 0 := by positivity
    field_simp at hr
    linarith
  intro h
  -- if `P2p` vanished, its `X`-coefficient would vanish, but the latter is a product of
  -- three nonzero factors.
  have hc := P2p_coeff_one N D ((Work.EQ.eqLam a : ℂ))
  rw [h, hN0c] at hc
  simp only [Polynomial.coeff_zero, zero_mul, sub_zero] at hc
  exact (mul_ne_zero (mul_ne_zero hn1 hd0) hℓ) hc.symm

end Work.EQ
