/-
# `Submission.Work.FIArea5.S16Hecke.conv_pow_four`

The value at a prime power `p ^ e` of the four-fold Dirichlet convolution of arbitrary
sequences `f₁, f₂, f₃, f₄ : ℕ → ℂ` is the four-fold Cauchy product (`cvs`) of the local
sequences `k ↦ fᵢ (p ^ k)`.

The mathematical content is the fact that the only divisors of `p ^ e` are the powers
`p ^ i`, `0 ≤ i ≤ e`, so that the Dirichlet convolution at `p ^ e` becomes a convolution
over `+` on the exponents.  The two-fold statement is `conv_apply_prime_pow` /
`conv_pow_eq_cvs` below; the four-fold statement follows by using it three times, together
with the function-level form `conv_pow_eq_cvs`.
-/
import Mathlib
import Submission.Work.FIArea5.S16Hecke.conv_defs

set_option autoImplicit false

namespace Work.FIArea5.S16Hecke

open Finset
open scoped BigOperators

noncomputable section

/-- Reindexing at a prime power: the antidiagonal of the divisors of `p ^ e` is parametrised
by the exponents `i ≤ e`, the two factors being `p ^ i` and `p ^ (e - i)`. -/
lemma sum_divisorsAntidiagonal_prime_pow {p : ℕ} (hp : p.Prime) (e : ℕ) (F G : ℕ → ℂ) :
    (∑ i ∈ Finset.range (e + 1), F (p ^ i) * G (p ^ (e - i)))
      = ∑ x ∈ (p ^ e).divisorsAntidiagonal, F x.1 * G x.2 := by
  have hp2 : 2 ≤ p := hp.two_le
  refine Finset.sum_bij (fun a _ => (p ^ a, p ^ (e - a))) ?_ ?_ ?_ ?_
  · intro a ha
    rw [Nat.mem_divisorsAntidiagonal]
    refine ⟨?_, pow_ne_zero e hp.ne_zero⟩
    rw [← pow_add, Nat.add_sub_of_le (by rw [Finset.mem_range] at ha; omega)]
  · intro a₁ _ a₂ _ h
    simp only [Prod.mk.injEq] at h
    exact Nat.pow_right_injective hp2 h.1
  · intro x hx
    rw [Nat.mem_divisorsAntidiagonal] at hx
    obtain ⟨hxprod, _⟩ := hx
    have hdvd : x.1 ∣ p ^ e := ⟨x.2, hxprod.symm⟩
    obtain ⟨k, hk, hk1⟩ := (Nat.dvd_prime_pow hp).mp hdvd
    refine ⟨k, ?_, ?_⟩
    · rw [Finset.mem_range]; omega
    · have hx2 : x.2 = p ^ (e - k) := by
        refine Nat.mul_left_cancel (pow_pos hp.pos k) ?_
        rw [← hk1, hxprod, hk1, ← pow_add, Nat.add_sub_of_le hk]
      rw [← hk1, ← hx2]
  · intro a _
    rfl

/-- Dirichlet convolution at a prime power: `(f ⍟ g) (p ^ e)` is the Cauchy product of the
local sequences `k ↦ f (p ^ k)`, `k ↦ g (p ^ k)`. -/
theorem conv_apply_prime_pow (f g : ℕ → ℂ) {p : ℕ} (hp : p.Prime) (e : ℕ) :
    LSeries.convolution f g (p ^ e)
      = cvs (fun k => f (p ^ k)) (fun k => g (p ^ k)) e := by
  rw [LSeries.convolution_def, cvs]
  exact (sum_divisorsAntidiagonal_prime_pow hp e f g).symm

/-- The same, as an equality of sequences in the exponent. -/
theorem conv_pow_eq_cvs (f g : ℕ → ℂ) {p : ℕ} (hp : p.Prime) :
    (fun k => LSeries.convolution f g (p ^ k))
      = cvs (fun k => f (p ^ k)) (fun k => g (p ^ k)) := by
  funext e
  exact conv_apply_prime_pow f g hp e

/-- The value at `p ^ e` of a four-fold Dirichlet convolution equals the four-fold Cauchy
product of the local (prime power) sequences. -/
theorem conv_pow_four (f₁ f₂ f₃ f₄ : ℕ → ℂ) (p : ℕ) (hp : p.Prime) (e : ℕ) :
    LSeries.convolution (LSeries.convolution (LSeries.convolution f₁ f₂) f₃) f₄ (p ^ e)
      = Work.FIArea5.S16Hecke.cvs
          (Work.FIArea5.S16Hecke.cvs
            (Work.FIArea5.S16Hecke.cvs (fun k => f₁ (p ^ k)) (fun k => f₂ (p ^ k)))
            (fun k => f₃ (p ^ k)))
          (fun k => f₄ (p ^ k)) e := by
  have h1 := conv_pow_eq_cvs f₁ f₂ hp
  have h2 := conv_pow_eq_cvs (LSeries.convolution f₁ f₂) f₃ hp
  have h3 := conv_pow_eq_cvs (LSeries.convolution (LSeries.convolution f₁ f₂) f₃) f₄ hp
  rw [h2, h1] at h3
  exact congrFun h3 e

end

end Work.FIArea5.S16Hecke
