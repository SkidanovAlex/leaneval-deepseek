/-
# ZeroFreeTables.XY — `KsumFiveNonneg`

The five-term positivity of the Heath-Brown `K`-sum that the `F`-method derivation
of the order-2 `λ₁`-estimate uses: with coefficients `14379, 24480, 14900, 6000, 1250`
attached to `K(β + i k γ, χ₁^k)` for `k = 0, …, 4` (where `χ₁` is a real character,
`χ₁² = 1`, so that `χ₁^k` is `1, χ₁, 1, χ₁, 1`), the total is non-negative.

The mechanism is the one of `Work.ZeroFreeTables.ksum_trigPoly_nonneg`: since
`Λ(n) ≥ 0` and `f ≥ 0`, it suffices that the Chebyshev polynomial

`P(x) = 14379 T₀(x) + 24480 T₁(x) + 14900 T₂(x) + 6000 T₃(x) + 1250 T₄(x)`

be non-negative on `[-1,1]`; and indeed

`P(x) = (100 x² + 120 x + 27)²`

is a perfect square.  This is the reason for the (otherwise arbitrary looking)
values of the five coefficients.
-/
import Mathlib
import Submission.Work.ZeroFreeTables.XY.XYEngineDefs
import Submission.Work.ZeroFreeTables.ksum_trigPoly_nonneg

open DirichletCharacter
open scoped Classical BigOperators

namespace Work.ZeroFreeTables.XY

/-- Coefficient vector of the five-term positivity combination. -/
def KsumFiveC : ℕ → ℝ
  | 0 => 14379
  | 1 => 24480
  | 2 => 14900
  | 3 => 6000
  | 4 => 1250
  | _ => 0

/-- `Kxy` is `Ksum` with the point `s` written as `β + i t`. -/
theorem Ksum_eq_Kxy {q : ℕ} [NeZero q] (f : ℝ → ℝ) (L β t : ℝ)
    (χ : DirichletCharacter ℂ q) :
    Work.ZeroFreeTables.Ksum q f L ((β : ℂ) + (t : ℂ) * Complex.I) χ = Kxy f L β t χ := rfl

/-- `T₃ = 2 X T₂ - T₁`. -/
lemma chebyshevT_three :
    Polynomial.Chebyshev.T ℝ 3
      = 2 * Polynomial.X * Polynomial.Chebyshev.T ℝ 2 - Polynomial.Chebyshev.T ℝ 1 := by
  have := Polynomial.Chebyshev.T_eq ℝ 3
  norm_num at this ⊢
  exact this

/-- `T₄ = 2 X T₃ - T₂`. -/
lemma chebyshevT_four :
    Polynomial.Chebyshev.T ℝ 4
      = 2 * Polynomial.X * Polynomial.Chebyshev.T ℝ 3 - Polynomial.Chebyshev.T ℝ 2 := by
  have := Polynomial.Chebyshev.T_eq ℝ 4
  norm_num at this ⊢
  exact this

/-- The Chebyshev combination `14379 T₀ + 24480 T₁ + 14900 T₂ + 6000 T₃ + 1250 T₄`
is the square `(100 x² + 120 x + 27)²`, hence non-negative on all of `ℝ`. -/
theorem KsumFiveChebyshev_eq (x : ℝ) :
    (∑ k ∈ Finset.range (4 + 1),
        KsumFiveC k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x)
      = (100 * x ^ 2 + 120 * x + 27) ^ 2 := by
  have h0 : (Polynomial.Chebyshev.T ℝ 0).eval x = 1 := by
    rw [Polynomial.Chebyshev.T_zero]; simp
  have h1 : (Polynomial.Chebyshev.T ℝ 1).eval x = x := by
    rw [Polynomial.Chebyshev.T_one]; simp
  have h2 : (Polynomial.Chebyshev.T ℝ 2).eval x = 2 * x ^ 2 - 1 := by
    rw [Polynomial.Chebyshev.T_two]; simp
  have h3 : (Polynomial.Chebyshev.T ℝ 3).eval x = 4 * x ^ 3 - 3 * x := by
    rw [chebyshevT_three, Polynomial.Chebyshev.T_two, Polynomial.Chebyshev.T_one]
    simp
    ring
  have h4 : (Polynomial.Chebyshev.T ℝ 4).eval x = 8 * x ^ 4 - 8 * x ^ 2 + 1 := by
    rw [chebyshevT_four, chebyshevT_three, Polynomial.Chebyshev.T_two,
      Polynomial.Chebyshev.T_one]
    simp
    ring
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, KsumFiveC]
  push_cast
  rw [h0, h1, h2, h3, h4]
  ring

theorem KsumFiveNonneg {q : ℕ} [NeZero q] {f : ℝ → ℝ} (hf : ∀ t : ℝ, 0 ≤ f t)
    {x₀ L β γ : ℝ} (hx₀ : 0 < x₀) (hL : 0 < L)
    (hsupp : ∀ t : ℝ, x₀ ≤ t → f t = 0) (χ₁ : DirichletCharacter ℂ q) (hχ₁ : χ₁ ^ 2 = 1) :
    0 ≤ 14379 * Work.ZeroFreeTables.XY.Kxy f L β 0 (1 : DirichletCharacter ℂ q)
      + 24480 * Work.ZeroFreeTables.XY.Kxy f L β γ χ₁
      + 14900 * Work.ZeroFreeTables.XY.Kxy f L β (2 * γ) (1 : DirichletCharacter ℂ q)
      + 6000 * Work.ZeroFreeTables.XY.Kxy f L β (3 * γ) χ₁
      + 1250 * Work.ZeroFreeTables.XY.Kxy f L β (4 * γ) (1 : DirichletCharacter ℂ q) := by
  have hpow2 : χ₁ ^ 2 = 1 := hχ₁
  have hpow3 : χ₁ ^ 3 = χ₁ := by
    rw [show (3 : ℕ) = 2 + 1 from rfl, pow_succ, hχ₁, one_mul]
  have hpow4 : χ₁ ^ 4 = 1 := by
    rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, hχ₁, one_mul]
  -- the Chebyshev polynomial is non-negative on `[-1,1]`
  have hcheb : ∀ x ∈ Set.Icc (-1 : ℝ) 1,
      0 ≤ ∑ k ∈ Finset.range (4 + 1),
        KsumFiveC k * (Polynomial.Chebyshev.T ℝ (k : ℤ)).eval x := by
    intro x _
    rw [KsumFiveChebyshev_eq x]
    positivity
  have hmain := Work.ZeroFreeTables.ksum_trigPoly_nonneg (q := q) (f := f) (x₀ := x₀)
    (L := L) (β := β) (γ := γ) (c := KsumFiveC) (d := 4) hf hL hx₀.le hsupp hcheb χ₁
  -- identify the conclusion with the five displayed `Kxy`-terms
  have hsum_eq :
      (∑ k ∈ Finset.range (4 + 1), KsumFiveC k
        * Work.ZeroFreeTables.Ksum q f L ((β : ℂ) + ((k : ℝ) * γ : ℂ) * Complex.I) (χ₁ ^ k))
      = 14379 * Kxy f L β 0 (1 : DirichletCharacter ℂ q)
        + 24480 * Kxy f L β γ χ₁
        + 14900 * Kxy f L β (2 * γ) (1 : DirichletCharacter ℂ q)
        + 6000 * Kxy f L β (3 * γ) χ₁
        + 1250 * Kxy f L β (4 * γ) (1 : DirichletCharacter ℂ q) := by
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, KsumFiveC, hpow2, hpow3, hpow4,
      ← Complex.ofReal_mul, Ksum_eq_Kxy, Nat.cast_ofNat, Nat.cast_zero, Nat.cast_one, zero_mul,
      one_mul, pow_zero, pow_one, zero_add]
  rw [hsum_eq] at hmain
  exact hmain

end Work.ZeroFreeTables.XY
