/-
# `Work.FIChain.GammaTruncMulCoprime`

The truncation identity for the Möbius coefficient `γ(n; C) = ∑_{d ∣ n, d ≤ C} μ(d)` of the
companion paper's hypothesis (B) (see `Work.FIPlan.gammaTrunc`, `ASP.rhoTrunc`):

  for `(n₁, n₀) = 1` and any real `σ`,
    `∑_{d₁ ∣ n₁} μ(d₁) · γ(σ / d₁; n₀) = γ(σ; n₁ n₀)`.

The content is the multiplicativity of the truncated Möbius coefficient: because `n₁` and `n₀` are
coprime, the divisors of `n₁ n₀` are exactly the products `d₁ d₀` with `d₁ ∣ n₁`, `d₀ ∣ n₀`
(`Nat.Coprime.mul_injOn_divisors` / `Nat.divisors_mul`), the truncation condition `d₁ d₀ ≤ σ`
becomes `d₀ ≤ σ / d₁` (`le_div_iff₀`, using `d₁ ≥ 1`), and `μ(d₁ d₀) = μ(d₁) μ(d₀)` on coprime
arguments (`ArithmeticFunction.isMultiplicative_moebius`).

This is the algebraic step behind the passage from the `ρ`-weighted sums of `ASP.S7c`/`S8b` to
the untruncated Möbius sums, i.e. the `(B)`-shape input of the Friedlander–Iwaniec proof.
-/
import Mathlib
import Submission.Work.FIPlan.Interface

set_option autoImplicit false

namespace Work.FIChain

open Finset

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## Auxiliary lemmas -/

/-- For coprime `m`, `n` the divisors of `m * n` are exactly the products `p.1 * p.2` with
`p ∈ m.divisors ×ˢ n.divisors`, and the map is injective on that product. -/
private lemma sum_divisors_mul_coprime (m n : ℕ) (h : m.Coprime n) (F : ℕ → ℝ) :
    ∑ d ∈ (m * n).divisors, F d = ∑ p ∈ m.divisors ×ˢ n.divisors, F (p.1 * p.2) := by
  rw [Nat.divisors_mul, Finset.mul_def, Finset.sum_image]
  intro x hx y hy hxy
  exact h.mul_injOn_divisors hx hy hxy

/-- The pointwise comparison of a term of the left-hand double sum with a term of the right-hand
sum: on coprime divisors `d₁ ∣ n₁`, `d₀ ∣ n₀` the condition `d₀ ≤ σ / d₁` is the condition
`d₁ d₀ ≤ σ`, and `μ(d₁ d₀) = μ(d₁) μ(d₀)`. -/
private lemma term_eq (n₁ n₀ : ℕ) (hcop : n₁.Coprime n₀) (σ : ℝ)
    {d₁ d₀ : ℕ} (h₁ : d₁ ∈ n₁.divisors) (h₀ : d₀ ∈ n₀.divisors) :
    (ArithmeticFunction.moebius d₁ : ℝ) *
        (if (d₀ : ℝ) ≤ σ / (d₁ : ℝ) then (ArithmeticFunction.moebius d₀ : ℝ) else 0)
      = (if ((d₁ * d₀ : ℕ) : ℝ) ≤ σ then
          (ArithmeticFunction.moebius (d₁ * d₀) : ℝ) else 0) := by
  have hd₁ : 0 < d₁ := Nat.pos_of_mem_divisors h₁
  have hpos : (0 : ℝ) < (d₁ : ℝ) := by exact_mod_cast hd₁
  have hc : d₁.Coprime d₀ :=
    (hcop.coprime_dvd_left (Nat.mem_divisors.mp h₁).1).coprime_dvd_right
      (Nat.mem_divisors.mp h₀).1
  have hmu : (ArithmeticFunction.moebius (d₁ * d₀) : ℝ)
      = (ArithmeticFunction.moebius d₁ : ℝ) * (ArithmeticFunction.moebius d₀ : ℝ) := by
    rw [ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hc, Int.cast_mul]
  by_cases hle : (d₀ : ℝ) ≤ σ / (d₁ : ℝ)
  · have h2 : ((d₁ * d₀ : ℕ) : ℝ) ≤ σ := by
      have h' := (le_div_iff₀ hpos).mp hle
      rw [Nat.cast_mul]
      linarith
    rw [if_pos hle, if_pos h2, hmu]
  · have h2 : ¬ ((d₁ * d₀ : ℕ) : ℝ) ≤ σ := by
      intro hc2
      apply hle
      rw [le_div_iff₀ hpos]
      rw [Nat.cast_mul] at hc2
      linarith
    rw [if_neg hle, if_neg h2, mul_zero]

/-! ## The identity -/

theorem GammaTruncMulCoprime (n₁ n₀ : ℕ) (hcop : n₁.Coprime n₀) (σ : ℝ) :
    ∑ d₁ ∈ n₁.divisors, (ArithmeticFunction.moebius d₁ : ℝ) *
        Work.FIPlan.gammaTrunc (σ / (d₁ : ℝ)) n₀
      = Work.FIPlan.gammaTrunc σ (n₁ * n₀) := by
  -- The `γ` on the left, pushed inside and reindexed by the divisor pairs of `n₀`:
  have hL1 : (∑ d₁ ∈ n₁.divisors, (ArithmeticFunction.moebius d₁ : ℝ) *
        Work.FIPlan.gammaTrunc (σ / (d₁ : ℝ)) n₀)
      = ∑ d₁ ∈ n₁.divisors, ∑ d₀ ∈ n₀.divisors,
          (ArithmeticFunction.moebius d₁ : ℝ) *
            (if (d₀ : ℝ) ≤ σ / (d₁ : ℝ) then (ArithmeticFunction.moebius d₀ : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro d₁ _
    rw [Work.FIPlan.gammaTrunc, Finset.sum_filter, Finset.mul_sum]
  -- ... as a single sum over the product `n₁.divisors ×ˢ n₀.divisors`:
  have hL2 : (∑ d₁ ∈ n₁.divisors, ∑ d₀ ∈ n₀.divisors,
          (ArithmeticFunction.moebius d₁ : ℝ) *
            (if (d₀ : ℝ) ≤ σ / (d₁ : ℝ) then (ArithmeticFunction.moebius d₀ : ℝ) else 0))
      = ∑ p ∈ n₁.divisors ×ˢ n₀.divisors,
          (ArithmeticFunction.moebius p.1 : ℝ) *
            (if (p.2 : ℝ) ≤ σ / (p.1 : ℝ) then (ArithmeticFunction.moebius p.2 : ℝ) else 0) :=
    (Finset.sum_product' n₁.divisors n₀.divisors
      (fun a b => (ArithmeticFunction.moebius a : ℝ) *
        (if (b : ℝ) ≤ σ / (a : ℝ) then (ArithmeticFunction.moebius b : ℝ) else 0))).symm
  -- ... with the truncation moved from `d₀` to the product and `μ` made multiplicative:
  have hL3 : (∑ p ∈ n₁.divisors ×ˢ n₀.divisors,
          (ArithmeticFunction.moebius p.1 : ℝ) *
            (if (p.2 : ℝ) ≤ σ / (p.1 : ℝ) then (ArithmeticFunction.moebius p.2 : ℝ) else 0))
      = ∑ p ∈ n₁.divisors ×ˢ n₀.divisors,
          (if ((p.1 * p.2 : ℕ) : ℝ) ≤ σ then
            (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) else 0) := by
    apply Finset.sum_congr rfl
    intro p hp
    exact term_eq n₁ n₀ hcop σ (Finset.mem_product.mp hp).1 (Finset.mem_product.mp hp).2
  -- The right-hand `γ` is the same sum over the divisor pairs of the coprime product.
  have hR1 : Work.FIPlan.gammaTrunc σ (n₁ * n₀)
      = ∑ p ∈ n₁.divisors ×ˢ n₀.divisors,
          (if ((p.1 * p.2 : ℕ) : ℝ) ≤ σ then
            (ArithmeticFunction.moebius (p.1 * p.2) : ℝ) else 0) := by
    rw [Work.FIPlan.gammaTrunc, Finset.sum_filter, sum_divisors_mul_coprime n₁ n₀ hcop]
  exact hL1.trans (hL2.trans (hL3.trans hR1.symm))

end

end Work.FIChain
