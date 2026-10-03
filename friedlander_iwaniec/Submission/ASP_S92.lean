import Submission.ASP_R
import Submission.Commons.NumberTheory.FriedlanderIwaniec.sum_sq_an_le

/-!
# Hypothesis `(9.2)` of the companion "Asymptotic sieve for primes" for `X² + Y⁴`

The companion paper's Theorem 2 (its §9) frees the sequence `A = (a_n)` from the
squarefree-support hypothesis `(1.16)`, at the price of the extra hypotheses
`(9.1)` (on `g(p²)`) and

  `(9.2)   ∑_{n ≤ x} a_n² ≤ x^{-2/3} A(x)²`.

This file verifies `(9.2)` for the Friedlander–Iwaniec sequence
`a_n = #{(a,c) ∈ ℤ² : a² + c⁴ = n}`.

The input is the commons theorem `sum_sq_an_le`: for every `ε > 0`,
`∑_{n ≤ x} a_n² ≤ C x^{3/4 + ε}`; together with `A(x) ≫ x^{3/4}`
(`Submission.exists_const_mul_rpow_le_Aseq`) this gives
`x^{-2/3} A(x)² ≫ x^{-2/3 + 3/2} = x^{5/6} ≥ x^{3/4+ε}` for `ε < 1/12`.
-/

namespace Submission

open Finset

/-- **(9.2)** of the companion paper for the Friedlander–Iwaniec sequence. -/
theorem X2Y4_S92 :
    ∃ X₀ : ℕ, ∀ x : ℕ, X₀ ≤ x →
      (∑ n ∈ Finset.range (x + 1), (an n : ℝ) ^ 2)
        ≤ (x : ℝ) ^ (-(2 : ℝ) / 3) * (Aseq x : ℝ) ^ 2 := by
  obtain ⟨cA, hcA, XA, hAlow⟩ := exists_const_mul_rpow_le_Aseq
  obtain ⟨C, hC, hCb⟩ := Commons.NumberTheory.FriedlanderIwaniec.sum_sq_an_le (1 / 24) (by norm_num)
  refine ⟨max XA (⌈(C / cA ^ 2) ^ (24 : ℕ)⌉₊ + 1) + 1, fun x hx => ?_⟩
  have hxXA : XA ≤ x := by omega
  have hx1 : 1 ≤ x := by omega
  have hxC : ⌈(C / cA ^ 2) ^ (24 : ℕ)⌉₊ ≤ x := by omega
  have hxpos : (0 : ℝ) < (x : ℝ) := by
    exact_mod_cast (by omega : 0 < x)
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hxpos
  -- **Step 1** : the square-sum bound `∑ a_n² ≤ C x^{19/24}`
  have h1 : (∑ n ∈ Finset.range (x + 1), (an n : ℝ) ^ 2)
      ≤ C * (x : ℝ) ^ ((19 : ℝ) / 24) := by
    have h := hCb x hx1
    have h2 : (x : ℝ) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ (1 / 24 : ℝ) = (x : ℝ) ^ ((19 : ℝ) / 24) := by
      rw [← Real.rpow_add hxpos]; norm_num
    calc (∑ n ∈ Finset.range (x + 1), (an n : ℝ) ^ 2)
        ≤ C * (x : ℝ) ^ ((3 : ℝ) / 4) * (x : ℝ) ^ (1 / 24 : ℝ) := h
      _ = C * (x : ℝ) ^ ((19 : ℝ) / 24) := by rw [mul_assoc, h2]
  -- **Step 2** : the lower bound `cA² x^{3/2} ≤ A(x)²`
  have hA := hAlow x hxXA
  have hA0 : (0 : ℝ) ≤ cA * (x : ℝ) ^ ((3 : ℝ) / 4) := by positivity
  have h3 : cA ^ 2 * (x : ℝ) ^ ((3 : ℝ) / 2) ≤ (Aseq x : ℝ) ^ 2 := by
    have h4 : (cA * (x : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 ≤ (Aseq x : ℝ) ^ 2 :=
      pow_le_pow_left₀ hA0 hA 2
    have h5 : (cA * (x : ℝ) ^ ((3 : ℝ) / 4)) ^ 2 = cA ^ 2 * (x : ℝ) ^ ((3 : ℝ) / 2) := by
      rw [mul_pow, ← Real.rpow_natCast ((x : ℝ) ^ ((3 : ℝ) / 4)) 2, ← Real.rpow_mul hx0]
      norm_num
    rwa [h5] at h4
  -- **Step 3** : `C x^{19/24} ≤ x^{-2/3} (cA² x^{3/2})`
  have h6 : C * (x : ℝ) ^ ((19 : ℝ) / 24)
      ≤ (x : ℝ) ^ (-(2 : ℝ) / 3) * (cA ^ 2 * (x : ℝ) ^ ((3 : ℝ) / 2)) := by
    have h7 : (C / cA ^ 2) ^ (24 : ℕ) ≤ (x : ℝ) := by
      have h8 : ((⌈(C / cA ^ 2) ^ (24 : ℕ)⌉₊ : ℕ) : ℝ) ≤ (x : ℝ) := by exact_mod_cast hxC
      have h9 : (C / cA ^ 2) ^ (24 : ℕ) ≤ ((⌈(C / cA ^ 2) ^ (24 : ℕ)⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
      linarith
    have h10 : C / cA ^ 2 ≤ (x : ℝ) ^ ((1 : ℝ) / 24) := by
      have h11 : ((C / cA ^ 2) ^ (24 : ℕ)) ^ ((1 : ℝ) / 24) ≤ ((x : ℝ)) ^ ((1 : ℝ) / 24) :=
        Real.rpow_le_rpow (by positivity) h7 (by norm_num)
      have h12 : ((C / cA ^ 2) ^ (24 : ℕ)) ^ ((1 : ℝ) / 24) = C / cA ^ 2 := by
        rw [← Real.rpow_natCast (C / cA ^ 2) 24, ← Real.rpow_mul (by positivity : (0:ℝ) ≤ C / cA ^ 2)]
        norm_num
      rwa [h12] at h11
    have h15 : (x : ℝ) ^ (-(2 : ℝ) / 3) * (cA ^ 2 * (x : ℝ) ^ ((3 : ℝ) / 2))
        = cA ^ 2 * (x : ℝ) ^ ((5 : ℝ) / 6) := by
      have h16 : (x : ℝ) ^ (-(2 : ℝ) / 3) * (x : ℝ) ^ ((3 : ℝ) / 2) = (x : ℝ) ^ ((5 : ℝ) / 6) := by
        rw [← Real.rpow_add hxpos]; norm_num
      calc (x : ℝ) ^ (-(2 : ℝ) / 3) * (cA ^ 2 * (x : ℝ) ^ ((3 : ℝ) / 2))
          = cA ^ 2 * ((x : ℝ) ^ (-(2 : ℝ) / 3) * (x : ℝ) ^ ((3 : ℝ) / 2)) := by ring
        _ = cA ^ 2 * (x : ℝ) ^ ((5 : ℝ) / 6) := by rw [h16]
    rw [h15]
    have h17 : C * (x : ℝ) ^ ((19 : ℝ) / 24)
        = (C / cA ^ 2 * (x : ℝ) ^ (-(1 : ℝ) / 24)) * (cA ^ 2 * (x : ℝ) ^ ((5 : ℝ) / 6)) := by
      rw [show (x : ℝ) ^ ((19 : ℝ) / 24) = (x : ℝ) ^ (-(1 : ℝ) / 24) * (x : ℝ) ^ ((5 : ℝ) / 6) by
        rw [← Real.rpow_add hxpos]; norm_num]
      field_simp
    rw [h17]
    refine mul_le_of_le_one_left (by positivity) ?_
    calc C / cA ^ 2 * (x : ℝ) ^ (-(1 : ℝ) / 24)
        ≤ (x : ℝ) ^ ((1 : ℝ) / 24) * (x : ℝ) ^ (-(1 : ℝ) / 24) :=
          mul_le_mul_of_nonneg_right h10 (Real.rpow_nonneg hx0 _)
      _ = 1 := by rw [← Real.rpow_add hxpos]; norm_num
  calc (∑ n ∈ Finset.range (x + 1), (an n : ℝ) ^ 2)
      ≤ C * (x : ℝ) ^ ((19 : ℝ) / 24) := h1
    _ ≤ (x : ℝ) ^ (-(2 : ℝ) / 3) * (cA ^ 2 * (x : ℝ) ^ ((3 : ℝ) / 2)) := h6
    _ ≤ (x : ℝ) ^ (-(2 : ℝ) / 3) * (Aseq x : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_left h3 (Real.rpow_nonneg hx0 _)

end Submission
