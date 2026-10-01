import Mathlib

open scoped Nat Real

namespace Work.ZeroDensity.Ingham

/-- The classical Fourier series of the second Bernoulli polynomial: for every real `u`,

`∑_{n ≥ 1} cos (2 π n u) / n² = π² * B₂({u})`, where `{u} = Int.fract u` is the fractional
part of `u` and `B₂(x) = x² - x + 1/6`.

This is the case `k = 1` of `hasSum_one_div_nat_pow_mul_cos` (the Fourier expansion of the
`2`-nd Bernoulli polynomial, valid on `[0,1]`), together with the periodicity of `cos`: the
terms only see `u` modulo `1`. -/
theorem hasSum_cos_fract (u : ℝ) :
    HasSum (fun n : ℕ => (1 / (n : ℝ) ^ 2) * Real.cos (2 * Real.pi * n * u))
      (Real.pi ^ 2 * ((Int.fract u) ^ 2 - Int.fract u + 1 / 6)) := by
  -- The fractional part lies in `[0, 1]`, where the Fourier expansion is stated.
  have hx : Int.fract u ∈ Set.Icc (0 : ℝ) 1 :=
    ⟨Int.fract_nonneg u, le_of_lt (Int.fract_lt_one u)⟩
  -- Fourier series of `B₂` (case `k = 1` of the Mathlib theorem, so `2 * k = 2`).
  have hs := hasSum_one_div_nat_pow_mul_cos (k := 1) (by norm_num) hx
  -- `cos (2 π n u) = cos (2 π n {u})`, since `u - {u} = ⌊u⌋` is an integer.
  have hterm : ∀ n : ℕ, (1 / (n : ℝ) ^ (2 * 1)) * Real.cos (2 * Real.pi * n * Int.fract u)
      = (1 / (n : ℝ) ^ 2) * Real.cos (2 * Real.pi * n * u) := by
    intro n
    have hcos : Real.cos (2 * Real.pi * n * Int.fract u) = Real.cos (2 * Real.pi * n * u) := by
      have hmul : (2 * Real.pi * n * u)
          = (2 * Real.pi * n * Int.fract u) + ((n * ⌊u⌋ : ℤ) : ℝ) * (2 * Real.pi) := by
        conv_lhs => rw [← Int.fract_add_floor u]
        push_cast
        ring
      rw [hmul, Real.cos_add_int_mul_two_pi]
    rw [hcos]
  -- The value produced by the Fourier expansion is `π² * B₂({u}) = π² * ({u}² - {u} + 1/6)`.
  have hval : (-1 : ℝ) ^ (1 + 1) * (2 * Real.pi) ^ (2 * 1) / 2 / (2 * 1)! *
        Polynomial.eval (Int.fract u) (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1)))
      = Real.pi ^ 2 * ((Int.fract u) ^ 2 - Int.fract u + 1 / 6) := by
    have hB : Polynomial.eval (Int.fract u) (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli 2))
        = (Int.fract u) ^ 2 - Int.fract u + 1 / 6 := by
      rw [Polynomial.bernoulli_def]
      simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
      norm_num [Polynomial.eval_monomial]
      ring
    norm_num only [Nat.reduceMul, Nat.reduceAdd, Nat.factorial]
    rw [hB]
    ring
  have h' : HasSum (fun n : ℕ => (1 / (n : ℝ) ^ 2) * Real.cos (2 * Real.pi * n * u))
      ((-1 : ℝ) ^ (1 + 1) * (2 * Real.pi) ^ (2 * 1) / 2 / (2 * 1)! *
        Polynomial.eval (Int.fract u)
          (Polynomial.map (algebraMap ℚ ℝ) (Polynomial.bernoulli (2 * 1)))) :=
    hs.congr_fun (fun n => (hterm n).symm)
  rwa [hval] at h'

end Work.ZeroDensity.Ingham
