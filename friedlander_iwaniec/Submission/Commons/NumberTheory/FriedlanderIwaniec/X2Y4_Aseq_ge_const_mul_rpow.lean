import Mathlib
import Submission.Commons.NumberTheory.FriedlanderIwaniec.X2Y4_sieve_remainder_le
import Submission.Commons.Analysis.Integral.integral_sqrt_one_sub_pow_four_ge

namespace Commons.NumberTheory.FriedlanderIwaniec

/-- `A(x) = #{a ∈ ℤ² : a₁² + a₂⁴ ≤ x} ≫ x^{3/4}` for large `x` (the main term being
`4κx^{3/4}` with `κ = ∫₀¹√(1-u⁴) ≥ 0.872`). -/
theorem X2Y4_Aseq_ge_const_mul_rpow :
    ∃ c : ℝ, 0 < c ∧ ∃ X : ℕ, ∀ x : ℕ, X ≤ x →
      c * (x : ℝ) ^ ((3 : ℝ) / 4) ≤ (Submission.Aseq x : ℝ) := by
  -- (3.18): `A(x) = 4κ x^{3/4} + O(√x)`
  obtain ⟨C, hC, h⟩ := Submission.Aseq_asymptotic
  -- the numerical lower bound `κ ≥ 0.87215`
  set K : ℝ := (87215 : ℝ) / 100000 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; norm_num
  have hκ : K ≤ ∫ u in (0)..1, Real.sqrt (1 - u ^ 4) :=
    Commons.Analysis.Integral.integral_sqrt_one_sub_pow_four_ge
  -- the threshold `T` with `C ≤ 2K T`, so that `C√x ≤ 2K x^{3/4}` for `x ≥ T⁴`
  set T : ℝ := C / (2 * K) with hTdef
  have hTpos : 0 < T := by rw [hTdef]; positivity
  refine ⟨2 * K, by positivity, ⌈T ^ 4⌉₊ + 1, fun x hx => ?_⟩
  have hxT : T ^ 4 ≤ (x : ℝ) := by
    have h2 : T ^ 4 ≤ ((⌈T ^ 4⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
    have h3 : ((⌈T ^ 4⌉₊ : ℕ) : ℝ) ≤ (x : ℝ) := by
      exact_mod_cast (by omega : ⌈T ^ 4⌉₊ ≤ x)
    linarith only [h2, h3]
  have hx1 : (1 : ℝ) ≤ (x : ℝ) := by
    have hx1' : 1 ≤ x := by omega
    exact_mod_cast hx1'
  have hxpos : (0 : ℝ) < (x : ℝ) := lt_of_lt_of_le zero_lt_one hx1
  have hx0 : (0 : ℝ) ≤ (x : ℝ) := le_of_lt hxpos
  -- `T ≤ x^{1/4}`
  have hrpow : T ≤ (x : ℝ) ^ ((1 : ℝ) / 4) := by
    have h1 : (T ^ 4) ^ ((1 : ℝ) / 4) ≤ (x : ℝ) ^ ((1 : ℝ) / 4) :=
      Real.rpow_le_rpow (by positivity) hxT (by norm_num)
    rwa [← Real.rpow_natCast T 4, ← Real.rpow_mul (le_of_lt hTpos),
      show (((4 : ℕ) : ℝ) * (1 / 4)) = 1 by norm_num, Real.rpow_one] at h1
  -- hence `C ≤ 2K x^{1/4}`
  have hCsq : C ≤ 2 * K * (x : ℝ) ^ ((1 : ℝ) / 4) := by
    have h2 : 2 * K * T ≤ 2 * K * (x : ℝ) ^ ((1 : ℝ) / 4) :=
      mul_le_mul_of_nonneg_left hrpow (by positivity)
    have h3 : 2 * K * T = C := by rw [hTdef]; field_simp
    rw [h3] at h2
    exact h2
  -- rewrite `x^{3/4}` as `x^{1/4} x^{1/2}`
  have hsplit : (x : ℝ) ^ ((3 : ℝ) / 4)
      = (x : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((1 : ℝ) / 2) := by
    rw [← Real.rpow_add hxpos]
    norm_num
  -- the error term is absorbed: `C√x ≤ 2K x^{3/4}`
  have hCsqrt : C * (x : ℝ) ^ ((1 : ℝ) / 2) ≤ 2 * K * (x : ℝ) ^ ((3 : ℝ) / 4) := by
    calc C * (x : ℝ) ^ ((1 : ℝ) / 2)
        ≤ (2 * K * (x : ℝ) ^ ((1 : ℝ) / 4)) * (x : ℝ) ^ ((1 : ℝ) / 2) :=
          mul_le_mul_of_nonneg_right hCsq (Real.rpow_nonneg hx0 _)
      _ = 2 * K * ((x : ℝ) ^ ((1 : ℝ) / 4) * (x : ℝ) ^ ((1 : ℝ) / 2)) := by ring
      _ = 2 * K * (x : ℝ) ^ ((3 : ℝ) / 4) := by rw [← hsplit]
  -- the asymptotic lower bound, with `√x = x^{1/2}`
  have h1 : 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ ((3 : ℝ) / 4)
      - C * (x : ℝ) ^ ((1 : ℝ) / 2) ≤ (Submission.Aseq x : ℝ) := by
    have hab := (abs_le.mp (h x (by omega))).1
    rw [Real.sqrt_eq_rpow] at hab
    linarith only [hab]
  -- `2K x^{3/4} ≤ (4κ − 2K) x^{3/4}`
  have h3 : 2 * K * (x : ℝ) ^ ((3 : ℝ) / 4)
      ≤ (4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) - 2 * K) * (x : ℝ) ^ ((3 : ℝ) / 4) := by
    have hK' : 2 * K ≤ 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) - 2 * K := by
      linarith only [hκ]
    exact mul_le_mul_of_nonneg_right hK' (Real.rpow_nonneg hx0 _)
  calc 2 * K * (x : ℝ) ^ ((3 : ℝ) / 4)
      ≤ (4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) - 2 * K) * (x : ℝ) ^ ((3 : ℝ) / 4) := h3
    _ = 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ ((3 : ℝ) / 4)
        - 2 * K * (x : ℝ) ^ ((3 : ℝ) / 4) := by ring
    _ ≤ 4 * (∫ u in (0)..1, Real.sqrt (1 - u ^ 4)) * (x : ℝ) ^ ((3 : ℝ) / 4)
        - C * (x : ℝ) ^ ((1 : ℝ) / 2) := sub_le_sub_left hCsqrt _
    _ ≤ (Submission.Aseq x : ℝ) := h1

end Commons.NumberTheory.FriedlanderIwaniec
