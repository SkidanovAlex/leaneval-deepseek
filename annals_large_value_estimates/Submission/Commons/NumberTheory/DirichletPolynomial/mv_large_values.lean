import Mathlib
import Submission.Commons.NumberTheory.DirichletPolynomial.large_sieve_block_sampled

namespace Commons.NumberTheory.DirichletPolynomial

open Finset Complex
open scoped ComplexConjugate BigOperators
set_option autoImplicit false

/-- Classical mean-value / large-sieve bound for the number of 1-separated large values
of a Dirichlet polynomial of length `N` with 1-bounded coefficients:
`R ≤ C·(N²V⁻² + T·N·V⁻²)` with an absolute constant `C`.

Proof: apply the block sampled large sieve
`Commons.NumberTheory.DirichletPolynomial.large_sieve_block_sampled`
(`Σ_r ‖D(t_r)‖² ≤ C(T+N)·Σ_{n∈[N,2N]}‖b_n‖²`) to the coefficients
`a n = if n ∈ Icc N (2N) then b n else 0`; use `‖b n‖ ≤ 1` and
`#(Icc N (2N)) = N+1 ≤ 2N` to get `Σ‖a_n‖² ≤ 2N`; and bound the left side below by
`R·V²` using `‖D(t_r)‖ ≥ V`.  Finally rewrite `V ^ (-2 : ℤ) = (V^2)⁻¹`. -/
theorem mv_large_values :
    ∃ C : ℝ, 0 < C ∧
      ∀ (b : ℕ → ℂ), (∀ n, ‖b n‖ ≤ 1) →
      ∀ (N : ℕ) (V T : ℝ) (R : ℕ) (t : Fin R → ℝ),
        1 ≤ N → 0 < V → 0 ≤ T →
        (∀ i j, i ≠ j → 1 ≤ |t i - t j|) → (∀ i, t i ∈ Set.Icc 0 T) →
        (∀ r, ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ (I * (t r : ℂ))‖ ≥ V) →
        (R : ℝ) ≤ C * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * ((N : ℝ) * V ^ (-2 : ℤ))) := by
  obtain ⟨C, hCpos, hmain⟩ :=
    Commons.NumberTheory.DirichletPolynomial.large_sieve_block_sampled
  refine ⟨2 * C, by positivity, ?_⟩
  intro b hb N V T R t hN hV hT hsep hIcc hlarge
  -- The coefficients restricted to the block `[N, 2N]`.
  set a : ℕ → ℂ := fun n => if n ∈ Finset.Icc N (2 * N) then b n else 0 with ha
  have hsupp : ∀ n, n ∉ Finset.Icc N (2 * N) → a n = 0 := by
    intro n hn
    change (if n ∈ Finset.Icc N (2 * N) then b n else 0) = 0
    exact if_neg hn
  have hls := hmain N hN T hT a R t hIcc hsep hsupp
  -- The two inner sums agree on the block.
  have hD : ∀ r : Fin R,
      (∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (I * (t r : ℂ))) =
      (∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ (I * (t r : ℂ))) := by
    intro r
    apply Finset.sum_congr rfl
    intro n hn
    simp only [ha, hn, if_true]
  have hDsum :
      (∑ r : Fin R, ‖∑ n ∈ Finset.Icc N (2 * N), a n * (n : ℂ) ^ (I * (t r : ℂ))‖ ^ 2) =
      (∑ r : Fin R, ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ (I * (t r : ℂ))‖ ^ 2) := by
    apply Finset.sum_congr rfl
    intro r _
    rw [hD r]
  rw [hDsum] at hls
  -- Bound the coefficient energy by `2N`.
  have ha_le : ∀ n, ‖a n‖ ^ 2 ≤ 1 := by
    intro n
    by_cases hn : n ∈ Finset.Icc N (2 * N)
    · simp only [ha, hn, if_true]
      have hbn := hb n
      nlinarith [norm_nonneg (b n), hbn]
    · simp only [ha, hn, if_false, norm_zero]
      norm_num
  have hsum_le : ∑ n ∈ Finset.Icc N (2 * N), ‖a n‖ ^ 2 ≤ 2 * (N : ℝ) := by
    have h1 : ∑ n ∈ Finset.Icc N (2 * N), ‖a n‖ ^ 2 ≤
        (Finset.Icc N (2 * N)).card • (1 : ℝ) :=
      Finset.sum_le_card_nsmul _ _ _ (fun n _ => ha_le n)
    rw [nsmul_eq_mul, mul_one] at h1
    have hcard : ((Finset.Icc N (2 * N)).card : ℝ) ≤ 2 * (N : ℝ) := by
      rw [Nat.card_Icc]
      have hN1 : (1 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
      have hcast : ((2 * N + 1 - N : ℕ) : ℝ) = 2 * (N : ℝ) + 1 - (N : ℝ) := by
        push_cast [Nat.cast_sub (by omega : N ≤ 2 * N + 1)]
        ring
      rw [hcast]
      linarith
    linarith [h1, hcard]
  -- Coefficient of the `T + N` factor is nonnegative.
  have hTN : 0 ≤ C * (T + (N : ℝ)) := by
    apply mul_nonneg hCpos.le
    have : (0 : ℝ) ≤ (N : ℝ) := by positivity
    linarith
  have hup : ∑ r : Fin R, ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ (I * (t r : ℂ))‖ ^ 2
      ≤ C * (T + (N : ℝ)) * (2 * (N : ℝ)) := by
    refine le_trans hls ?_
    exact mul_le_mul_of_nonneg_left hsum_le hTN
  -- Lower bound from the large-value hypothesis.
  have hlow : (R : ℝ) * V ^ 2 ≤
      ∑ r : Fin R, ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ (I * (t r : ℂ))‖ ^ 2 := by
    have h1 : ∀ r : Fin R, V ^ 2 ≤
        ‖∑ n ∈ Finset.Icc N (2 * N), b n * (n : ℂ) ^ (I * (t r : ℂ))‖ ^ 2 :=
      fun r => pow_le_pow_left₀ hV.le (hlarge r) 2
    have h2 := Finset.sum_le_sum (fun r (_ : r ∈ (Finset.univ : Finset (Fin R))) => h1 r)
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h2
    exact h2
  -- Combine.
  have hcomb : (R : ℝ) * V ^ 2 ≤ C * (T + (N : ℝ)) * (2 * (N : ℝ)) :=
    le_trans hlow hup
  have hA : (R : ℝ) * V ^ 2 ≤ 2 * C * ((N : ℝ) ^ 2 + (N : ℝ) * T) := by
    have heq : C * (T + (N : ℝ)) * (2 * (N : ℝ)) = 2 * C * ((N : ℝ) ^ 2 + (N : ℝ) * T) := by
      ring
    linarith [hcomb, heq.symm.le, heq.le]
  -- Convert `R * V^2 ≤ A` into the stated bound.
  have hV2pos : 0 < V ^ 2 := by positivity
  have hV2ne : V ^ 2 ≠ 0 := ne_of_gt hV2pos
  have hz : V ^ (-2 : ℤ) = (V ^ 2)⁻¹ := by
    rw [zpow_neg]
    norm_num
  have hfin : (R : ℝ) ≤ 2 * C * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ) +
      T * ((N : ℝ) * V ^ (-2 : ℤ))) := by
    have h1 : (R : ℝ) * V ^ 2 * (V ^ 2)⁻¹ ≤
        (2 * C * ((N : ℝ) ^ 2 + (N : ℝ) * T)) * (V ^ 2)⁻¹ :=
      mul_le_mul_of_nonneg_right hA (by positivity)
    have hsimp : (R : ℝ) * V ^ 2 * (V ^ 2)⁻¹ = (R : ℝ) := by
      rw [mul_assoc, mul_inv_cancel₀ hV2ne, mul_one]
    rw [hsimp] at h1
    have heq : (2 * C * ((N : ℝ) ^ 2 + (N : ℝ) * T)) * (V ^ 2)⁻¹ =
        2 * C * ((N : ℝ) ^ 2 * V ^ (-2 : ℤ) + T * ((N : ℝ) * V ^ (-2 : ℤ))) := by
      rw [hz]; ring
    linarith [h1, heq.le, heq.symm.le]
  exact hfin

end Commons.NumberTheory.DirichletPolynomial
