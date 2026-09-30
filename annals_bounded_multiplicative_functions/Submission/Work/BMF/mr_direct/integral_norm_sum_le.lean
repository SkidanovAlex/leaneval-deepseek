import Mathlib
import Submission.Work.BMF.mr_direct_defs
import Submission.Work.BMF.mr_direct.mv_integral_finset
import Submission.Work.BMF.mr_direct.dirichlet_sum_eq_exp_sum
import Submission.Work.BMF.mr_direct.sum_norm_bCoeff_le
import Submission.Work.BMF.mr_direct.inv_three_mul_le_abs_log_sub
import Submission.Work.BMF.mr_direct.mv_C0_nonneg

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

open MeasureTheory intervalIntegral
open scoped BigOperators Interval

namespace Work.BMF.mr_direct

-- Finset-level mean value bound with multiplicities for a sum of exponential terms.
-- `hC₀` is the Montgomery–Vaughan large-sieve inequality `mv_integral_separated_frequencies`
-- (see `Submission/Commons/NumberTheory/DirichletPolynomial/mv_integral_separated_frequencies.lean`,
-- available as `Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies`),
-- whose `∃C, 0 < C ∧ ...` form is unpacked by the caller.
theorem integral_norm_sum_le (C₀ : ℝ)
    (hC₀ : ∀ (δ : ℝ), 0 < δ → ∀ (N : ℕ) (μ : Fin N → ℝ) (b : Fin N → ℂ),
      (∀ i j, i ≠ j → δ ≤ |μ i - μ j|) → ∀ (A B : ℝ), A ≤ B →
        (∫ t in A..B, ‖∑ n, b n * Complex.exp (Complex.I * ((μ n : ℂ) * (t : ℂ)))‖ ^ 2)
          ≤ (B - A + C₀ / δ) * ∑ n, ‖b n‖ ^ 2) :
    ∀ {ι : Type} (s : Finset ι) (γ : ι → ℂ) (nn : ι → ℕ) (N : Finset ℕ) (A B S : ℝ),
      0 < A → A ≤ B → 0 ≤ S →
      (∀ i ∈ s, nn i ∈ N) → (∀ i ∈ s, A ≤ (nn i : ℝ)) → (∀ i ∈ s, (nn i : ℝ) ≤ B) →
      (∫ t in (-S)..S, ‖∑ i ∈ s, γ i * (nn i : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
        ≤ (2 * S + 3 * C₀ * B) *
            ∑ n ∈ N, (((s.filter (fun i => nn i = n)).card : ℝ) *
              (∑ i ∈ s.filter (fun i => nn i = n), ‖γ i‖ ^ 2) / (n : ℝ) ^ 2) := by
  intro ι s γ nn N A B S hA hAB hS hmem hAle hBle
  classical
  have hBpos : 0 < B := lt_of_lt_of_le hA hAB
  have hC0 : 0 ≤ C₀ := mv_C0_nonneg C₀ hC₀
  -- The image of `s` under `nn` is a set of positive integers in `[A, B]`, hence `1/B`-separated
  -- in the logarithmic variable `n ↦ -log n`.
  have hsep : ∀ i ∈ s.image nn, ∀ j ∈ s.image nn, i ≠ j →
      (1/(3*B)) ≤ |(-(Real.log i)) - (-(Real.log j))| := by
    intro i hi j hj hij
    obtain ⟨i', hi', hii'⟩ := Finset.mem_image.mp hi
    obtain ⟨j', hj', hjj'⟩ := Finset.mem_image.mp hj
    have hi1 : 1 ≤ nn i' := by
      have hpos : (0:ℝ) < (nn i' : ℝ) := lt_of_lt_of_le hA (hAle i' hi')
      have h2 : 0 < nn i' := Nat.cast_pos.mp hpos
      omega
    have hj1 : 1 ≤ nn j' := by
      have hpos : (0:ℝ) < (nn j' : ℝ) := lt_of_lt_of_le hA (hAle j' hj')
      have h2 : 0 < nn j' := Nat.cast_pos.mp hpos
      omega
    have hne : nn i' ≠ nn j' := by
      intro h; exact hij (by rw [← hii', ← hjj', h])
    have key := inv_three_mul_le_abs_log_sub hi1 hj1 (hBle i' hi') (hBle j' hj') hBpos hne
    rw [hii', hjj'] at key
    rw [show (-(Real.log i)) - (-(Real.log j)) = -(Real.log i - Real.log j) by ring, abs_neg]
    exact key
  -- Apply the Finset-indexed large sieve to `T = s.image nn` with the separated frequencies
  -- `μ n = -log n`, `δ = 1/(3B)` and the collapsed coefficients `b n = Σ_{nn i = n} γ i / n`.
  have hls := mv_integral_finset C₀ hC₀ (s.image nn) (fun n => -(Real.log n))
      (fun n => ∑ i ∈ s.filter (fun i => nn i = n), γ i * (n:ℂ)⁻¹)
      (1/(3*B)) (-S) S (by positivity) (by linarith) hsep
  -- Rewrite the Dirichlet polynomial as the separated-frequency exponential sum.
  have hInt : (∫ t in (-S)..S, ‖∑ i ∈ s, γ i * (nn i : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
      = ∫ t in (-S)..S,
          ‖∑ i ∈ s.image nn, (∑ j ∈ s.filter (fun j => nn j = i), γ j * (i : ℂ)⁻¹)
            * Complex.exp (Complex.I * ((((-(Real.log i)) : ℝ) : ℂ) * (t : ℂ)))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only []
    rw [dirichlet_sum_eq_exp_sum s γ nn t]
  -- Assemble: large sieve bound, then collapse the multiplicities with Cauchy–Schwarz.
  calc (∫ t in (-S)..S, ‖∑ i ∈ s, γ i * (nn i : ℂ) ^ (-(1 + Complex.I * (t : ℂ)))‖ ^ 2)
      = ∫ t in (-S)..S,
          ‖∑ i ∈ s.image nn, (∑ j ∈ s.filter (fun j => nn j = i), γ j * (i : ℂ)⁻¹)
            * Complex.exp (Complex.I * ((((-(Real.log i)) : ℝ) : ℂ) * (t : ℂ)))‖ ^ 2 := hInt
    _ ≤ (S - (-S) + C₀ / (1/(3*B))) *
          ∑ n ∈ s.image nn, ‖∑ i ∈ s.filter (fun i => nn i = n), γ i * (n : ℂ)⁻¹‖ ^ 2 := hls
    _ = (2 * S + 3 * C₀ * B) *
          ∑ n ∈ s.image nn, ‖∑ i ∈ s.filter (fun i => nn i = n), γ i * (n : ℂ)⁻¹‖ ^ 2 := by
        rw [show S - (-S) + C₀ / (1/(3*B)) = 2 * S + 3 * C₀ * B by field_simp; ring]
    _ ≤ (2 * S + 3 * C₀ * B) *
          ∑ n ∈ N, (((s.filter (fun i => nn i = n)).card : ℝ) *
            (∑ i ∈ s.filter (fun i => nn i = n), ‖γ i‖ ^ 2) / (n : ℝ) ^ 2) := by
        apply mul_le_mul_of_nonneg_left (sum_norm_bCoeff_le s γ nn N hmem)
        nlinarith [hS, mul_nonneg hC0 hBpos.le]

end Work.BMF.mr_direct
