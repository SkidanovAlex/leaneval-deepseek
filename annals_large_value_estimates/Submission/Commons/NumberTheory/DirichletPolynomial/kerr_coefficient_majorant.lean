import Mathlib
import Submission.Commons.Analysis.Fourier.fejer_window_localization_majorant

namespace Commons.NumberTheory.DirichletPolynomial

open Finset

/-- Multiplying every coefficient of a Dirichlet sum by a constant `B` scales the squared
modulus of the sum by `B ^ 2`. -/
private lemma normSq_sum_const_mul (B : ℝ) (z : ℕ → ℂ) (S : Finset ℕ) :
    ‖∑ n ∈ S, (B : ℂ) * z n‖ ^ 2 = B ^ 2 * ‖∑ n ∈ S, z n‖ ^ 2 := by
  rw [← Finset.mul_sum, norm_mul, mul_pow]
  rw [show ‖(B : ℂ)‖ ^ 2 = B ^ 2 by
    rw [← Complex.normSq_eq_norm_sq, Complex.normSq_ofReal]; ring]

theorem kerr_coefficient_majorant :
    ∃ C : ℝ, 0 < C ∧ ∀ (N : ℕ), 1 ≤ N → ∀ (Δ : ℝ), 0 < Δ → ∀ (B : ℝ), 1 ≤ B →
    ∀ (c : ℕ → ℂ), (∀ n, ‖c n‖ ≤ B) → ∀ (R : ℕ) (t : Fin R → ℝ),
    (∀ i j, i ≠ j → 1 ≤ |t i - t j|) →
    (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          c n * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0))
    ≤ C * B ^ 2 * (∑ i : Fin R, ∑ j : Fin R,
      (if |t i - t j| ≤ Δ then
        ‖∑ n ∈ Finset.Icc N (2 * N),
          (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
       else 0)) := by
  obtain ⟨Cf, hCf, hfe⟩ := Commons.Analysis.Fourier.fejer_window_localization_majorant
  refine ⟨4 * Cf, by positivity, ?_⟩
  intro N hN Δ hΔ B hB c hc R t hsep
  have h := hfe (1 / 4) (by norm_num) (by norm_num) Δ hΔ N hN (fun _ => B) c hc R t hsep
  rw [show (4 : ℝ) * (1 / 4) * Δ = Δ by ring] at h
  have hfac : (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc N (2 * N),
            (B : ℂ) * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0))
      = B ^ 2 * (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc N (2 * N),
            (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0)) := by
    have hterm : ∀ i j : Fin R,
        (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc N (2 * N),
            (B : ℂ) * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0)
        = B ^ 2 * (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc N (2 * N),
            (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0) := by
      intro i j
      by_cases hp : |t i - t j| ≤ Δ
      · rw [if_pos hp, if_pos hp]
        have hz : (∑ n ∈ Finset.Icc N (2 * N),
              (B : ℂ) * (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))
                / (Real.sqrt (n : ℝ) : ℂ))
            = ∑ n ∈ Finset.Icc N (2 * N),
              (B : ℂ) * ((n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ))
                / (Real.sqrt (n : ℝ) : ℂ)) := by
          refine Finset.sum_congr rfl fun n _ => ?_
          rw [mul_div_assoc]
        rw [hz, normSq_sum_const_mul]
      · rw [if_neg hp, if_neg hp]; ring
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => hterm i j
  rw [hfac] at h
  have hconst : Cf / (1 / 4) * (B ^ 2 * (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc N (2 * N),
            (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0)))
      = (4 * Cf) * B ^ 2 * (∑ i : Fin R, ∑ j : Fin R,
        (if |t i - t j| ≤ Δ then
          ‖∑ n ∈ Finset.Icc N (2 * N),
            (n : ℂ) ^ (Complex.I * ((t i - t j : ℝ) : ℂ)) / (Real.sqrt (n : ℝ) : ℂ)‖ ^ 2
         else 0)) := by ring
  rw [hconst] at h
  exact h

end Commons.NumberTheory.DirichletPolynomial
