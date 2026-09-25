import Submission.Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies

open scoped Real BigOperators ComplexConjugate
open MeasureTheory intervalIntegral Complex

namespace Commons.Analysis.Fourier

/-- **Near-orthogonality of `1`-separated exponentials.**  There is a universal constant
`C` such that for any finite family of real frequencies `lam k` that are pairwise separated
by at least `1`, and any complex coefficients `a k`, the mean square of the exponential sum
`∑ k, a k · e^{i·(lam k)·u}` over the unit interval `[0,1]` is bounded by `C · ∑ k, ‖a k‖²`.

This expresses the fact that `{u ↦ e^{i·λ·u}}_λ` is a Bessel system of `L²([0,1])` when the
frequencies are `1`-separated.  It is a direct consequence of the sharp mean-value estimate
`Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies` (Hilbert's
inequality for separated frequencies), here specialized to the separation `δ = 1` and the
interval `[0,1]`. -/
theorem separated_exponentials_near_orthogonal :
    ∃ C : ℝ, 0 < C ∧ ∀ (K : ℕ) (lam : Fin K → ℝ),
      (∀ k l : Fin K, k ≠ l → 1 ≤ |lam k - lam l|) →
      ∀ (a : Fin K → ℂ),
        ∫ u in (0 : ℝ)..1,
            ‖∑ k : Fin K, a k * Complex.exp (Complex.I * (lam k : ℂ) * (u : ℂ))‖ ^ 2
          ≤ C * ∑ k : Fin K, ‖a k‖ ^ 2 := by
  obtain ⟨C, hCpos, hC⟩ :=
    Commons.NumberTheory.DirichletPolynomial.mv_integral_separated_frequencies
  refine ⟨1 + C, by linarith, ?_⟩
  intro K lam hsep a
  have hsep' : ∀ i j : Fin K, i ≠ j → (1 : ℝ) ≤ |lam i - lam j| := fun i j hij => hsep i j hij
  have h := hC 1 (by norm_num) K lam a hsep' 0 1 (by norm_num)
  -- The mean-value estimate is stated with the frequency appearing as `(lam k) * t`;
  -- rewrite the exponent into that shape.
  have hform : (∫ u in (0 : ℝ)..1,
        ‖∑ k : Fin K, a k * Complex.exp (Complex.I * (lam k : ℂ) * (u : ℂ))‖ ^ 2)
      = ∫ t in (0 : ℝ)..1,
        ‖∑ k : Fin K, a k * Complex.exp (Complex.I * ((lam k : ℂ) * (t : ℂ)))‖ ^ 2 := by
    apply intervalIntegral.integral_congr
    intro u _
    change ‖∑ k : Fin K, a k * Complex.exp (Complex.I * (lam k : ℂ) * (u : ℂ))‖ ^ 2
      = ‖∑ k : Fin K, a k * Complex.exp (Complex.I * ((lam k : ℂ) * (u : ℂ)))‖ ^ 2
    rw [show (∑ k : Fin K, a k * Complex.exp (Complex.I * (lam k : ℂ) * (u : ℂ)))
        = ∑ k : Fin K, a k * Complex.exp (Complex.I * ((lam k : ℂ) * (u : ℂ))) from by
          apply Finset.sum_congr rfl
          intro k _
          simp only [mul_assoc]]
  calc (∫ u in (0 : ℝ)..1,
        ‖∑ k : Fin K, a k * Complex.exp (Complex.I * (lam k : ℂ) * (u : ℂ))‖ ^ 2)
      = ∫ t in (0 : ℝ)..1,
        ‖∑ k : Fin K, a k * Complex.exp (Complex.I * ((lam k : ℂ) * (t : ℂ)))‖ ^ 2 := hform
    _ ≤ (1 - 0 + C / 1) * ∑ k : Fin K, ‖a k‖ ^ 2 := h
    _ = (1 + C) * ∑ k : Fin K, ‖a k‖ ^ 2 := by ring

end Commons.Analysis.Fourier
