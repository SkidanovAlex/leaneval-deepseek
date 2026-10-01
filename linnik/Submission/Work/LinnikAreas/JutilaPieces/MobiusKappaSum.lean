import Mathlib
import Submission.Work.LinnikAreas.JutilaPieces.MobiusKappaDefs
import Submission.Work.LinnikAreas.JutilaPieces.MobiusKappaAux
import Submission.Work.LinnikAreas.JutilaPieces.KappaSumBoundPow

/-!
# The Möbius `1/κ`-sum: An's (Graham's) Lemma 12

`Σ_{n ≤ Q, (n,r)=1} μ(n)/κ(n) = O_A(σ_{-1/2}(r)·(log(2+Q))^{-A})`, where
`κ(n) = n·∏_{p | n}(1 + 1/p)` and `σ_{-1/2}(r) = Σ_{d | r} d^{-1/2}`.

The proof goes through the Selberg-diagonalised expansion of the *smoothed* sum
(`KappaSum.kappaLogSum_expansion`) with the sharp `Θ`-asymptotic
`ThetaPow.selTheta_asymptotic_pow`, and the `c`-trick that recovers the unweighted sum
(`kappaSum_bound_pow`); both live in the companion modules above.
-/

open Finset
open scoped BigOperators

namespace Work.LinnikAreas.JutilaPieces

noncomputable section

/-- The target sum is `kappaSum` and the right-hand factor is `sHalf`. -/
lemma mobius_kappa_sum_key (E : ℝ) (hE : 0 < E) :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (r : ℕ), 1 ≤ Q → 1 ≤ r →
      |∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => n.Coprime r),
          (ArithmeticFunction.moebius n : ℝ)
            / ((n : ℝ) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)))|
        ≤ (C * ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * Real.log (2 + Q) ^ (-E) := by
  obtain ⟨C0, hC0pos, hC0⟩ := kappaSum_bound_pow E hE
  refine ⟨C0, hC0pos, ?_⟩
  intro Q r hQ hr
  have h1 := hC0 Q r hQ hr
  have hLHS : (∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => n.Coprime r),
      (ArithmeticFunction.moebius n : ℝ)
        / ((n : ℝ) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ))))
      = Work.LinnikAreas.Density4.kappaSum ⌊Q⌋₊ r := by
    rw [Work.LinnikAreas.Density4.kappaSum]
    apply Finset.sum_congr rfl
    intro n _
    rfl
  rw [hLHS]
  rw [Work.LinnikAreas.Density4.sHalf] at h1
  exact h1

theorem MobiusKappaSum (A : ℝ) : ∃ C : ℝ, 0 < C ∧ ∀ (Q : ℝ) (r : ℕ), 1 ≤ Q → 1 ≤ r →
    |∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => n.Coprime r),
        (ArithmeticFunction.moebius n : ℝ) / ((n : ℝ) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)))|
      ≤ (C * ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * Real.log (2 + Q) ^ (-A) := by
  by_cases hA : A ≤ 0
  · obtain ⟨C1, hC1pos, hC1⟩ := mobius_kappa_sum_key 1 (by norm_num)
    refine ⟨C1, hC1pos, ?_⟩
    intro Q r hQ hr
    have h1 := hC1 Q r hQ hr
    have hlog1 : 1 ≤ Real.log (2 + Q) := one_le_log_two_add' hQ
    have hlogpos : 0 < Real.log (2 + Q) := Real.log_pos (by linarith)
    have hexp : (Real.log (2 + Q)) ^ (-1 : ℝ) ≤ (Real.log (2 + Q)) ^ (-A) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
    calc |∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => n.Coprime r),
          (ArithmeticFunction.moebius n : ℝ)
            / ((n : ℝ) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)))|
        ≤ (C1 * ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
            * Real.log (2 + Q) ^ (-1 : ℝ) := h1
      _ ≤ (C1 * ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ))
            * Real.log (2 + Q) ^ (-A) :=
          mul_le_mul_of_nonneg_left hexp (by positivity)
  · obtain ⟨C1, hC1pos, hC1⟩ := mobius_kappa_sum_key A (lt_of_not_ge hA)
    exact ⟨C1, hC1pos, hC1⟩

end

end Work.LinnikAreas.JutilaPieces
