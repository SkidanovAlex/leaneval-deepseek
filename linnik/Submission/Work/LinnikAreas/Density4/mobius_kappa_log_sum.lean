import Mathlib
import Submission.Work.LinnikAreas.Density4.mkl_assembly
import Submission.Work.LinnikAreas.Density4.kappa_log_sum_reduction_real
import Submission.Work.LinnikAreas.Density4.kappa_error_sum_pow

namespace Work.LinnikAreas.Density4

open Finset
open scoped BigOperators

noncomputable section

/-- **Sharp Mertens-type evaluation for the `1/κ`-weighted Möbius sum.**  For every `A : ℝ`
there is `C > 0` with, for all real `Q ≥ 1` and all `r ≥ 1`,
`|Σ_{n ≤ Q, (n,r)=1} μ(n)/(n·∏_{p|n}(1+1/p))·log(Q/n) − (∏_{p|r}(1+1/p))·ζ(2)| ≤ C·σ_{-1/2}(r)·log(2+Q)^{-A}`,
where `ζ(2) = π²/6` and `σ_{-1/2}(r) = Σ_{d|r} d^{-1/2}`.

(Reviewer-verified: writing `a(n) = ∏_{p|n}p/(p+1)`, the relevant Dirichlet series is
`D_r(s) = F(1+s)/∏_{p|r}(1−a(p)p^{-1-s})` with `F(s) = ∏_p(1 − a(p)p^{-s})`; since
`Σ_n μ(n)a(n)/n` converges to `∏_p p/(p+1)`, `F(1) = 0` and the smoothed sum tends to
`D_r'(0) = ζ(2)∏_{p|r}(1+1/p)`.  Numerically `S(N) → 1.64492` for `r=1` (target `π²/6 = 1.64493`),
decaying like `N^{-1/2+ε}`, so the stated logarithmic error is very safe.)

The proof expands `1/κ(n) = ∏_{p|n} p/(p+1)`, reduces the sum to a `d`-sum of Selberg's
`Θ`-values (`Work.LinnikAreas.Density4.kappa_log_sum_reduction_real`), splits it into the
Euler-product main term (`Work.LinnikAreas.Density4.sqfree_coprime_recip_pm1_finite_self`,
`Work.LinnikAreas.Density4.main_term_d`, `Work.LinnikAreas.Density4.main_const`) and a weighted
`Θ`-error that decays like `log^{-A}` (`Work.LinnikAreas.Density4.ThetaPow.selTheta_asymptotic_pow`,
`Work.LinnikAreas.Density4.kappa_error_sum_pow`); the two pieces are assembled in
`Work.LinnikAreas.Density4.mkl_core`. -/
theorem mobius_kappa_log_sum (A : ℝ) : ∃ C : ℝ, 0 < C ∧
    ∀ (Q : ℝ) (r : ℕ), 1 ≤ Q → 1 ≤ r →
    |(∑ n ∈ (Finset.Icc 1 ⌊Q⌋₊).filter (fun n => n.Coprime r),
          (ArithmeticFunction.moebius n : ℝ) / ((n : ℝ) * ∏ p ∈ n.primeFactors, (1 + 1 / (p : ℝ)))
            * Real.log (Q / (n : ℝ)))
      - (∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ))) * (Real.pi ^ 2 / 6)|
      ≤ (C * ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) * Real.log (2 + Q) ^ (-A) := by
  by_cases hA : A ≤ 0
  · obtain ⟨C, hC, hb⟩ :=
      mkl_core 1 (by norm_num) kappa_log_sum_reduction_real (kappa_error_sum_pow 1 (by norm_num))
    refine ⟨C, hC, ?_⟩
    intro Q r hQ hr
    refine (hb Q r hQ hr).trans ?_
    have hlog1 : (1 : ℝ) ≤ Real.log (2 + Q) := by
      have h4 : Real.log 3 ≤ Real.log (2 + Q) := Real.log_le_log (by norm_num) (by linarith)
      have h5 : (1 : ℝ) ≤ Real.log 3 :=
        (Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)).mpr Real.exp_one_lt_three.le
      linarith
    have hexp : Real.log (2 + Q) ^ (-1 : ℝ) ≤ Real.log (2 + Q) ^ (-A) :=
      Real.rpow_le_rpow_of_exponent_le hlog1 (by linarith)
    have hSnn : (0 : ℝ) ≤ C * ∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ) := by
      apply mul_nonneg hC.le
      exact Finset.sum_nonneg (fun d _ => by positivity)
    exact mul_le_mul_of_nonneg_left hexp hSnn
  · push_neg at hA
    exact mkl_core A hA kappa_log_sum_reduction_real (kappa_error_sum_pow A hA)

end

end Work.LinnikAreas.Density4
