import Mathlib
import Submission.Work.BMF.mr_core.lambdaAbelReduce
import Submission.Work.BMF.mr_core.bumpFnDerivMainTerm
import Submission.Work.BMF.mr_core.bumpFnScaledRpowIntegral
import Submission.Work.BMF.smoothing_exists

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF.mr_direct

open MeasureTheory intervalIntegral Finset

noncomputable section

set_option maxHeartbeats 800000

/-- **Abel summation for the smoothed `Λ`-sum, with the exact error integral** (corrected: the
hypothesis `0 < A` is required — without it the identity is false, since Mathlib's `Real.log` is
even and `4 ≤ Real.log A` is satisfiable with `A < 0`).

`Work.BMF.bumpFn` is the smooth bump of `Submission/Work/BMF/smoothing_exists.lean`
(`1` on `[1/2,2]`, `0` outside `[1/4,4]`).  The smoothed Λ-sum equals the explicit main term
`A ^ (1 + iδ) · ∫ y^{iδ} φ(y)` minus the integral of the weight derivative against the
explicit-formula error `Σ_{n ≤ ⌊t⌋} Λ(n) n^{iδ} − t^{1+iδ}/(1+iδ)`.

PROOF ROUTE (all ingredients already proved in the workspace):
* `Work.BMF.mr_core.lambdaAbelReduce (A δ) hA0` gives
  `Σ_{n ≤ ⌈4A⌉₊} Λ(n) n^{iδ} φ(n/A) = −∫_0^{⌈4A⌉₊} (φ′(t/A)/A) · Σ_{n ≤ ⌊t⌋} Λ(n) n^{iδ} dt`;
* `Work.BMF.mr_core.bumpFnDerivMainTerm (A δ) hA0` gives
  `∫_0^{⌈4A⌉₊} (φ′(t/A)/A) · t^{1+iδ}/(1+iδ) dt = −A^{1+iδ}∫_{1/4}^4 y^{iδ} φ(y) dy`;
* split the integrand as `Σ_{n ≤ ⌊t⌋} Λ(n)n^{iδ} = (Σ ... − t^{1+iδ}/(1+iδ)) + t^{1+iδ}/(1+iδ)`
  and use linearity of the interval integral. -/
theorem lambda_smoothed_abel_clean (A δ : ℝ) (hA0 : 0 < A) (hA : 4 ≤ Real.log A) :
    (∑ n ∈ Finset.Icc 1 ⌈4 * A⌉₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (n : ℂ) ^ (Complex.I * (δ : ℂ)) * ((Work.BMF.bumpFn (n / A)) : ℂ))
      = (A : ℂ) ^ (1 + Complex.I * (δ : ℂ)) *
          (∫ y in (1 / 4 : ℝ)..4, (y : ℂ) ^ (Complex.I * (δ : ℂ)) * ((Work.BMF.bumpFn y) : ℂ))
        - ∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)),
            (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
              ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                  (n : ℂ) ^ (Complex.I * (δ : ℂ)))
                - (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ))) := by
  -- `0 ≤ ⌈4A⌉₊`, and the two integrands of the split
  have hM0 : (0 : ℝ) ≤ ((⌈4 * A⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hF'cont : Continuous
      (fun t : ℝ => (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ)) :=
    Work.BMF.mr_core.continuous_deriv_bumpFn_div A
  have hecont : Continuous
      (fun t : ℝ => (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ))) :=
    (Complex.continuous_ofReal_cpow_const (by simp)).div_const _
  -- integrability of the weight derivative against the (staircase) partial sum
  have hCint : IntervalIntegrable
      (fun t : ℝ => (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
        (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
            (n : ℂ) ^ (Complex.I * (δ : ℂ))))
      volume (0 : ℝ) (((⌈4 * A⌉₊ : ℕ) : ℝ)) := by
    rw [intervalIntegrable_iff_integrableOn_Icc_of_le hM0]
    refine integrableOn_mul_sum_Icc
      (fun n : ℕ => ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
        (n : ℂ) ^ (Complex.I * (δ : ℂ))) le_rfl ?_
    simpa using hF'cont.continuousOn.integrableOn_Icc
  -- integrability of the weight derivative against the explicit main term
  have heint : IntervalIntegrable
      (fun t : ℝ => (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
        ((t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ))))
      volume (0 : ℝ) (((⌈4 * A⌉₊ : ℕ) : ℝ)) :=
    (hF'cont.mul hecont).intervalIntegrable _ _
  -- split the Abel integral: partial sum = explicit-formula error + main term
  have hsplit : (∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)),
        (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
          (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
              (n : ℂ) ^ (Complex.I * (δ : ℂ))))
      = (∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)),
            (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
              ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                  (n : ℂ) ^ (Complex.I * (δ : ℂ)))
                - (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ))))
        + ∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)),
            (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
              ((t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ))) := by
    have hsub := intervalIntegral.integral_sub hCint heint
    have hcongr : (∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)),
          (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
            (∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                (n : ℂ) ^ (Complex.I * (δ : ℂ)))
          - (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
            ((t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ))))
        = ∫ t in (0 : ℝ)..(((⌈4 * A⌉₊ : ℕ) : ℝ)),
            (((deriv Work.BMF.bumpFn (t / A)) : ℝ) : ℂ) / (A : ℂ) *
              ((∑ n ∈ Finset.Icc 1 ⌊t⌋₊, ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) *
                  (n : ℂ) ^ (Complex.I * (δ : ℂ)))
                - (t : ℂ) ^ (1 + Complex.I * (δ : ℂ)) / (1 + Complex.I * (δ : ℂ))) :=
      intervalIntegral.integral_congr fun t _ => by ring
    rw [hcongr] at hsub
    rw [hsub]
    ring
  rw [Work.BMF.mr_core.lambdaAbelReduce A δ hA0, hsplit,
    Work.BMF.mr_core.bumpFnDerivMainTerm A δ hA0,
    Work.BMF.mr_core.bumpFnScaledRpowIntegral A δ hA0]
  ring

end

end Work.BMF.mr_direct
