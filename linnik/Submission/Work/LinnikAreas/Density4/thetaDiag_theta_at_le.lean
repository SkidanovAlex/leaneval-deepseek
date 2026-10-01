import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs

namespace Work.LinnikAreas.Density4

/-- **The diagonal of the `θ`-mollifier at the cut-off `W = e^M` (HB §11, (11.7)).**
For every `n ≥ 1` with `n ≤ e^M`,
`∑_{d | n} θ_d = [n = 1] + Λ(n)/M`.
Indeed `θ_d = μ(d) log(e^M/d)/log(e^M) = μ(d)(M - log d)/M` for `d | n` (the cut-off is automatic
since `d ≤ n ≤ e^M`), so the sum is `(M ∑_{d|n} μ(d) - ∑_{d|n} μ(d) log d)/M`, and the classical
identities `∑_{d|n} μ(d) = [n = 1]`, `∑_{d|n} μ(d) log d = -Λ(n)` finish the job. -/
theorem thetaDiag_theta_at_le (M : ℝ) (hM : 0 < M) (n : ℕ) (hn : 1 ≤ n) (hnW : (n:ℝ) ≤ Real.exp M) :
    (∑ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM (Real.exp M) d)
      = (if n = 1 then 1 else 0) + (ArithmeticFunction.vonMangoldt n) / M := by
  have hMne : M ≠ 0 := ne_of_gt hM
  -- Step 1: `θ_d = μ(d)(M - log d)/M` for every divisor `d` of `n`.
  have hterm : ∀ d ∈ n.divisors, Work.LinnikAreas.Density4.thetaM (Real.exp M) d
      = ((ArithmeticFunction.moebius d : ℝ) * (M - Real.log d)) / M := by
    intro d hd
    have hdle : d ≤ n := Nat.divisor_le hd
    have hdle' : (d:ℝ) ≤ (n:ℝ) := by exact_mod_cast hdle
    have hle : (d:ℝ) ≤ Real.exp M := le_trans hdle' hnW
    have hdne : (d:ℝ) ≠ 0 := by
      have h0 : 0 < d := Nat.pos_of_mem_divisors hd
      positivity
    rw [Work.LinnikAreas.Density4.thetaM, if_pos hle,
      Real.log_div (Real.exp_ne_zero M) hdne, Real.log_exp]
  rw [Finset.sum_congr rfl hterm]
  -- Step 2: `∑_{d | n} μ(d) = [n = 1]`.
  have hmu : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ)) = if n = 1 then 1 else 0 := by
    simp_rw [← ArithmeticFunction.intCoe_apply
      (f := (ArithmeticFunction.moebius : ArithmeticFunction ℤ))]
    rw [← ArithmeticFunction.coe_mul_zeta_apply
      (f := (ArithmeticFunction.moebius : ArithmeticFunction ℝ)) (x := n)]
    rw [ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply]
  -- Step 3: `∑_{d | n} μ(d) log d = -Λ(n)`.
  have hlog : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * Real.log d)
      = - (ArithmeticFunction.vonMangoldt n) := by
    simpa using (ArithmeticFunction.sum_moebius_mul_log_eq (n := n))
  -- Step 4: collect the algebra.
  rw [← Finset.sum_div]
  have hnum : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * (M - Real.log d))
      = (if n = 1 then 1 else 0) * M + ArithmeticFunction.vonMangoldt n := by
    have step1 : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) * (M - Real.log d))
        = ∑ d ∈ n.divisors,
            ((ArithmeticFunction.moebius d : ℝ) * M - (ArithmeticFunction.moebius d : ℝ) * Real.log d) := by
      apply Finset.sum_congr rfl
      intro d _
      ring
    rw [step1, Finset.sum_sub_distrib, ← Finset.sum_mul, hmu, hlog]
    ring
  rw [hnum]
  rw [add_div, mul_div_cancel_right₀ _ hMne]

end Work.LinnikAreas.Density4
