import Mathlib
import Submission.Work.LinnikAreas.Density4.Defs

namespace Work.LinnikAreas.Density4

open scoped BigOperators

/-- The Möbius divisor-sum identity `∑_{d | n} μ(d) = [n = 1]`, over `ℤ`. -/
private lemma sum_moebius_divisors_eq (n : ℕ) :
    (∑ d ∈ n.divisors, ArithmeticFunction.moebius d : ℤ) = if n = 1 then 1 else 0 := by
  rw [← ArithmeticFunction.coe_mul_zeta_apply (f := ArithmeticFunction.moebius) (x := n),
    ArithmeticFunction.moebius_mul_coe_zeta]
  exact ArithmeticFunction.one_apply

/-- **Heath-Brown (11.10).**  For the mollifier `ψ_d` of (11.6) (`Work.LinnikAreas.Density4.psiM`: a
cut-off Möbius weight, `μ(d)` for `d ≤ U`, `μ(d)log(V/d)/log(V/U)` for `U ≤ d ≤ V`, `0` beyond), the
divisor sum collapses below `U`: for `2 ≤ n ≤ U` we have `Σ_{d | n} ψ_d = Σ_{d | n} μ(d) = 0`.
(Also `Σ_{d|1} ψ_d = 1`.)  This support fact is what makes the weights `e^{-n/X} - e^{-n𝓛²/U}` in HB
(11.9)–(11.14) small, and is used both in the zero detector and in the evaluation of `Σ_n b_n²`. -/
theorem psiM_divisor_sum_zero {U V : ℝ} (hU : 1 ≤ U) (hUV : U ≤ V) {n : ℕ} (hn : 2 ≤ n)
    (hnU : (n : ℝ) ≤ U) :
    ∑ d ∈ n.divisors, Work.LinnikAreas.Density4.psiM U V d = 0 := by
  have hn1 : n ≠ 1 := by omega
  have key : ∀ d ∈ n.divisors, psiM U V d = (ArithmeticFunction.moebius d : ℝ) := by
    intro d hd
    have hdn : d ∣ n := Nat.dvd_of_mem_divisors hd
    have hdle : d ≤ n := Nat.le_of_dvd (by omega) hdn
    have hdU : (d : ℝ) ≤ U := by
      have : (d : ℝ) ≤ (n : ℝ) := by exact_mod_cast hdle
      linarith
    rw [psiM, if_pos hdU]
  rw [Finset.sum_congr rfl key]
  have hcast : ((∑ d ∈ n.divisors, ArithmeticFunction.moebius d : ℤ) : ℝ)
      = ∑ d ∈ n.divisors, (ArithmeticFunction.moebius d : ℝ) := by
    push_cast
    rfl
  rw [← hcast, sum_moebius_divisors_eq n, if_neg hn1]
  norm_num

end Work.LinnikAreas.Density4
