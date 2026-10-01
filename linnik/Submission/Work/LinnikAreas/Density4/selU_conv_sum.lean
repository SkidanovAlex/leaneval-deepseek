import Mathlib
import Submission.Work.LinnikAreas.Density4.SelbergDefs
import Submission.Work.LinnikAreas.Density4.sum_Icc_div_reindex
import Submission.Commons.NumberTheory.Moebius.sum_Icc_divisors_bijection

namespace Work.LinnikAreas.Density4

open scoped BigOperators
open Finset

/-- The Möbius sum over the divisors of `n`, in the reindexed form `d ↦ n/d`:
`∑_{d | n} μ(n/d) = [n = 1]`.  Obtained from `(μ * ζ) = 1` together with the
antidiagonal reindexing `Nat.sum_divisorsAntidiagonal'`. -/
lemma mobius_div_divisors_sum (n : ℕ) :
    (∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n/d) : ℝ)) = if n = 1 then 1 else 0 := by
  have h1 : (∑ d ∈ n.divisors, (ArithmeticFunction.moebius (n/d) : ℝ))
      = ∑ d ∈ n.divisors,
          ((ArithmeticFunction.moebius (n/d) : ℝ) * (ArithmeticFunction.zeta d : ℝ)) := by
    apply Finset.sum_congr rfl
    intro d hd
    rw [ArithmeticFunction.zeta_apply_ne (Nat.pos_of_mem_divisors hd).ne']
    simp
  rw [h1]
  have h3 : (∑ x ∈ n.divisorsAntidiagonal,
        (ArithmeticFunction.moebius x.1 : ℝ) * (ArithmeticFunction.zeta x.2 : ℝ))
      = ∑ i ∈ n.divisors,
          (ArithmeticFunction.moebius (n/i) : ℝ) * (ArithmeticFunction.zeta i : ℝ) := by
    simpa using Nat.sum_divisorsAntidiagonal' (n := n)
      (f := fun a b => (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.zeta b : ℝ))
  have h2 : (∑ d ∈ n.divisors,
        (ArithmeticFunction.moebius (n/d) : ℝ) * (ArithmeticFunction.zeta d : ℝ))
      = (ArithmeticFunction.moebius * ArithmeticFunction.zeta : ArithmeticFunction ℝ) n := by
    rw [ArithmeticFunction.mul_apply]
    exact h3.symm
  rw [h2, ArithmeticFunction.coe_moebius_mul_coe_zeta, ArithmeticFunction.one_apply]

/-- Unfolding `selU` at the rational point `N/n` with `1 ≤ n`, and absorbing the factor `1/n`
into the summand.  Uses `Nat.floor_div_natCast` (`⌊N/n⌋₊ = N/n`) and the identification
`(N/n)/m = N/(n*m)`. -/
lemma inv_mul_selU_nat_div (N n : ℕ) (hn : 1 ≤ n) :
    (1/(n:ℝ)) * selU ((N:ℝ)/(n:ℝ))
      = ∑ m ∈ Finset.Icc 1 (N/n),
          (ArithmeticFunction.moebius m : ℝ) * Real.log ((N:ℝ)/(((n*m:ℕ):ℝ))) / (((n*m:ℕ):ℝ)) := by
  rw [selU, Nat.floor_div_natCast, Nat.floor_natCast]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro m hm
  rw [Nat.cast_mul]
  rw [show (N:ℝ)/(n:ℝ)/(m:ℝ) = (N:ℝ)/((n:ℝ)*(m:ℝ)) by rw [div_div]]
  have hn' : (n:ℝ) ≠ 0 := by positivity
  have hm' : (m:ℝ) ≠ 0 := by
    have : 1 ≤ m := (Finset.mem_Icc.mp hm).1
    positivity
  field_simp

/-- Only the term `n = 1` survives against the indicator of `{1}`. -/
lemma sum_log_div_mul_ite (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N, (Real.log ((N:ℝ)/(n:ℝ)) / (n:ℝ)) * (if n = 1 then 1 else 0))
      = Real.log (N:ℝ) := by
  rw [Finset.sum_eq_single_of_mem (a := 1) (Finset.mem_Icc.mpr ⟨le_refl 1, hN⟩)
        (by intro b _ hb; rw [if_neg hb, mul_zero])]
  simp

/-- Mertens-type convolution identity: `∑_{n ≤ N} (1/n) * selU(N/n) = log N`.
Hint: expand `selU`, using `Nat.floor_div_natCast` so that `m ≤ ⌊N/n⌋₊ ↔ n*m ≤ N`; then the pairs
`(n,m)` with `n*m ≤ N` are reindexed by `k = n*m`, giving
`∑_{k ≤ N} (log(N/k)/k) * ∑_{m | k} μ(m) = log N` since `∑_{m|k} μ(m) = [k = 1]`.
The workspace already has the reindexing lemma
`Commons.NumberTheory.Moebius.sum_Icc_divisors_bijection (R N : ℕ) (f : ℕ → ℕ → ℝ)` (take `R = 0`). -/
theorem selU_conv_sum (N : ℕ) (hN : 1 ≤ N) :
    (∑ n ∈ Finset.Icc 1 N,
        (1/(n:ℝ)) * Work.LinnikAreas.Density4.selU ((N:ℝ)/(n:ℝ))) = Real.log (N:ℝ) := by
  have h1 : (∑ n ∈ Finset.Icc 1 N, (1/(n:ℝ)) * selU ((N:ℝ)/(n:ℝ)))
      = ∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N/n),
          (ArithmeticFunction.moebius m : ℝ) * Real.log ((N:ℝ)/(((n*m:ℕ):ℝ)))
            / (((n*m:ℕ):ℝ)) := by
    apply Finset.sum_congr rfl
    intro n hn
    exact inv_mul_selU_nat_div N n (Finset.mem_Icc.mp hn).1
  have h2 : (∑ n ∈ Finset.Icc 1 N, ∑ m ∈ Finset.Icc 1 (N/n),
          (ArithmeticFunction.moebius m : ℝ) * Real.log ((N:ℝ)/(((n*m:ℕ):ℝ)))
            / (((n*m:ℕ):ℝ)))
      = ∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
          (ArithmeticFunction.moebius (n/d) : ℝ)
            * Real.log ((N:ℝ)/(((d*(n/d):ℕ):ℝ))) / (((d*(n/d):ℕ):ℝ)) := by
    simpa using sum_Icc_div_reindex N (fun _ => True)
      (fun d m => (ArithmeticFunction.moebius m : ℝ)
        * Real.log ((N:ℝ)/(((d*m:ℕ):ℝ))) / (((d*m:ℕ):ℝ)))
  have h3 : (∑ n ∈ Finset.Icc 1 N, ∑ d ∈ n.divisors,
          (ArithmeticFunction.moebius (n/d) : ℝ)
            * Real.log ((N:ℝ)/(((d*(n/d):ℕ):ℝ))) / (((d*(n/d):ℕ):ℝ)))
      = ∑ n ∈ Finset.Icc 1 N,
          (Real.log ((N:ℝ)/(n:ℝ)) / (n:ℝ)) * (if n = 1 then 1 else 0) := by
    apply Finset.sum_congr rfl
    intro n hn
    have hstep : ∀ d ∈ n.divisors,
        (ArithmeticFunction.moebius (n/d) : ℝ)
            * Real.log ((N:ℝ)/(((d*(n/d):ℕ):ℝ))) / (((d*(n/d):ℕ):ℝ))
        = (ArithmeticFunction.moebius (n/d) : ℝ) * (Real.log ((N:ℝ)/(n:ℝ)) / (n:ℝ)) := by
      intro d hd
      have hdvd : d ∣ n := Nat.dvd_of_mem_divisors hd
      rw [Nat.mul_div_cancel' hdvd]
      ring
    rw [Finset.sum_congr rfl hstep, ← Finset.sum_mul, mobius_div_divisors_sum n]
    ring
  rw [h1, h2, h3, sum_log_div_mul_ite N hN]

end Work.LinnikAreas.Density4
