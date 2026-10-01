import Mathlib
import Submission.Work.LinnikAreas.Density4.BzBilinDefs
import Submission.Work.LinnikAreas.Density4.sqfree_coprime_count
import Submission.Work.LinnikAreas.Density4.totient_div_mul_moebU

namespace Work.LinnikAreas.Density4.BzBilin

open Finset

/-- `μ²(n)` as a real number is the indicator of the squarefree integers. -/
lemma moebius_sq_cast_eq_indicator (n : ℕ) :
    (ArithmeticFunction.moebius n : ℝ) ^ 2 = if Squarefree n then 1 else 0 := by
  have h : (ArithmeticFunction.moebius n : ℝ) ^ 2
      = ((ArithmeticFunction.moebius n ^ 2 : ℤ) : ℝ) := by
    push_cast; ring
  rw [h, ArithmeticFunction.moebius_sq]
  by_cases hs : Squarefree n <;> simp [hs]

/-- The squarefree indicator converts the count of squarefree integers into a Möbius-square sum. -/
lemma sum_mu_sq_eq_sum_squarefree (Q r : ℕ) :
    (∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n r),
        (ArithmeticFunction.moebius n : ℝ) ^ 2)
      = ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n r ∧ Squarefree n),
          (1 : ℝ) := by
  have h1 : (∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n r),
        (ArithmeticFunction.moebius n : ℝ) ^ 2)
      = ∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n r),
          (if Squarefree n then (1 : ℝ) else 0) :=
    Finset.sum_congr rfl (fun n _ => moebius_sq_cast_eq_indicator n)
  rw [h1, ← Finset.sum_filter, Finset.filter_filter]

/-- The main term `(φ(r)/r)·moebU r` of the squarefree count equals `(π²/6)⁻¹·∏_{p|r} p/(p+1)`. -/
lemma totient_div_mul_moebU_eq_pi (r : ℕ) (hr : 1 ≤ r) :
    ((r.totient : ℝ) / (r : ℝ)) * moebU r = (Real.pi ^ 2 / 6)⁻¹ * sqDens r := by
  rw [totient_div_mul_moebU r hr, zeta2_eq_pi_sq_div_six, sqDens]
  congr 1
  have hr0 : (r : ℝ) ≠ 0 := by
    have : (0 : ℕ) < r := by omega
    exact_mod_cast this.ne'
  have hL : (r : ℝ) / ((r : ℝ) * ∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ)))
      = (∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ)))⁻¹ := by
    rw [div_eq_mul_inv, mul_inv, ← mul_assoc, mul_inv_cancel₀ hr0, one_mul]
  have hR : (∏ p ∈ r.primeFactors, (1 + 1 / (p : ℝ)))⁻¹
      = ∏ p ∈ r.primeFactors, (p : ℝ) / ((p : ℝ) + 1) := by
    rw [← Finset.prod_inv_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hp0 : (p : ℝ) ≠ 0 := by
      have hpp : p ≠ 0 := (Nat.prime_of_mem_primeFactors hp).ne_zero
      exact_mod_cast hpp
    rw [show (1 : ℝ) + 1 / (p : ℝ) = ((p : ℝ) + 1) / (p : ℝ) by
      field_simp, inv_div]
  rw [hL, hR]

/-- The squarefree integers coprime to `r`, counted with a `√Q·σ_{-1/2}(r)` error
(An, arXiv:2206.10104, Lemma 0108 for `k = ℚ`).

SUGGESTED ROUTE (elementary, no zeros of L-functions).  Write `[n ⟂ r] = Σ_{b | r, b | n} μ b`
and `μ²(n) = Σ_{a² | n} μ a` (`∑_{d ∣ n, d² ∣ n} μ d = μ² n`; prove it either by multiplicativity
over prime powers, or as `ArithmeticFunction.moebius` composed with the square part).  Then
`Σ_{n ≤ Q, (n,r)=1} μ²(n) = Σ_{a} Σ_{b | r} [a ⟂ r] μ a μ b ⌊Q/(a²b)⌋`
(a term with `a²b > Q` contributes `0`; the workspace file
`Submission.Work.LinnikAreas.Density4.sqfree_coprime_double_sum` states this rearrangement, but it
carries a `sorry` — it, `double_sum_error_bound`, `sqfree_coprime_count` (Density4) and
`Work.BzHard.squarefree_coprime_count` are all sorry-carriers and MUST NOT be used as inputs, since
they inject `sorryAx`).
Compare with `Q · (Σ'_{a, (a,r)=1} μ a / a²) · (Σ_{b | r} μ b / b)`: writing `⌊x⌋ = x - {x}`,
the fractional-part sum is `Σ_{b|r} Σ_{a² b ≤ Q} |μ a μ b {Q/(a²b)}| ≤ Σ_{b | r} √(Q/b)`
(KEY: reverse the order of summation, so the number of `a`'s for a fixed `b` is `≤ √(Q/b)`; do NOT
bound each inner `a`-sum trivially by `√Q`, which would give `τ(r)` instead of `σ_{-1/2}(r)`),
while the `Q/(a²b)` piece differs from the infinite series by
`≤ Q·Σ_{b|r} b⁻¹·(2√b/√Q) = 2√Q σ_{-1/2}(r)` (tail `Σ_{a > N} 1/a² ≤ 1/N`).  Finally
`(Σ'_{a,(a,r)=1} μ a/a²)·(Σ_{b|r} μ b/b) = (6/π²)·∏_{p | r} p/(p+1)`: the first factor is
`∏_{p ∤ r}(1 - p⁻²)` (Euler product; `Submission.Work.LinnikAreas.Density4.moebius_coprime_recip_sq_tsum`
is proved and states it), the second is `∏_{p | r} (1 - 1/p)`
(`Submission.Work.LinnikAreas.Density4.sum_divisors_moebius_div_eq_prod` / the multiplicative
divisor-sum lemma `Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors`), and
`(1 - p⁻²)(1 - 1/p) = p/(p+1)`.  A slightly larger absolute constant `C` is fine. -/
theorem sqfree_coprime_count_sigma :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q r : ℕ), 1 ≤ Q → 1 ≤ r →
      |(∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n r),
          (ArithmeticFunction.moebius n : ℝ) ^ 2)
        - (Real.pi ^ 2 / 6)⁻¹ * Work.LinnikAreas.Density4.sqDens r * (Q : ℝ)|
      ≤ C * Real.sqrt (Q : ℝ) * Work.LinnikAreas.Density4.sigmaHalf r := by
  refine ⟨3, by norm_num, ?_⟩
  intro Q r hQ hr
  have hmain := sqfree_count_main_est Q r hQ hr
  have hval : (Real.pi ^ 2 / 6)⁻¹ * sqDens r * (Q : ℝ)
      = (Q : ℝ) * (((r.totient : ℝ) / (r : ℝ)) * moebU r) := by
    rw [← totient_div_mul_moebU_eq_pi r hr]; ring
  rw [sum_mu_sq_eq_sum_squarefree, hval, sigmaHalf]
  exact hmain

end Work.LinnikAreas.Density4.BzBilin
