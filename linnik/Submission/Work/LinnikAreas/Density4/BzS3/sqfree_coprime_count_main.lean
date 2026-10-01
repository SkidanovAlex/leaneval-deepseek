import Mathlib
import Submission.Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
import Submission.Work.LinnikAreas.Density4.sqfree_moebius_double_sum
import Submission.Work.LinnikAreas.Density4.double_sum_error_bound
import Submission.Work.LinnikAreas.Density4.moebius_coprime_recip_sq_tsum

namespace Work.LinnikAreas.Density4.BzS3

open Finset

/-!
# The squarefree count in a coprime class

We assemble the proof of

`#{n ≤ Q : (n,r) = 1, n squarefree} = Q · (6/π²) · ∏_{p | r} p/(p+1) + O(√Q · Σ_{d | r} 1/√d)`.

The count is written with the weight `μ(n)²`, which is the squarefree indicator
(`ArithmeticFunction.moebius_sq`).  Three ingredients, each proved elsewhere in this workspace
and sorry-free, are used:

* `sqfree_moebius_double_sum` (module `…Density4.sqfree_moebius_double_sum`): the exact Möbius
  rearrangement of the count into the double sum
  `Σ_{b | r} μ(b) · Σ_{a ≤ Q, (a,r)=1} μ(a)·⌊Q/(b a²)⌋`;
* `double_sum_error_bound` (module `…Density4.double_sum_error_bound`): that double sum equals
  `Q · (Σ'_{(a,r)=1} μ(a)/a²) · (Σ_{b | r} μ(b)/b)` up to `4√Q · Σ_{d | r} 1/√d`;
* `moebius_coprime_recip_sq_tsum` (module `…Density4.moebius_coprime_recip_sq_tsum`):
  `Σ'_{(a,r)=1} μ(a)/a² = (6/π²)·∏_{p | r}(1 - p⁻²)⁻¹`.

The remaining work done in this file is (i) the pointwise identification `μ(n)² = [n squarefree]`,
(ii) the evaluation `Σ_{b | r} μ(b)/b = ∏_{p | r}(1 - 1/p)` and the local identity
`(1 - p⁻²)⁻¹·(1 - 1/p) = p/(p+1)`, whose product is `(6/π²)·∏_{p | r} p/(p+1)`, and (iii) the
reindexing that puts the double sum of `sqfree_moebius_double_sum` into the exact shape expected
by `double_sum_error_bound`.
-/

/-- The squarefree indicator in the form needed here: the Möbius weight is `1` on squarefree
integers and `0` otherwise.  (`ArithmeticFunction.moebius_sq` in `ℤ`, transported to `ℝ`.) -/
lemma moebius_sq_eq_indicator (n : ℕ) :
    (ArithmeticFunction.moebius n : ℝ) ^ 2 = if Squarefree n then (1 : ℝ) else 0 := by
  rw [show (ArithmeticFunction.moebius n : ℝ)
      = ((ArithmeticFunction.moebius n : ℤ) : ℝ) from rfl]
  rw [← Int.cast_pow, ArithmeticFunction.moebius_sq]
  by_cases h : Squarefree n <;> simp [h]

/-- The finite Möbius divisor sum `Σ_{b | r} μ(b)/b = ∏_{p | r} (1 - 1/p)`, obtained from
`prod_primeFactors_one_add_eq_sum_divisors` applied to the multiplicative function `b ↦ μ(b)/b`
(which vanishes on the prime powers `p^k`, `k ≥ 2`). -/
theorem sum_divisors_moebius_div_eq_prod (r : ℕ) (hr : 1 ≤ r) :
    (∑ b ∈ r.divisors, (ArithmeticFunction.moebius b : ℝ) / (b : ℝ))
      = ∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ)) := by
  set f : ℕ → ℝ := fun b => (ArithmeticFunction.moebius b : ℝ) / (b : ℝ) with hf
  have hf1 : f 1 = 1 := by
    simp [hf]
  have hfm : ∀ a b : ℕ, Nat.Coprime a b → f (a * b) = f a * f b := by
    intro a b hab
    by_cases ha : a = 0
    · subst ha
      have hb : b = 1 := (Nat.coprime_zero_left b).mp hab
      subst hb; simp [hf]
    by_cases hb : b = 0
    · subst hb
      have ha1 : a = 1 := (Nat.coprime_zero_right a).mp hab
      subst ha1; simp [hf]
    have hmul : ArithmeticFunction.moebius (a * b)
        = ArithmeticFunction.moebius a * ArithmeticFunction.moebius b :=
      ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime
        (Nat.coprime_iff_gcd_eq_one.mp hab)
    have haR : (a : ℝ) ≠ 0 := by exact_mod_cast ha
    have hbR : (b : ℝ) ≠ 0 := by exact_mod_cast hb
    simp only [hf]
    rw [hmul]
    push_cast
    field_simp
  have hfs : ∀ p k : ℕ, p.Prime → 2 ≤ k → f (p ^ k) = 0 := by
    intro p k hp hk
    simp only [hf]
    rw [ArithmeticFunction.moebius_apply_prime_pow hp (by omega : k ≠ 0)]
    simp [show k ≠ 1 by omega]
  have h := Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors
    f r (by omega) hf1 hfm hfs
  rw [← h]
  refine Finset.prod_congr rfl fun p hp => ?_
  simp only [hf]
  rw [ArithmeticFunction.moebius_apply_prime (Nat.prime_of_mem_primeFactors hp)]
  push_cast
  ring

/-- The local factor identity `(1 - p⁻²)⁻¹ · (1 - 1/p) = p/(p+1)` at a prime `p`. -/
private lemma local_factor (p : ℕ) (hp : p.Prime) :
    (1 - (1 : ℝ) / (p : ℝ) ^ 2)⁻¹ * (1 - 1 / (p : ℝ)) = (p : ℝ) / ((p : ℝ) + 1) := by
  have hp2 : (2 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hp.two_le
  have hpm1 : (p : ℝ) - 1 ≠ 0 := by linarith
  have hpp1 : (p : ℝ) + 1 ≠ 0 := by positivity
  have hp2m1 : (p : ℝ) ^ 2 - 1 ≠ 0 := by nlinarith
  have hne1 : (1 : ℝ) - 1 / (p : ℝ) ^ 2 ≠ 0 := by
    have : (1 : ℝ) / (p : ℝ) ^ 2 < 1 := by rw [div_lt_one (by positivity)]; nlinarith
    linarith
  have hne2 : (1 : ℝ) - 1 / (p : ℝ) ≠ 0 := by
    have : (1 : ℝ) / (p : ℝ) < 1 := by rw [div_lt_one (by positivity)]; linarith
    linarith
  field_simp
  ring

/-- **The main term in closed form.**  The product of the two series produced by the Möbius
rearrangement equals `(∏_{p | r} p/(p+1)) / (π²/6)`: the convergent Euler product
`Σ'_{(a,r)=1} μ(a)/a² = (6/π²)∏_{p | r}(1 - p⁻²)⁻¹` times the finite product
`∏_{p | r}(1 - 1/p)`, using `(1 - p⁻²)⁻¹(1 - 1/p) = p/(p+1)` and `(π²/6)⁻¹ = 6/π²`. -/
theorem main_term_eq (r : ℕ) (hr : 1 ≤ r) :
    (∏ p ∈ r.primeFactors, (p : ℝ) / ((p : ℝ) + 1)) / (Real.pi ^ 2 / 6)
      = (∑' a : ℕ,
          if Nat.Coprime a r then (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2 else 0)
        * (∑ b ∈ r.divisors, (ArithmeticFunction.moebius b : ℝ) / (b : ℝ)) := by
  rw [Work.LinnikAreas.Density4.moebius_coprime_recip_sq_tsum r hr,
    sum_divisors_moebius_div_eq_prod r hr]
  have hprod : (∏ p ∈ r.primeFactors, (1 - (1 : ℝ) / (p : ℝ) ^ 2)⁻¹)
      * (∏ p ∈ r.primeFactors, (1 - 1 / (p : ℝ)))
      = ∏ p ∈ r.primeFactors, (p : ℝ) / ((p : ℝ) + 1) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun p hp => ?_
    exact local_factor p (Nat.prime_of_mem_primeFactors hp)
  rw [mul_assoc, hprod]
  rw [div_eq_mul_inv, inv_div]
  ring

/-- **Reindexing of the double sum.**  The double sum produced by `sqfree_moebius_double_sum`
(sum over `b | r` of `μ(b)` times the `a`-sum) is the double sum of `double_sum_error_bound`
(sum over `a ≤ Q` of the `b | r`-sum), the two differing only by the order of summation and the
order of the factors `μ(a) μ(b)` and `b·a² = a²·b`. -/
theorem sqfree_double_sum_reindex (Q r : ℕ) (_hr : 1 ≤ r) :
    (∑ m₀ ∈ r.divisors, (ArithmeticFunction.moebius m₀ : ℝ) *
        ∑ m₂ ∈ (Finset.Icc 1 Q).filter (fun m₂ => Nat.Coprime m₂ r),
          (ArithmeticFunction.moebius m₂ : ℝ) * (((Q / (m₀ * m₂ ^ 2)) : ℕ) : ℝ))
      = ∑ a ∈ Finset.Icc 1 Q, ∑ b ∈ r.divisors,
          (if Nat.Coprime a r then
            (ArithmeticFunction.moebius a : ℝ) * (ArithmeticFunction.moebius b : ℝ)
              * ((Q / (a ^ 2 * b) : ℕ) : ℝ)
           else 0) := by
  simp_rw [Finset.mul_sum]
  simp_rw [Finset.sum_filter]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  refine Finset.sum_congr rfl (fun b _ => ?_)
  by_cases hc : Nat.Coprime a r
  · rw [if_pos hc, if_pos hc, Nat.mul_comm b (a ^ 2)]
    ring
  · rw [if_neg hc, if_neg hc]

/-- **The squarefree count in a coprime class, with a power-saving error.**
There is an absolute `C > 0` with, for all `Q, r ≥ 1`,
`|#{n ≤ Q : (n,r) = 1, n squarefree} − Q·(6/π²)·∏_{p | r} p/(p+1)| ≤ C·√Q·Σ_{d | r} 1/√d`.

A complete elementary route (all steps are already available in this workspace for the pieces):

1. `μ²(n) = Σ_{d² | n} μ(d)` for `n ≥ 1` (i.e. `Σ_{d ∈ n.divisors} [d² ∣ n] μ(d) = μ(n)²`; note
   Mathlib's `ArithmeticFunction.moebius_sq : μ n ^ 2 = if Squarefree n then 1 else 0`).
2. Swap sums: `Σ_{n ≤ Q, (n,r)=1} μ²(n) = Σ_{d ≤ √Q, (d,r)=1} μ(d)·#{k ≤ Q/d² : (k,r)=1}`, and
   `#{k ≤ M : (k,r)=1} = Σ_{b | r, b squarefree} μ(b)·⌊M/b⌋`
   (Mathlib: this is Möbius inversion over the divisors of `r`).
3. Write `⌊x⌋ = x − {x}` and extend the `d`-sum to all `d ≥ 1` (terms with `d² > Q` vanish):
   `S = Q·(Σ'_{d, (d,r)=1} μ(d)/d²)·(Σ_{b | r, b squarefree} μ(b)/b) − (fractional parts)` with
   `|fractional parts| ≤ Σ_{b | r, b squarefree} Σ_d min(1, Q/(d²b)) ≤ 3√Q·Σ_{b | r} 1/√b`.
4. Evaluate: `Σ'_{(d,r)=1} μ(d)/d² = (6/π²)·∏_{p | r}(1 − p⁻²)⁻¹` — *already proved* in this
   workspace as `Work.LinnikAreas.Density4.moebius_coprime_recip_sq_tsum`
   (`Submission/Work/LinnikAreas/Density4/moebius_coprime_recip_sq_tsum.lean`, sorry-free) —
   and `Σ_{b | r, b squarefree} μ(b)/b = ∏_{p | r}(1 − 1/p)` (use
   `Commons.Algebra.BigOperators.prod_primeFactors_one_add_eq_sum_divisors` or
   `ArithmeticFunction.IsMultiplicative.prodPrimeFactors_one_sub_of_squarefree`). Then
   `(1 - p⁻²)⁻¹(1 - 1/p) = p/(p+1)`.

Please keep the proof independent of the files
`Submission/Work/LinnikAreas/Density4/sqfree_coprime_double_sum.lean`,
`Submission/Work/LinnikAreas/Density4/squarefree_coprime_count.lean` and
`Submission/Work/BzHard/squarefree_coprime_count.lean` (they currently contain `sorry`s, so
importing a *declaration* from them would taint your proof; verify with `#print axioms`). -/
theorem sqfree_coprime_count_main :
    ∃ C : ℝ, 0 < C ∧ ∀ (Q r : ℕ), 1 ≤ Q → 1 ≤ r →
      |(∑ n ∈ (Finset.Icc 1 Q).filter (fun n => Nat.Coprime n r),
          (((ArithmeticFunction.moebius n : ℤ) : ℝ)) ^ 2)
        - (Q : ℝ) * (∏ p ∈ r.primeFactors, (p : ℝ) / ((p : ℝ) + 1)) / (Real.pi ^ 2 / 6)|
        ≤ C * Real.sqrt (Q : ℝ) * (∑ d ∈ r.divisors, 1 / Real.sqrt (d : ℝ)) := by
  refine ⟨4, by norm_num, ?_⟩
  intro Q r hQ hr
  -- Replace the weight `μ(n)²` by the squarefree indicator and absorb the coprimality filter.
  simp_rw [moebius_sq_eq_indicator]
  rw [← Finset.sum_filter, Finset.filter_filter]
  -- Exact Möbius rearrangement of the count into a double sum.
  rw [Work.LinnikAreas.Density4.sqfree_moebius_double_sum Q r hr]
  -- Put the double sum into the shape used by the error estimate.
  rw [sqfree_double_sum_reindex Q r hr]
  -- Identify the "main term" with `Q · (∏_{p | r} p/(p+1)) / (π²/6)`.
  have hmain : (Q : ℝ) * (∏ p ∈ r.primeFactors, (p : ℝ) / ((p : ℝ) + 1))
        / (Real.pi ^ 2 / 6)
      = (Q : ℝ) * ((∑' a : ℕ,
            if Nat.Coprime a r then (ArithmeticFunction.moebius a : ℝ) / (a : ℝ) ^ 2 else 0)
          * (∑ b ∈ r.divisors, (ArithmeticFunction.moebius b : ℝ) / (b : ℝ))) := by
    rw [mul_div_assoc, main_term_eq r hr]
  rw [hmain]
  exact Work.LinnikAreas.Density4.double_sum_error_bound Q r hQ hr

end Work.LinnikAreas.Density4.BzS3
