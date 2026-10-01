import Mathlib
import Submission.Work.ZeroDensity.Jutila.KappaMertensDefs

namespace Work.ZeroDensity.Jutila

open Finset

noncomputable section

/-!
# The divisor-sum identity `KMKappaGSum`

For squarefree `t`,

`Σ_{e | t} κ(e)⁻¹ · σ_{-1/2}(e) · ∏_{p | e} (p+1)/(√p+1) = σ_{-1/2}(t)`.

The point is that every summand collapses to `e^{-1/2}`: writing the squarefree `e` as the product
of its prime factors,

* `κ(e) = ∏_{p|e} (p+1)`,
* `σ_{-1/2}(e) = ∏_{p|e} (1 + p^{-1/2})` (multiplicativity of the divisor sum),
* `∏_{p|e} (p+1)/(√p+1)` is already a product over `e.primeFactors`,

and `(1 + p^{-1/2}) = (√p+1)/√p`, so that the single-prime factors telescope:
`(p+1)⁻¹ · (1 + 1/√p) · (p+1)/(√p+1) = 1/√p`. Hence the whole summand is
`∏_{p|e} p^{-1/2} = e^{-1/2}`, and the sum over the divisors of `t` is `σ_{-1/2}(t)`.
-/

/-- `σ_{-1/2}` packaged as an arithmetic function; the value at `0` is the empty sum `0`. -/
def sigHalfAF : ArithmeticFunction ℝ := ⟨sigHalf, by simp [sigHalf, Nat.divisors_zero]⟩

lemma sigHalfAF_apply (n : ℕ) : sigHalfAF n = sigHalf n := rfl

/-- `σ_{-1/2}` is multiplicative: for coprime `m`, `n`,
`σ_{-1/2}(mn) = σ_{-1/2}(m)·σ_{-1/2}(n)`.

When `m` and `n` are coprime, `(d₁,d₂) ↦ d₁d₂` is a bijection
`m.divisors ×ˢ n.divisors → (mn).divisors` and `d ↦ d^{-1/2}` is multiplicative. -/
lemma sigHalf_mul_of_coprime {m n : ℕ} (h : Nat.Coprime m n) :
    sigHalf (m * n) = sigHalf m * sigHalf n := by
  have key : ∀ d1 ∈ m.divisors, ∀ d2 ∈ n.divisors,
      (1:ℝ) / Real.sqrt ((d1 * d2 : ℕ) : ℝ)
        = (1 / Real.sqrt (d1:ℝ)) * (1 / Real.sqrt (d2:ℝ)) := by
    intro d1 h1 d2 h2
    have hd1 : (0:ℝ) < (d1:ℝ) := by exact_mod_cast Nat.pos_of_mem_divisors h1
    rw [Nat.cast_mul, Real.sqrt_mul (le_of_lt hd1), div_mul_div_comm, mul_one]
  have hdiv : (m * n).divisors
      = Finset.image (fun p : ℕ × ℕ => p.1 * p.2) (m.divisors ×ˢ n.divisors) := by
    rw [Nat.divisors_mul, Finset.mul_def]
  unfold sigHalf
  rw [hdiv, Finset.sum_image (h.mul_injOn_divisors), Finset.sum_product]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl; intro d1 h1
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl; intro d2 h2
  exact key d1 h1 d2 h2

lemma sigHalfAF_isMultiplicative : ArithmeticFunction.IsMultiplicative sigHalfAF := by
  refine ⟨?_, ?_⟩
  · show sigHalf 1 = 1
    exact sigHalf_one
  · intro m n h
    show sigHalf (m * n) = sigHalf m * sigHalf n
    exact sigHalf_mul_of_coprime h

/-- For a prime `p`, `σ_{-1/2}(p) = 1 + p^{-1/2}` (its divisors are `1` and `p`). -/
lemma sigHalf_prime {p : ℕ} (hp : p.Prime) :
    sigHalf p = 1 + 1 / Real.sqrt (p : ℝ) := by
  rw [sigHalf, hp.divisors,
    Finset.sum_insert (by rw [Finset.mem_singleton]; exact hp.ne_one.symm),
    Finset.sum_singleton]
  simp

/-- For squarefree `e`, `σ_{-1/2}(e) = ∏_{p | e} (1 + p^{-1/2})`. -/
lemma sigHalf_eq_prod_primeFactors {e : ℕ} (he : Squarefree e) :
    sigHalf e = ∏ p ∈ e.primeFactors, (1 + 1 / Real.sqrt (p : ℝ)) := by
  have h := ArithmeticFunction.IsMultiplicative.prod_primeFactors sigHalfAF_isMultiplicative he
  show sigHalfAF e = ∏ p ∈ e.primeFactors, (1 + 1 / Real.sqrt (p : ℝ))
  rw [← h]
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact sigHalf_prime (Nat.prime_of_mem_primeFactors hp)

/-- For squarefree `e`, `∏_{p | e} p^{-1/2} = e^{-1/2}`. -/
lemma prod_inv_sqrt_primeFactors {e : ℕ} (he : Squarefree e) :
    ∏ p ∈ e.primeFactors, 1 / Real.sqrt (p : ℝ) = 1 / Real.sqrt (e : ℝ) := by
  have hs : ∏ p ∈ e.primeFactors, Real.sqrt (p : ℝ) = Real.sqrt (e : ℝ) := by
    rw [← Real.sqrt_prod e.primeFactors (fun p _ => by positivity)]
    congr 1
    rw [← Nat.cast_prod]
    exact_mod_cast Nat.prod_primeFactors_of_squarefree he
  simp only [one_div]
  rw [Finset.prod_inv_distrib, hs]

/-- The single-prime telescoping identity
`(p+1)⁻¹ · (1 + p^{-1/2}) · (p+1)/(√p+1) = p^{-1/2}`. -/
lemma kmTerm_eq {p : ℕ} (hp : p.Prime) :
    ((p : ℝ) + 1)⁻¹ * (1 + 1 / Real.sqrt (p : ℝ))
        * (((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1))
      = 1 / Real.sqrt (p : ℝ) := by
  have hpR : (0 : ℝ) < (p : ℝ) := by
    have := hp.two_le
    exact_mod_cast (by omega : 0 < p)
  have h1 : ((p : ℝ) + 1) ≠ 0 := by positivity
  have h2 : Real.sqrt (p : ℝ) + 1 ≠ 0 := by positivity
  field_simp

/-- For squarefree `e` the summand of `KMKappaGSum` equals `e^{-1/2}`. -/
lemma kappa_sigHalf_prod_eq {e : ℕ} (he : Squarefree e) :
    (kappa e)⁻¹ * sigHalf e
        * (∏ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1))
      = 1 / Real.sqrt (e : ℝ) := by
  have hk : kappa e = ∏ p ∈ e.primeFactors, ((p : ℝ) + 1) := by
    rw [kappa_eq_kap_of_squarefree he]; rfl
  rw [hk, sigHalf_eq_prod_primeFactors he]
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  rw [← prod_inv_sqrt_primeFactors he]
  refine Finset.prod_congr rfl ?_
  intro p hp
  exact kmTerm_eq (Nat.prime_of_mem_primeFactors hp)

theorem KMKappaGSum (t : ℕ) (ht : Squarefree t) :
    ∑ e ∈ t.divisors,
        (kappa e)⁻¹ * sigHalf e
          * (∏ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1))
      = sigHalf t := by
  have hgoal : ∑ e ∈ t.divisors,
        (kappa e)⁻¹ * sigHalf e
          * (∏ p ∈ e.primeFactors, ((p : ℝ) + 1) / (Real.sqrt (p : ℝ) + 1))
      = ∑ e ∈ t.divisors, 1 / Real.sqrt (e : ℝ) := by
    refine Finset.sum_congr rfl ?_
    intro e he
    exact kappa_sigHalf_prod_eq (ht.squarefree_of_dvd (Nat.dvd_of_mem_divisors he))
  rw [hgoal]
  rfl

end

end Work.ZeroDensity.Jutila
