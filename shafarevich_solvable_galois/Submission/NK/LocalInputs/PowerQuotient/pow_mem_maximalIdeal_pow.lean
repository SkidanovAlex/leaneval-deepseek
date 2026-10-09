import Mathlib
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.unusedVariables false

namespace NK.LocalInputs.PowerQuotient

/-- **The binomial/geometric-sum bound for `(1 + x)^p - 1`.**

In any commutative ring `R` with an ideal `I`, if `p ∈ I ^ e` and `a - 1 ∈ I ^ n` — so that
`a = 1 + x` with `x ∈ I ^ n` and `p ≡ 0` modulo `I ^ e` — then

  `a ^ p - 1 ∈ I ^ min (n + e) (2 * n)`.

Indeed `a ^ p - 1 = (a - 1) * S` with `S = ∑_{i < p} a ^ i`; each `a ^ i - 1 = (a - 1) * (…)`
lies in `I ^ n`, so `S = p + (S - p)` with `S - p ∈ I ^ n`, and hence

  `a ^ p - 1 = (a - 1) * p + (a - 1) * (S - p) ∈ I ^ (n + e) + I ^ (2 * n) ⊆ I ^ min (n + e) (2 * n)`. -/
private lemma pow_sub_one_mem_pow {R : Type*} [CommRing R] (I : Ideal R) {e p n : ℕ}
    (hpe : (p : R) ∈ I ^ e) (a : R) (ha : a - 1 ∈ I ^ n) :
    a ^ p - 1 ∈ I ^ min (n + e) (2 * n) := by
  -- `S = ∑ i < p, a ^ i` differs from `p` by an element of `I ^ n`.
  have hS : (∑ i ∈ Finset.range p, a ^ i) - (p : R) ∈ I ^ n := by
    have hsum : (∑ i ∈ Finset.range p, a ^ i) - (p : R)
        = ∑ i ∈ Finset.range p, (a ^ i - 1) := by
      rw [Finset.sum_sub_distrib]
      congr 1
      simp [Finset.sum_const, nsmul_eq_mul]
    rw [hsum]
    refine Ideal.sum_mem _ (fun i _ => ?_)
    rw [← mul_geom_sum a i]
    exact Ideal.mul_mem_right _ (I ^ n) ha
  -- The two summands of the geometric-sum decomposition.
  have h1 : (a - 1) * (p : R) ∈ I ^ min (n + e) (2 * n) :=
    Ideal.pow_le_pow_right (min_le_left _ _) (by
      have := Ideal.mul_mem_mul ha hpe
      rwa [← pow_add] at this)
  have h2 : (a - 1) * ((∑ i ∈ Finset.range p, a ^ i) - (p : R)) ∈
      I ^ min (n + e) (2 * n) :=
    Ideal.pow_le_pow_right (min_le_right _ _) (by
      have := Ideal.mul_mem_mul ha hS
      rw [← pow_add] at this
      rwa [show n + n = 2 * n from by ring] at this)
  have hfin : (a - 1) * (p : R) +
      (a - 1) * ((∑ i ∈ Finset.range p, a ^ i) - (p : R)) ∈
      I ^ min (n + e) (2 * n) :=
    Ideal.add_mem _ h1 h2
  have hkey : (a - 1) * (p : R) + (a - 1) * ((∑ i ∈ Finset.range p, a ^ i) - (p : R))
      = a ^ p - 1 := by
    rw [← mul_add, add_sub_cancel, mul_geom_sum]
  rwa [hkey] at hfin

theorem pow_mem_maximalIdeal_pow {K : Type*} [Field K] [NumberField K]
    (𝔭 : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers K)) {p : ℕ} (hp : p.Prime)
    (hpe : ((p : ℕ) : 𝔭.adicCompletionIntegers K) ∈
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) ^ (𝔭.asIdeal.ramificationIdx ℤ))
    {n : ℕ} (hn : 1 ≤ n) {u : (𝔭.adicCompletionIntegers K)ˣ}
    (hu : ((u : 𝔭.adicCompletionIntegers K) - 1) ∈
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) ^ n) :
    ((u ^ p : (𝔭.adicCompletionIntegers K)ˣ) : 𝔭.adicCompletionIntegers K) - 1 ∈
      (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K)) ^
        (min (n + 𝔭.asIdeal.ramificationIdx ℤ) (2 * n)) := by
  have h := pow_sub_one_mem_pow (R := 𝔭.adicCompletionIntegers K)
    (IsLocalRing.maximalIdeal (𝔭.adicCompletionIntegers K))
    (e := 𝔭.asIdeal.ramificationIdx ℤ) (p := p) (n := n) hpe
    (u : 𝔭.adicCompletionIntegers K) hu
  simpa only [Units.val_pow_eq_pow_val] using h

end NK.LocalInputs.PowerQuotient
