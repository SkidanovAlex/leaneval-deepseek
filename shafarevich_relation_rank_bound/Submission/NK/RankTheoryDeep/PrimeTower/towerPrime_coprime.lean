import Mathlib
import Submission.NK.RankTheoryDeep.PrimeTower.Defs

/-!
# The tower primes are pairwise coprime

`towerPrime ℓ n = (towerNum ℓ (n + 1)).minFac`, where
`towerNum ℓ k = ∑_{i < ℓ} ℓ ^ (i * ℓ ^ (k - 1))` (see
`Submission/Work/RankTheoryDeep/PrimeTower/Defs.lean`).  We show that the primes `towerPrime ℓ n`
for distinct `n` are coprime, so that the moduli `towerMod ℓ N` are squarefree products of
distinct primes.

The mathematical content is the pairwise coprimality of the numbers `towerNum ℓ k` for `k ≥ 1`.
For `k ≥ 1` the number `towerNum ℓ k` is the geometric sum `∑_{i < ℓ} Bₖ ^ i` with
`Bₖ = ℓ ^ (ℓ ^ (k - 1))`, and `B_{k+1} = Bₖ ^ ℓ`.  So `towerNum ℓ k = Φ_ℓ(Bₖ)` where
`Φ_ℓ(X) = 1 + X + ⋯ + X ^ (ℓ - 1)` is the `ℓ`-th cyclotomic polynomial, and
`towerNum ℓ j = Φ_ℓ(Bᵢ ^ (ℓ ^ (j - i)))` for `j > i`.

Suppose a prime `p` divides both `towerNum ℓ a` and `towerNum ℓ b`, `1 ≤ a < b`.  Reducing
modulo `p`, the base `B = Bₐ` satisfies `∑_{i < ℓ} B ^ i = 0`, hence
`B ^ ℓ = 1` (multiply by `B - 1`).  Since `ℓ ∣ ℓ ^ (b - a)` this gives
`B ^ (ℓ ^ (b - a)) = 1`, so the second sum `∑_{i < ℓ} (B ^ (ℓ ^ (b - a))) ^ i` equals `ℓ` in
`ZMod p`; but it also vanishes because `p` divides `towerNum ℓ b`.  Hence `p ∣ ℓ`, so `p = ℓ`,
which contradicts `ℓ ∤ towerNum ℓ a` (`not_dvd_towerNum`).

Note that this argument never uses that `p` is the *least* prime factor: it shows directly that
the numbers `towerNum ℓ k` for `k ≥ 1` are pairwise coprime.
-/

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

namespace NK.RankTheoryDeep.PrimeTower

/-- **The base of the geometric sum defining `towerNum ℓ k`, reduced into `ZMod p`**:
`ℓ ^ (ℓ ^ (k - 1))`, so that `(towerNum ℓ k : ZMod p) = ∑_{i < ℓ} (towerBase ℓ p k) ^ i`. -/
def towerBase (ℓ p k : ℕ) : ZMod p := (ℓ : ZMod p) ^ (ℓ ^ (k - 1))

theorem towerBase_zero (ℓ p : ℕ) : towerBase ℓ p 0 = (ℓ : ZMod p) := by
  simp [towerBase]

theorem towerBase_succ (ℓ p : ℕ) {k : ℕ} (hk : 1 ≤ k) :
    towerBase ℓ p (k + 1) = (towerBase ℓ p k) ^ ℓ := by
  have hk' : k + 1 - 1 = k - 1 + 1 := by omega
  rw [towerBase, towerBase, ← pow_mul, hk', pow_succ]

/-- **`towerNum ℓ k` is the geometric sum of ratio `towerBase ℓ p k`, reduced into `ZMod p`.** -/
theorem towerNum_cast_eq_sum (ℓ p k : ℕ) :
    ((towerNum ℓ k : ℕ) : ZMod p) = ∑ i ∈ Finset.range ℓ, (towerBase ℓ p k) ^ i := by
  rw [towerNum, Nat.cast_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Nat.cast_pow, towerBase, mul_comm, pow_mul]

/-- **The bases are iterated `ℓ`-th powers of each other.** -/
theorem towerBase_pow (ℓ p : ℕ) {a b : ℕ} (ha : 1 ≤ a) (hab : a ≤ b) :
    (towerBase ℓ p a) ^ (ℓ ^ (b - a)) = towerBase ℓ p b := by
  have hexp : ℓ ^ (a - 1) * ℓ ^ (b - a) = ℓ ^ (b - 1) := by
    rw [← pow_add]
    congr 1
    omega
  rw [towerBase, towerBase, ← pow_mul, hexp]

/-- **The key local statement.**  If a prime `p` divides both `towerNum ℓ a` and `towerNum ℓ b`
with `1 ≤ a < b`, then `p = ℓ`, contradicting `ℓ ∤ towerNum ℓ a`. -/
theorem not_prime_dvd_both (ℓ : ℕ) [Fact ℓ.Prime] {a b : ℕ} (ha : 1 ≤ a) (hab : a < b)
    {p : ℕ} (hp : p.Prime) (hpa : p ∣ towerNum ℓ a) (hpb : p ∣ towerNum ℓ b) : False := by
  have hℓ : ℓ.Prime := Fact.out
  -- the reduction of `towerNum ℓ a` modulo `p` vanishes
  have hsum_a : (∑ i ∈ Finset.range ℓ, (towerBase ℓ p a) ^ i : ZMod p) = 0 := by
    rw [← towerNum_cast_eq_sum ℓ p a]
    exact (CharP.cast_eq_zero_iff (ZMod p) p (towerNum ℓ a)).mpr hpa
  -- multiplying by `B - 1` exhibits `towerNum ℓ a ≡ 0` as `B ^ ℓ = 1`
  have hBℓ : (towerBase ℓ p a) ^ ℓ = 1 := by
    have h := geom_sum_mul (towerBase ℓ p a) ℓ
    rw [hsum_a, zero_mul] at h
    exact sub_eq_zero.mp h.symm
  -- hence the corresponding base for `b` is `1`
  have hone : (towerBase ℓ p a) ^ (ℓ ^ (b - a)) = 1 := by
    obtain ⟨t, ht⟩ : ∃ t, b - a = t + 1 := ⟨b - a - 1, by omega⟩
    rw [ht, pow_succ' ℓ t, pow_mul, hBℓ, one_pow]
  -- the reduction of `towerNum ℓ b` modulo `p` vanishes,
  have hsum_b_zero : (∑ i ∈ Finset.range ℓ, (towerBase ℓ p b) ^ i : ZMod p) = 0 := by
    rw [← towerNum_cast_eq_sum ℓ p b]
    exact (CharP.cast_eq_zero_iff (ZMod p) p (towerNum ℓ b)).mpr hpb
  -- but it also equals `ℓ`
  have hsum_b_ell : (∑ i ∈ Finset.range ℓ, (towerBase ℓ p b) ^ i : ZMod p) = (ℓ : ZMod p) := by
    rw [← towerBase_pow ℓ p ha (le_of_lt hab)]
    rw [Finset.sum_congr rfl fun i _ => by rw [hone, one_pow]]
    simp
  -- so `ℓ = 0` in `ZMod p`, i.e. `p = ℓ`, contradicting `ℓ ∤ towerNum ℓ a`
  have hell : ((ℓ : ℕ) : ZMod p) = 0 := by rw [← hsum_b_ell, hsum_b_zero]
  have hpℓ : p ∣ ℓ := (CharP.cast_eq_zero_iff (ZMod p) p ℓ).mp hell
  have hpeq : p = ℓ := (Nat.prime_dvd_prime_iff_eq hp hℓ).mp hpℓ
  exact not_dvd_towerNum ℓ a (hpeq ▸ hpa)

/-- **The values `towerNum ℓ k` for `k ≥ 1` are pairwise coprime.** -/
theorem towerNum_coprime_of_lt (ℓ : ℕ) [Fact ℓ.Prime] {a b : ℕ} (ha : 1 ≤ a) (hab : a < b) :
    Nat.Coprime (towerNum ℓ a) (towerNum ℓ b) := by
  rw [Nat.coprime_iff_gcd_eq_one]
  by_contra hg
  obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg
  exact not_prime_dvd_both ℓ ha hab hp (dvd_trans hpd (Nat.gcd_dvd_left _ _))
    (dvd_trans hpd (Nat.gcd_dvd_right _ _))

-- towerPrime ℓ n = (towerNum ℓ (n + 1)).minFac, in Submission/Work/RankTheoryDeep/PrimeTower/Defs.lean
theorem towerPrime_coprime (ℓ : ℕ) [Fact ℓ.Prime] {i j : ℕ} (h : i ≠ j) :
    Nat.Coprime (towerPrime ℓ i) (towerPrime ℓ j) := by
  -- the two tower numbers `towerNum ℓ (i + 1)`, `towerNum ℓ (j + 1)` are coprime
  have hcop : Nat.Coprime (towerNum ℓ (i + 1)) (towerNum ℓ (j + 1)) := by
    rcases Nat.lt_or_gt_of_ne h with hij | hji
    · exact towerNum_coprime_of_lt ℓ (a := i + 1) (b := j + 1) (by omega) (by omega)
    · exact (towerNum_coprime_of_lt ℓ (a := j + 1) (b := i + 1) (by omega) (by omega)).symm
  rw [Nat.coprime_iff_gcd_eq_one] at hcop ⊢
  -- `gcd pᵢ pⱼ` divides both tower numbers, hence divides their `gcd`, which is `1`
  have hdvd : Nat.gcd (towerPrime ℓ i) (towerPrime ℓ j)
      ∣ Nat.gcd (towerNum ℓ (i + 1)) (towerNum ℓ (j + 1)) :=
    Nat.dvd_gcd (dvd_trans (Nat.gcd_dvd_left _ _) (towerPrime_dvd ℓ i))
      (dvd_trans (Nat.gcd_dvd_right _ _) (towerPrime_dvd ℓ j))
  rw [hcop] at hdvd
  exact Nat.dvd_one.mp hdvd

end NK.RankTheoryDeep.PrimeTower
