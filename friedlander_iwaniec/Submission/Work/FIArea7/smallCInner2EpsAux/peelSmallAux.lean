/-
# `peelSmallAux` — vocabulary and elementary facts for the peeled *small* part of the
inner `ℓ`-sum of *FI* §25.

This file defines the two ranges of the peeled linear part (`q ≤ z`, `p > z` prime), the
exceptional-prime range, and records the elementary arithmetic identities of the summand
(`μ(pq) = -μ(q)`, multiplicativity of the sieve indicator and of the coprimality indicator,
`ν(pq,z) = 1` for `q ≤ z`).
-/
import Mathlib
import Submission.Work.FIArea7.smallCInner2EpsAux.defs
import Submission.Work.FIArea7.primeSumPsi

set_option autoImplicit false

namespace Work.FIArea7.smallCInner2EpsAux

open Finset
open scoped BigOperators

attribute [local instance] Classical.propDecidable

noncomputable section

/-! ## 1. The ranges -/

/-- The outer range of the peeled linear part: `1 ≤ q ≤ u`, `q ≤ z`. -/
def pOuterRange (u z : ℕ) : Finset ℕ := (Finset.Icc 1 u).filter (fun q => q ≤ z)

/-- The prime variable of the peeled linear part: the primes `p` with `z < p ≤ u`. -/
def pPrimeSet (u z : ℕ) : Finset ℕ := (Finset.Icc 1 u).filter (fun p => p.Prime ∧ z < p)

/-- The exceptional primes: the prime divisors of `c·q` that are `≤ u/q`. -/
def pExcSet (c u q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (u / q)).filter (fun p => p.Prime ∧ p ∣ c * q)

/-- The range of the shifted prime-sum estimate: primes `p ≤ u/q` with `p > max z Pz`. -/
def pRangeSet (u z Pz q : ℕ) : Finset ℕ :=
  (Finset.Icc 1 (u / q)).filter (fun p => p.Prime ∧ max z Pz < p)

/-! ## 2. Elementary facts -/

/-- For a prime `p` the sieve indicator `nspInd Pa p` is the threshold indicator of `Pz < p`. -/
lemma nspInd_prime (Pa : Work.FITop.Params) {p : ℕ} (hp : p.Prime) :
    Work.FIArea7.nspInd Pa p = if Pa.Pz < p then (1 : ℂ) else 0 := by
  unfold Work.FIArea7.nspInd Work.FIArea7.NoSmallPrimesNat
  by_cases h : Pa.Pz < p
  · rw [if_pos h, if_pos]
    intro q hq hqPz hqvd
    have hqp : p = q := (hp.dvd_iff_eq hq.ne_one).mp hqvd
    omega
  · rw [if_neg h, if_neg]
    intro hcon
    exact (hcon p hp (not_lt.mp h)) (dvd_refl p)

/-- `μ(pq) = -μ(q)` for a prime `p` coprime to `q`. -/
lemma moebius_prime_mul_of_coprime {p q : ℕ} (hp : p.Prime) (hcop : Nat.Coprime p q) :
    ((ArithmeticFunction.moebius (p * q) : ℤ) : ℂ)
      = -((ArithmeticFunction.moebius q : ℤ) : ℂ) := by
  have h := ArithmeticFunction.isMultiplicative_moebius.map_mul_of_coprime hcop.gcd_eq_one
  rw [h, ArithmeticFunction.moebius_apply_prime hp]
  push_cast
  ring

/-- The coprimality indicator is multiplicative in the second argument. -/
lemma coprimeInd_mul (c p q : ℕ) :
    (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
      = (if Nat.Coprime c p then (1 : ℂ) else 0)
        * (if Nat.Coprime c q then (1 : ℂ) else 0) := by
  by_cases h : Nat.Coprime c (p * q)
  · have hp : Nat.Coprime c p := (Nat.coprime_mul_iff_right.mp h).1
    have hq : Nat.Coprime c q := (Nat.coprime_mul_iff_right.mp h).2
    rw [if_pos h, if_pos hp, if_pos hq]
    norm_num
  · rw [if_neg h]
    have h' : ¬ (Nat.Coprime c p ∧ Nat.Coprime c q) :=
      fun hh => h (Nat.coprime_mul_iff_right.mpr hh)
    rcases not_and_or.mp h' with hp | hq
    · rw [if_neg hp]; ring
    · rw [if_neg hq]; ring

/-- For `q ≤ z` and a prime `p > z` with `pq` squarefree and `pq ≤ u`, the number of prime
factors `> z` of `pq` below `u` is one (namely `p`). -/
lemma largePrimeCount_eq_one {u z p q : ℕ} (hp : p.Prime) (hzp : z < p) (hpq : p * q ≤ u)
    (hzq : q ≤ z) (hsq : Squarefree (p * q)) :
    Work.FIArea7.largePrimeCount u z (p * q) = 1 := by
  have hsq0 : p * q ≠ 0 := hsq.ne_zero
  have hq0 : q ≠ 0 := by
    rintro rfl
    simp at hsq0
  have hset : (Finset.Icc 1 u).filter (fun r => r.Prime ∧ z < r ∧ r ∣ p * q) = {p} := by
    ext r
    simp only [Finset.mem_filter, Finset.mem_singleton, Finset.mem_Icc]
    constructor
    · rintro ⟨-, hrp, hzr, hrdvd⟩
      rcases hrp.dvd_mul.mp hrdvd with h | h
      · exact (Nat.prime_dvd_prime_iff_eq hrp hp).mp h
      · have hle : r ≤ q := Nat.le_of_dvd (Nat.pos_of_ne_zero hq0) h
        omega
    · intro hr
      rw [hr]
      exact ⟨⟨hp.one_le, le_trans (Nat.le_mul_of_pos_right p (Nat.pos_of_ne_zero hq0)) hpq⟩,
        hp, hzp, dvd_mul_right p q⟩
  unfold Work.FIArea7.largePrimeCount
  rw [hset, Finset.card_singleton]


/-- `μ(pq) = 0` for a prime `p` dividing `q` (then `p² ∣ pq`). -/
lemma moebius_prime_mul_of_dvd {p q : ℕ} (hp : p.Prime) (h : p ∣ q) :
    ArithmeticFunction.moebius (p * q) = 0 := by
  apply ArithmeticFunction.moebius_eq_zero_of_not_squarefree
  intro hs
  have h2 : ¬ p * p ∣ p * q := (Nat.squarefree_iff_prime_squarefree.mp hs) p hp
  exact h2 (by obtain ⟨m, rfl⟩ := h; exact ⟨m, by ring⟩)

/-- **The coefficient of the peeled summand on the support.**  For a prime `p > Pz` with
`p ∤ cq` one has `μ(pq)·nspInd(pq)·1[(c,pq)=1] = -μ(q)·nspInd(q)·1[(c,q)=1]`. -/
lemma peelFactor_eq {c q p : ℕ} {Pa : Work.FITop.Params}
    (hp : p.Prime) (hPz : Pa.Pz < p) (hnd : ¬ p ∣ c * q) :
    (ArithmeticFunction.moebius (p * q) : ℂ) * Work.FIArea7.nspInd Pa (p * q)
        * (if Nat.Coprime c (p * q) then (1 : ℂ) else 0)
      = -((ArithmeticFunction.moebius q : ℤ) : ℂ) * Work.FIArea7.nspInd Pa q
          * (if Nat.Coprime c q then (1 : ℂ) else 0) := by
  have hpq : Nat.Coprime p q :=
    (hp.coprime_iff_not_dvd).mpr (fun h => hnd (Dvd.dvd.mul_left h c))
  have hpc : ¬ p ∣ c := fun h => hnd (Dvd.dvd.mul_right h q)
  have hcp : Nat.Coprime c p := ((hp.coprime_iff_not_dvd).mpr hpc).symm
  rw [coprimeInd_mul c p q, if_pos hcp, one_mul,
    Work.FIArea7.nspInd_mul Pa hpq, nspInd_prime Pa hp, if_pos hPz, one_mul,
    moebius_prime_mul_of_coprime hp hpq]

end

end Work.FIArea7.smallCInner2EpsAux
