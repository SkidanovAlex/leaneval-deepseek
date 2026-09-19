import Mathlib
import Submission.Commons.NumberTheory.Nat.prime_dvd_finset_prod

namespace Commons.NumberTheory.Nat

open Finset
open scoped BigOperators

/-- The product of a finite set of primes is squarefree. -/
lemma squarefree_prod_of_prime {s : Finset ℕ} (hs : ∀ p ∈ s, p.Prime) :
    Squarefree (∏ p ∈ s, p) := by
  classical
  let P : Finset ℕ → Prop := fun t => (∀ p ∈ t, p.Prime) → Squarefree (∏ p ∈ t, p)
  have hP : ∀ t : Finset ℕ, P t := by
    intro t
    refine Finset.induction_on t ?_ ?_
    · intro h
      simp
    · intro a u hau ih hu
      have hpa : a.Prime := hu a (mem_insert_self a u)
      have hpu : ∀ p ∈ u, p.Prime := fun p hp => hu p (mem_insert_of_mem hp)
      have hprod : Squarefree (∏ p ∈ u, p) := ih hpu
      have hcop : a.Coprime (∏ p ∈ u, p) := by
        rw [hpa.coprime_iff_not_dvd]
        intro hadvd
        have hpf : (∏ p ∈ u, p).primeFactors = u := Nat.primeFactors_prod hpu
        have ha_mem : a ∈ (∏ p ∈ u, p).primeFactors := by
          refine hpa.mem_primeFactors hadvd ?_
          exact Finset.prod_ne_zero_iff.mpr (fun x hx => (hpu x hx).ne_zero)
        exact hau (by simpa [hpf] using ha_mem)
      rw [Finset.prod_insert hau]
      exact (Nat.squarefree_mul hcop).2 ⟨hpa.squarefree, hprod⟩
  exact hP s hs

/--
For `n ≠ 0`, the sum over squarefree divisors `d` of `n` of `∏_{p | d} f p` equals the sum over
all subsets of `n.primeFactors` of `∏_{p ∈ T} f p`.  (Squarefree divisors of `n` are in bijection
with subsets of the set of prime factors of `n` via `d ↦ d.primeFactors`.)
-/
lemma sum_squarefree_divisors_eq_sum_powerset_primeFactors {α : Type*} [CommSemiring α]
    (n : ℕ) (hn : n ≠ 0) (f : ℕ → α) :
    (∑ d ∈ n.divisors with Squarefree d, ∏ p ∈ d.primeFactors, f p) =
      ∑ T ∈ n.primeFactors.powerset, ∏ p ∈ T, f p := by
  classical
  refine Finset.sum_bij (s := n.divisors.filter Squarefree)
      (t := n.primeFactors.powerset) (f := fun d => ∏ p ∈ d.primeFactors, f p)
      (g := fun T => ∏ p ∈ T, f p) (i := fun d _ => d.primeFactors) ?hi ?hinj ?hsurj ?hval
  · intro d hd
    exact Finset.mem_powerset.mpr
      (Nat.primeFactors_mono (Nat.dvd_of_mem_divisors (Finset.mem_filter.mp hd).1) hn)
  · intro d₁ hd₁ d₂ hd₂ hmem
    have hsq₁ : Squarefree d₁ := (Finset.mem_filter.mp hd₁).2
    have hsq₂ : Squarefree d₂ := (Finset.mem_filter.mp hd₂).2
    calc
      d₁ = ∏ p ∈ d₁.primeFactors, p := (Nat.prod_primeFactors_of_squarefree hsq₁).symm
      _ = ∏ p ∈ d₂.primeFactors, p := by rw [hmem]
      _ = d₂ := Nat.prod_primeFactors_of_squarefree hsq₂
  · intro T hT
    have hTsub : T ⊆ n.primeFactors := Finset.mem_powerset.mp hT
    have hTprime : ∀ p ∈ T, p.Prime := fun p hp => Nat.prime_of_mem_primeFactors (hTsub hp)
    have hdiv : (∏ p ∈ T, p) ∣ n := by
      calc
        (∏ p ∈ T, p) ∣ ∏ p ∈ n.primeFactors, p :=
          Finset.prod_dvd_prod_of_subset T n.primeFactors (fun p => p) hTsub
        _ ∣ n := Nat.prod_primeFactors_dvd n
    refine ⟨∏ p ∈ T, p, ?_, ?_⟩
    · exact Finset.mem_filter.mpr
        ⟨Nat.mem_divisors.mpr ⟨hdiv, hn⟩, Nat.squarefree_prod_of_prime hTprime⟩
    · exact Nat.primeFactors_prod hTprime
  · intro d hd
    rfl

/--
For a positive integer `n` with no prime factor equal to `2`:

`∏_{p | n} (p - 1) / (p - 2) = ∑_{d | n} [d squarefree] ∏_{p | d} 1 / (p - 2)`
-/
theorem prod_pm1_pm2_eq_divisor_sum (n : ℕ) (hn : n ≠ 0)
    (hodd : ∀ p : ℕ, p ∈ n.primeFactors → p ≠ 2) :
    (∏ p ∈ n.primeFactors, (((p : ℚ) - 1) / ((p : ℚ) - 2))) =
      ∑ d ∈ n.divisors,
        (if Squarefree d then ∏ p ∈ d.primeFactors, (1 : ℚ) / ((p : ℚ) - 2) else 0) := by
  classical
  let φ : ℕ → ℚ := fun p => (1 : ℚ) / ((p : ℚ) - 2)
  let S : Finset ℕ := n.primeFactors
  calc
    (∏ p ∈ S, (((p : ℚ) - 1) / ((p : ℚ) - 2))) = ∏ p ∈ S, (1 + φ p) := by
      apply Finset.prod_congr rfl
      intro p hp
      have hp2q : (p : ℚ) - 2 ≠ 0 := by
        exact sub_ne_zero.mpr (by exact_mod_cast (hodd p (by simpa [S] using hp)))
      have hφ : φ p = (1 : ℚ) / ((p : ℚ) - 2) := rfl
      rw [hφ]
      field_simp [hp2q]
      ring
    _ = ∑ T ∈ S.powerset, ∏ p ∈ T, φ p := by
      simpa [S] using (Finset.prod_one_add (f := φ) n.primeFactors)
    _ = ∑ d ∈ n.divisors with Squarefree d, ∏ p ∈ d.primeFactors, φ p := by
      simpa [S] using (sum_squarefree_divisors_eq_sum_powerset_primeFactors n hn φ).symm
    _ = ∑ d ∈ n.divisors,
          (if Squarefree d then ∏ p ∈ d.primeFactors, φ p else 0) := by
      rw [Finset.sum_filter]
    _ = ∑ d ∈ n.divisors,
          (if Squarefree d then ∏ p ∈ d.primeFactors, (1 : ℚ) / ((p : ℚ) - 2) else 0) := by
      apply Finset.sum_congr rfl
      intro d hd
      by_cases hsq : Squarefree d
      · simp [φ, hsq]
      · simp [hsq]

end Commons.NumberTheory.Nat
