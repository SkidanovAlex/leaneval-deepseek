import Mathlib
import Submission.Work.LinnikBurgess.burgess_lead_defs

/-!
# The Chinese-remainder step for the double-critical predicate

`BURGESS_ROUTE_LEAD.md` §4.1: the double-critical predicate `DLd` is "local at every prime", i.e.
if `DLp p (s p) a b` holds at every prime `p` of a finite set `P` of primes, then the (independent)
witnesses `y_p` can be combined by the Chinese remainder theorem into a single `y` witnessing
`DLd (∏ p ∈ P, p ^ s p) a b`.

The three ingredients are

* `crt_primePowers` — the Chinese remainder theorem for the prime-power moduli `p ^ s p`;
* `dvd_eval_of_modEq` — polynomial values at congruent arguments are congruent;
* `prod_primePowers_dvd` — divisibility by pairwise coprime prime powers multiplies.

The remaining bookkeeping (a prime of `∏ p ∈ P, p ^ s p` lies in `P`, and the exponents with `s p = 0`
contribute the factor `1`) is handled in `mem_of_mem_primeFactors_prod_primePowers` and in the main
proof.
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

open Polynomial

/-- Evaluating a polynomial with integer coefficients at congruent arguments gives congruent values:
if `Y ≡ c [MOD m]` and `m ∣ Q.eval c` then `m ∣ Q.eval Y`. -/
theorem dvd_eval_of_modEq {m c Y : ℕ} (Q : Polynomial ℤ) (h : Y ≡ c [MOD m])
    (hc : (m : ℤ) ∣ Q.eval (c : ℤ)) : (m : ℤ) ∣ Q.eval (Y : ℤ) := by
  have h1 : (m : ℤ) ∣ (Y : ℤ) - (c : ℤ) := by
    have h2 := h.dvd
    simpa [neg_sub] using (dvd_neg.mpr h2)
  have h4 : (m : ℤ) ∣ Q.eval (Y : ℤ) - Q.eval (c : ℤ) :=
    dvd_trans h1 (Polynomial.sub_dvd_eval_sub (Y : ℤ) (c : ℤ) Q)
  have h5 := Int.dvd_add h4 hc
  simpa using h5

/-- Divisibility by `x + c` is invariant under `x ≡ x' [MOD n]`. -/
lemma dvd_add_iff_of_modEq {n x x' c : ℕ} (h : x ≡ x' [MOD n]) : n ∣ x + c ↔ n ∣ x' + c := by
  have h' : (x + c) % n = (x' + c) % n := h.add_right c
  rw [Nat.dvd_iff_mod_eq_zero, Nat.dvd_iff_mod_eq_zero, h']

/-- The predicate `UnitAt p · a b` (no `y + a l` or `y + b l` divisible by `p`) only depends on `y`
modulo `p`. -/
theorem unitAt_of_modEq {p y Y : ℕ} {a b : Fin 3 → ℕ} (hmod : Y ≡ y [MOD p]) (h : UnitAt p y a b) :
    UnitAt p Y a b := by
  intro l
  exact ⟨fun hc => (h l).1 ((dvd_add_iff_of_modEq (c := a l) hmod).mp hc),
    fun hc => (h l).2 ((dvd_add_iff_of_modEq (c := b l) hmod).mp hc)⟩

/-- The prime factors of `∏ p ∈ P, p ^ s p` are among the elements of `P` (a finite set of primes). -/
theorem mem_of_mem_primeFactors_prod_primePowers (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (s : ℕ → ℕ)
    {q : ℕ} (hq : q ∈ (∏ p ∈ P, p ^ s p).primeFactors) : q ∈ P := by
  have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
  have hqdvd : q ∣ ∏ p ∈ P, p ^ s p := Nat.dvd_of_mem_primeFactors hq
  obtain ⟨p, hpP, hqps⟩ :=
    (Prime.dvd_finsetProd_iff hqprime.prime (fun p : ℕ => p ^ s p)).mp hqdvd
  have hqp : q ∣ p := hqprime.dvd_of_dvd_pow hqps
  have hpq : q = p := (Nat.prime_dvd_prime_iff_eq hqprime (hP p hpP)).mp hqp
  rw [hpq]
  exact hpP

/-- **CRT** for prime-power moduli indexed by a finite set of primes: a single `Y` is congruent to
`c p` modulo `p ^ s p` for every prime `p ∈ P`.  (No hypothesis `s p ≠ 0` is needed: `p ^ 0 = 1`.) -/
theorem crt_primePowers (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (s c : ℕ → ℕ) :
    ∃ Y : ℕ, ∀ p ∈ P, Y ≡ c p [MOD p ^ s p] := by
  have hs : ∀ p ∈ P, p ^ s p ≠ 0 := fun p hp => pow_ne_zero _ (hP p hp).ne_zero
  have hpp : (P : Set ℕ).Pairwise (Function.onFun Nat.Coprime (fun p => p ^ s p)) := by
    intro p hp q hq hpq
    exact (Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq |>.pow (s p) (s q)
  exact ⟨(Nat.chineseRemainderOfFinset c (fun p => p ^ s p) P hs hpp).val,
    (Nat.chineseRemainderOfFinset c (fun p => p ^ s p) P hs hpp).property⟩

/-- `∏ p ∈ P, p ^ s p` divides an integer as soon as every prime power `p ^ s p` does (`P` a finite
set of primes): the prime powers are pairwise coprime. -/
theorem prod_primePowers_dvd (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (s : ℕ → ℕ) {z : ℤ}
    (hz : ∀ p ∈ P, ((p ^ s p : ℕ) : ℤ) ∣ z) :
    (((∏ p ∈ P, p ^ s p : ℕ)) : ℤ) ∣ z := by
  rw [Nat.cast_prod]
  refine Finset.prod_dvd_of_coprime ?_ ?_
  · rintro p hp q hq hpq
    show IsCoprime ((p ^ s p : ℕ) : ℤ) ((q ^ s q : ℕ) : ℤ)
    rw [Int.isCoprime_iff_nat_coprime]
    simpa using ((Nat.coprime_primes (hP p hp) (hP q hq)).mpr hpq).pow (s p) (s q)
  · intro p hp
    exact hz p hp

/-- **CRT step for the double-critical predicate** (`BURGESS_ROUTE_LEAD.md` §4.1).  If the
double-critical condition `DLp p (s p) a b` holds at every prime `p` of a finite set `P` of primes
(with its own witness `y_p`), then the witnesses can be combined by the Chinese remainder
construction into a single `y` witnessing `DLd (∏ p ∈ P, p ^ s p) a b`. -/
theorem DLd_prod_of_DLp (P : Finset ℕ) (hP : ∀ p ∈ P, p.Prime) (s : ℕ → ℕ) (a b : Fin 3 → ℕ)
    (h : ∀ p ∈ P, DLp p (s p) a b) : DLd (∏ p ∈ P, p ^ s p) a b := by
  classical
  -- pick one witness per prime `p ∈ P` (and an arbitrary value outside `P`)
  have key : ∀ p : ℕ, ∃ y : ℕ, p ∈ P → UnitAt p y a b ∧
      (((p ^ s p : ℕ) : ℤ)) ∣ (critN a b).eval (y : ℤ) ∧
      (((p ^ s p : ℕ) : ℤ)) ∣ (derivative (critN a b)).eval (y : ℤ) := by
    intro p
    by_cases hp : p ∈ P
    · exact ⟨(h p hp).choose, fun _ => (h p hp).choose_spec⟩
    · exact ⟨0, fun hcontra => absurd hcontra hp⟩
  choose y hy using key
  -- combine the witnesses modulo the prime powers `p ^ s p`
  obtain ⟨Y, hY⟩ := crt_primePowers P hP s y
  refine ⟨Y, ?_, ?_, ?_⟩
  · -- `Y` is a unit at every prime dividing `∏ p ∈ P, p ^ s p`
    intro q hq
    have hqP : q ∈ P := mem_of_mem_primeFactors_prod_primePowers P hP s hq
    have hqprime : q.Prime := Nat.prime_of_mem_primeFactors hq
    have hqdvd : q ∣ ∏ p ∈ P, p ^ s p := Nat.dvd_of_mem_primeFactors hq
    -- `s q ≠ 0`, since `q` is one of the primes occurring in the product
    have hqsplit : q ∣ q ^ s q := by
      obtain ⟨p, hpP, hqps⟩ :=
        (Prime.dvd_finsetProd_iff hqprime.prime (fun p : ℕ => p ^ s p)).mp hqdvd
      have hqp : q ∣ p := hqprime.dvd_of_dvd_pow hqps
      have hpq : q = p := (Nat.prime_dvd_prime_iff_eq hqprime (hP p hpP)).mp hqp
      rw [hpq] at hqps ⊢
      exact hqps
    have hsne : s q ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hqsplit
      exact hqprime.not_dvd_one hqsplit
    exact unitAt_of_modEq ((hY q hqP).of_dvd (dvd_pow_self q hsne)) (hy q hqP).1
  · -- `∏ p ∈ P, p ^ s p ∣ critN a b` at `Y`
    refine prod_primePowers_dvd P hP s ?_
    intro p hp
    exact dvd_eval_of_modEq (critN a b) (hY p hp) (hy p hp).2.1
  · -- and the same for the derivative of `critN a b`
    refine prod_primePowers_dvd P hP s ?_
    intro p hp
    exact dvd_eval_of_modEq (derivative (critN a b)) (hY p hp) (hy p hp).2.2

end Work.LinnikBurgess
