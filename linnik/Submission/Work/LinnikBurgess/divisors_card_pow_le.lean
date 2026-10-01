import Mathlib
import Submission.Work.LinnikBurgess.singleton_ssa_defs

/-!
# The divisor count of a divisor of `q ^ 3` against the divisor count of `q`

For `m ∣ q ^ 3` with `q ≠ 0` we have `d(m) ≤ d(q) ^ 3`, where `d` is the number of
divisors.  Indeed, writing `a_p = v_p(q)` and `b_p = v_p(m)`, divisibility gives
`b_p ≤ 3 a_p`, hence `b_p + 1 ≤ 3 a_p + 1 ≤ (a_p + 1) ^ 3`, and the claim follows by
multiplying over the primes in the support of `m` (which is contained in that of `q`).

Raising to the eighth power yields the statement used in the Linnik/Burgess assembly:
for the specific number `sqfreePart q * d * g ∣ q ^ 3` one gets
`d(sqfreePart q * d * g) ^ 8 ≤ d(q) ^ 24`.
-/

namespace Work.LinnikBurgess

open Finset

/-- The number of divisors of `n ≠ 0` is the product of `v_p(n) + 1` over the primes `p`
dividing `n`. -/
lemma card_divisors_eq_prod_factorization {n : ℕ} (hn : n ≠ 0) :
    n.divisors.card = ∏ p ∈ n.primeFactors, (n.factorization p + 1) := by
  rw [Nat.divisors_eq_map_attach_Iic_factorization_prod_pow hn, Finset.card_map,
    Finset.card_attach, Finsupp.card_Iic, Nat.support_factorization]
  exact Finset.prod_congr rfl fun p _ => Nat.card_Iic _

/-- Elementary arithmetic estimate: `3 * a + 1 ≤ (a + 1) ^ 3`. -/
lemma three_mul_add_one_le_cube (a : ℕ) : 3 * a + 1 ≤ (a + 1) ^ 3 := by
  have h1 : a ≤ a * a := by
    rcases Nat.eq_zero_or_pos a with h | h
    · simp [h]
    · simpa using Nat.mul_le_mul_left a h
  have h2 : 3 * a + 1 ≤ (a + 1) ^ 2 := by
    have hsq : (a + 1) ^ 2 = a * a + 2 * a + 1 := by ring
    rw [hsq]
    omega
  have h3 : (a + 1) ^ 2 ≤ (a + 1) ^ 3 :=
    Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le a)) (by norm_num)
  exact h2.trans h3

/-- If `m ∣ q ^ 3` and `q ≠ 0`, every prime dividing `m` divides `q`. -/
lemma primeFactors_subset_of_dvd_pow_three {m q : ℕ} (hq : 0 < q) (h : m ∣ q ^ 3) :
    m.primeFactors ⊆ q.primeFactors := by
  intro p hp
  rw [Nat.mem_primeFactors] at hp ⊢
  obtain ⟨hpp, hpm, _⟩ := hp
  exact ⟨hpp, hpp.dvd_of_dvd_pow (hpm.trans h), hq.ne'⟩

/-- Local form of the divisor-count estimate: `v_p(m) + 1 ≤ (v_p(q) + 1) ^ 3`
whenever `m ∣ q ^ 3` and `q ≠ 0`. -/
lemma factorization_add_one_le_pow_three {m q : ℕ} (hq : 0 < q) (h : m ∣ q ^ 3) (p : ℕ) :
    m.factorization p + 1 ≤ (q.factorization p + 1) ^ 3 := by
  have hq3 : q ^ 3 ≠ 0 := pow_ne_zero _ hq.ne'
  have hm : m ≠ 0 := (Nat.pos_of_dvd_of_pos h (pow_pos hq 3)).ne'
  have hle : m.factorization p ≤ 3 * q.factorization p := by
    have h1 : m.factorization ≤ (q ^ 3).factorization :=
      (Nat.factorization_le_iff_dvd hm hq3).mpr h
    have h2 := h1 p
    rw [Nat.factorization_pow] at h2
    simpa using h2
  have harith := three_mul_add_one_le_cube (q.factorization p)
  omega

/-- **Divisor-count estimate.**  If `m ∣ q ^ 3` and `q ≠ 0`, then
`d(m) ≤ d(q) ^ 3`. -/
lemma divisors_card_le_pow_three {m q : ℕ} (hq : 0 < q) (h : m ∣ q ^ 3) :
    m.divisors.card ≤ q.divisors.card ^ 3 := by
  have hm : m ≠ 0 := (Nat.pos_of_dvd_of_pos h (pow_pos hq 3)).ne'
  rw [card_divisors_eq_prod_factorization hm, card_divisors_eq_prod_factorization hq.ne']
  calc ∏ p ∈ m.primeFactors, (m.factorization p + 1)
      ≤ ∏ p ∈ m.primeFactors, (q.factorization p + 1) ^ 3 :=
        Finset.prod_le_prod₀ (fun p _ => Nat.zero_le _)
          (fun p _ => factorization_add_one_le_pow_three hq h p)
    _ = (∏ p ∈ m.primeFactors, (q.factorization p + 1)) ^ 3 :=
        Finset.prod_pow _ 3 _
    _ ≤ (∏ p ∈ q.primeFactors, (q.factorization p + 1)) ^ 3 := by
        refine Nat.pow_le_pow_left (Finset.prod_le_prod_of_subset_of_one_le₀
          (primeFactors_subset_of_dvd_pow_three hq h)
          (fun p _ => Nat.zero_le _) (fun p _ _ => by omega)) 3

theorem divisors_card_pow_le {q d g : ℕ} (hq : 0 < q) (h : sqfreePart q * d * g ∣ q ^ 3) :
    ((sqfreePart q * d * g).divisors.card : ℝ) ^ 8 ≤ ((q.divisors.card : ℝ)) ^ 24 := by
  have hcard := divisors_card_le_pow_three hq h
  have h8 : (sqfreePart q * d * g).divisors.card ^ 8 ≤ q.divisors.card ^ 24 :=
    calc _ ≤ (q.divisors.card ^ 3) ^ 8 := Nat.pow_le_pow_left hcard 8
      _ = q.divisors.card ^ 24 := by rw [← pow_mul]
  have hcast := (Nat.cast_le (α := ℝ)).mpr h8
  simpa using hcast

end Work.LinnikBurgess
