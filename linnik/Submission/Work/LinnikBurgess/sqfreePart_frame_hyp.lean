import Mathlib
import Submission.Work.LinnikBurgess.singleton_ssa_defs

/-!
# The arithmetic frame hypothesis for the `sqfreePart q` splitting

With `e_p = q.factorization p` the primes of `q` split into the *low* set
`lowPrimeSet q = {p : e_p = 1}` (whose product is `sqfreePart q`) and the *high* set
`highPrimeSet q = {p : 2 ≤ e_p}`.  For an arbitrary choice
`σ : ↥(highPrimeSet q) → ℕ × ℕ` with `(σ p).1 ≤ e_p + 1` and `(σ p).2 ≤ e_p` the numbers

`d = ∏_p p^{(σ p).1}`  and  `g = ∏_p p^{(σ p).2}`

satisfy the abstract hypotheses of Theorem F (`frame_count`): `sqfreePart q` is squarefree and
coprime to both `d` and `g`, both are positive, `sqfreePart q * d * g ∣ q^3`, and `d` involves at
most `(highPrimeSet q).card` distinct primes.

The proof is a pointwise comparison of `p`-adic valuations, for which the basic tool is the
factorisation of a product of distinct primes to arbitrary powers
(`sqfFrame_factorization_prod_prime_pow`).
-/

open scoped BigOperators
open Classical

namespace Work.LinnikBurgess

/-! ## Elementary facts about `primeFactors`, `lowPrimeSet` and `highPrimeSet` -/

lemma sqfFrame_prime_of_mem_high {q p : ℕ} (hp : p ∈ highPrimeSet q) : Nat.Prime p :=
  Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)

lemma sqfFrame_prime_of_mem_low {q p : ℕ} (hp : p ∈ lowPrimeSet q) : Nat.Prime p :=
  Nat.prime_of_mem_primeFactors (Finset.mem_of_mem_filter p hp)

lemma sqfFrame_low_ne_high {q p p' : ℕ} (hp : p ∈ lowPrimeSet q) (hp' : p' ∈ highPrimeSet q) :
    p ≠ p' := by
  intro h; subst h
  rw [lowPrimeSet, Finset.mem_filter] at hp
  rw [highPrimeSet, Finset.mem_filter] at hp'
  omega

/-! ## Factorisation of `∏ p ∈ s, p ^ k p` -/

/-- The `p`-adic valuation of a product of distinct primes raised to arbitrary powers. -/
lemma sqfFrame_factorization_prod_prime_pow {s : Finset ℕ} {k : ℕ → ℕ}
    (hs : ∀ p ∈ s, Nat.Prime p) (r : ℕ) :
    (∏ p ∈ s, p ^ k p).factorization r = if r ∈ s then k r else 0 := by
  have hne : ∀ p ∈ s, p ^ k p ≠ 0 := fun p hp => pow_ne_zero _ (hs p hp).ne_zero
  have h1 : (∏ p ∈ s, p ^ k p).factorization = ∑ p ∈ s, (p ^ k p).factorization :=
    Nat.factorization_prod hne
  rw [h1, Finsupp.finsetSum_apply]
  have h2 : ∀ p ∈ s, (p ^ k p).factorization r = if r = p then k p else 0 := by
    intro p hp
    rw [(hs p hp).factorization_pow]
    by_cases h : r = p
    · subst h; simp
    · rw [Finsupp.single_eq_of_ne h, if_neg h]
  rw [Finset.sum_congr rfl h2]
  exact Finset.sum_ite_eq s r k

/-- Rewrite the subtype product over `highPrimeSet q` as a Finset product. -/
lemma sqfFrame_prod_high_eq (q : ℕ) (k : ↥(highPrimeSet q) → ℕ) :
    (∏ p : ↥(highPrimeSet q), p.val ^ k p)
      = ∏ p ∈ highPrimeSet q, p ^ (if h : p ∈ highPrimeSet q then k ⟨p, h⟩ else 1) := by
  rw [← Finset.prod_attach (highPrimeSet q)
      (fun p : ℕ => p ^ (if h : p ∈ highPrimeSet q then k ⟨p, h⟩ else 1)),
    Finset.attach_eq_univ]
  refine Finset.prod_congr rfl (fun p _ => ?_)
  rw [dif_pos p.2]

/-- The `r`-adic valuation of `∏ p : ↥(highPrimeSet q), p ^ k p`: only the prime `r` itself can
contribute, and only if it belongs to `highPrimeSet q`. -/
lemma sqfFrame_factorization_high (q : ℕ) (k : ↥(highPrimeSet q) → ℕ) (r : ℕ) :
    (∏ p : ↥(highPrimeSet q), p.val ^ k p).factorization r
      = if h : r ∈ highPrimeSet q then k ⟨r, h⟩ else 0 := by
  rw [sqfFrame_prod_high_eq,
    sqfFrame_factorization_prod_prime_pow
      (fun p hp => sqfFrame_prime_of_mem_high hp) r]
  by_cases h : r ∈ highPrimeSet q <;> simp [h]

/-- The `r`-adic valuation of `sqfreePart q`. -/
lemma sqfFrame_sqfreePart_factorization (q r : ℕ) :
    (sqfreePart q).factorization r = if r ∈ lowPrimeSet q then 1 else 0 := by
  have h : sqfreePart q = ∏ p ∈ lowPrimeSet q, p ^ (1 : ℕ) := by
    rw [sqfreePart, lowPrimeSet]
    exact Finset.prod_congr rfl (fun p _ => (pow_one p).symm)
  rw [h, sqfFrame_factorization_prod_prime_pow (fun p hp => sqfFrame_prime_of_mem_low hp) r]

/-! ## The individual claims -/

/-- `sqfreePart q` is coprime to any product of powers of the primes of `highPrimeSet q`. -/
lemma sqfFrame_coprime_high (q : ℕ) (k : ↥(highPrimeSet q) → ℕ) :
    Nat.Coprime (sqfreePart q) (∏ p : ↥(highPrimeSet q), p.val ^ k p) := by
  rw [sqfFrame_prod_high_eq]
  have h : sqfreePart q = ∏ p ∈ lowPrimeSet q, p := rfl
  rw [h]
  refine Nat.Coprime.prod_left (fun p hp => ?_)
  refine Nat.Coprime.prod_right (fun p' hp' => ?_)
  refine Nat.Coprime.pow_right _ ?_
  exact (Nat.coprime_primes (sqfFrame_prime_of_mem_low hp) (sqfFrame_prime_of_mem_high hp')).mpr
    (sqfFrame_low_ne_high hp hp')

/-- A product of powers of the primes of `highPrimeSet q` involves at most
`(highPrimeSet q).card` distinct primes. -/
lemma sqfFrame_card_high (q : ℕ) (k : ↥(highPrimeSet q) → ℕ) :
    (∏ p : ↥(highPrimeSet q), p.val ^ k p).primeFactors.card ≤ (highPrimeSet q).card := by
  rw [sqfFrame_prod_high_eq]
  have hne : (∏ p ∈ highPrimeSet q, p ^ (if h : p ∈ highPrimeSet q then k ⟨p, h⟩ else 1)) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr
      (fun p hp => pow_ne_zero _ (sqfFrame_prime_of_mem_high hp).ne_zero)
  have hsub :
      (∏ p ∈ highPrimeSet q, p ^ (if h : p ∈ highPrimeSet q then k ⟨p, h⟩ else 1)).primeFactors
        ⊆ highPrimeSet q := by
    intro r hr
    rw [Nat.mem_primeFactors] at hr
    obtain ⟨hpr, hdvd, -⟩ := hr
    by_contra hrH
    have h1 := (hpr.dvd_iff_one_le_factorization hne).mp hdvd
    rw [sqfFrame_factorization_prod_prime_pow (fun p hp => sqfFrame_prime_of_mem_high hp) r,
      if_neg hrH] at h1
    omega
  exact Finset.card_le_card hsub

/-- The key valuation bound: `sqfreePart q * d * g` has `r`-adic valuation at most `3 e_r`. -/
lemma sqfFrame_exp_bound (q : ℕ) (σ : ↥(highPrimeSet q) → ℕ × ℕ)
    (hσ1 : ∀ p, (σ p).1 ≤ q.factorization p.val + 1)
    (hσ2 : ∀ p, (σ p).2 ≤ q.factorization p.val) (r : ℕ) :
    (sqfreePart q).factorization r
      + (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).1).factorization r
      + (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).2).factorization r
      ≤ 3 * q.factorization r := by
  rw [sqfFrame_sqfreePart_factorization, sqfFrame_factorization_high,
    sqfFrame_factorization_high]
  by_cases hr : r ∈ q.primeFactors
  · have he1 : 1 ≤ q.factorization r := by
      have hm : r ∈ q.factorization.support := by rwa [Nat.support_factorization]
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hm)
    by_cases he : q.factorization r = 1
    · have hrlow : r ∈ lowPrimeSet q := by
        rw [lowPrimeSet, Finset.mem_filter]; exact ⟨hr, he⟩
      have hrhigh : r ∉ highPrimeSet q := by
        intro h; rw [highPrimeSet, Finset.mem_filter] at h; omega
      rw [if_pos hrlow, dif_neg hrhigh, dif_neg hrhigh]; omega
    · have he2 : 2 ≤ q.factorization r := by omega
      have hrhigh : r ∈ highPrimeSet q := by
        rw [highPrimeSet, Finset.mem_filter]; exact ⟨hr, he2⟩
      have hrlow : r ∉ lowPrimeSet q := by
        intro h; rw [lowPrimeSet, Finset.mem_filter] at h; omega
      rw [if_neg hrlow, dif_pos hrhigh, dif_pos hrhigh]
      have h1 : (σ ⟨r, hrhigh⟩).1 ≤ q.factorization r + 1 := hσ1 ⟨r, hrhigh⟩
      have h2 : (σ ⟨r, hrhigh⟩).2 ≤ q.factorization r := hσ2 ⟨r, hrhigh⟩
      omega
  · have he0 : q.factorization r = 0 := by
      by_contra h
      have hm : r ∈ q.factorization.support := Finsupp.mem_support_iff.mpr h
      rw [Nat.support_factorization] at hm
      exact hr hm
    have hrlow : r ∉ lowPrimeSet q := fun h => hr (Finset.mem_of_mem_filter r h)
    have hrhigh : r ∉ highPrimeSet q := fun h => hr (Finset.mem_of_mem_filter r h)
    rw [if_neg hrlow, dif_neg hrhigh, dif_neg hrhigh]
    omega

/-! ## The requested statement -/

theorem sqfreePart_frame_hyp {q : ℕ} (hq : 0 < q) (σ : ↥(highPrimeSet q) → ℕ × ℕ)
    (hσ : ∀ p, σ p ∈ (Finset.range (q.factorization p.val + 2)).product
      (Finset.range (q.factorization p.val + 1))) :
    Squarefree (sqfreePart q)
      ∧ Nat.Coprime (sqfreePart q) (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).1)
      ∧ Nat.Coprime (sqfreePart q) (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).2)
      ∧ 0 < (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).1)
      ∧ 0 < (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).2)
      ∧ sqfreePart q * (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).1)
          * (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).2) ∣ q ^ 3
      ∧ (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).1).primeFactors.card ≤ (highPrimeSet q).card := by
  classical
  have hσ1 : ∀ p : ↥(highPrimeSet q), (σ p).1 ≤ q.factorization p.val + 1 := by
    intro p
    have h := (Finset.mem_product.mp (hσ p)).1
    rw [Finset.mem_range] at h; omega
  have hσ2 : ∀ p : ↥(highPrimeSet q), (σ p).2 ≤ q.factorization p.val := by
    intro p
    have h := (Finset.mem_product.mp (hσ p)).2
    rw [Finset.mem_range] at h; omega
  have hA0 : sqfreePart q ≠ 0 := by
    rw [show sqfreePart q = ∏ p ∈ lowPrimeSet q, p from rfl]
    exact Finset.prod_ne_zero_iff.mpr (fun p hp => (sqfFrame_prime_of_mem_low hp).ne_zero)
  have hD10 : (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).1) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun p _ => pow_pos (sqfFrame_prime_of_mem_high p.2).pos _))
  have hD20 : (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).2) ≠ 0 :=
    ne_of_gt (Finset.prod_pos (fun p _ => pow_pos (sqfFrame_prime_of_mem_high p.2).pos _))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · refine Nat.squarefree_of_factorization_le_one hA0 (fun r => ?_)
    rw [sqfFrame_sqfreePart_factorization]
    by_cases h : r ∈ lowPrimeSet q <;> simp [h]
  · exact sqfFrame_coprime_high q (fun p => (σ p).1)
  · exact sqfFrame_coprime_high q (fun p => (σ p).2)
  · exact Finset.prod_pos (fun p _ => pow_pos (sqfFrame_prime_of_mem_high p.2).pos _)
  · exact Finset.prod_pos (fun p _ => pow_pos (sqfFrame_prime_of_mem_high p.2).pos _)
  · rw [← Nat.factorization_le_iff_dvd (mul_ne_zero (mul_ne_zero hA0 hD10) hD20)
      (pow_ne_zero 3 (ne_of_gt hq))]
    rw [Finsupp.le_def]
    intro r
    have hLHS : (sqfreePart q * (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).1)
          * (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).2)).factorization r
        = (sqfreePart q).factorization r
          + (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).1).factorization r
          + (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).2).factorization r := by
      have e1 : (sqfreePart q * (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).1)).factorization
          = (sqfreePart q).factorization
            + (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).1).factorization :=
        Nat.factorization_mul hA0 hD10
      have e2 : (sqfreePart q * (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).1)
            * (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).2)).factorization
          = (sqfreePart q * (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).1)).factorization
            + (∏ p : ↥(highPrimeSet q), p.val ^ (σ p).2).factorization :=
        Nat.factorization_mul (mul_ne_zero hA0 hD10) hD20
      rw [e2, Finsupp.add_apply, e1, Finsupp.add_apply]
    have hRHS : (q ^ 3).factorization r = 3 * q.factorization r := by
      rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul]
    rw [hLHS, hRHS]
    exact sqfFrame_exp_bound q σ hσ1 hσ2 r
  · exact sqfFrame_card_high q (fun p => (σ p).1)

end Work.LinnikBurgess
