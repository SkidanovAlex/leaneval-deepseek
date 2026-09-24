import Mathlib
import Submission.Work.NumberTheory.Chen.BTermCount.BLodDefs

namespace Work.NumberTheory.Chen.BTermCount

/-!
# Injectivity of the product map on `B`-term triples

A `B`-term triple is a triple `(q, q₂, q₃)` of primes with `M ≤ q < Y ≤ q₂ ≤ q₃` and
`q q₂ q₃ ≤ x + 2`.  Its product `q q₂ q₃` determines it: the smallest prime factor below
`Y` is unique, and the remaining two primes are pinned down by their ordering.

Hence the map `t ↦ t.1 * t.2.1 * t.2.2` is injective on `bTripleSet x M Y`, which is what
makes `bProdSet x M Y` have the same cardinality as `bTripleSet x M Y` and lets one replace
the multiple counting of triples by counting of products.
-/

/-- Membership in `bTripleSet x M Y`, unpacked into its eight conjuncts. -/
theorem mem_bTripleSet_elim {x M Y : ℕ} {t : ℕ × ℕ × ℕ} (ht : t ∈ bTripleSet x M Y) :
    t.1.Prime ∧ t.2.1.Prime ∧ t.2.2.Prime ∧ M ≤ t.1 ∧ t.1 < Y ∧ Y ≤ t.2.1 ∧
      t.2.1 ≤ t.2.2 ∧ t.1 * t.2.1 * t.2.2 ≤ x + 2 := by
  classical
  rw [bTripleSet, Finset.mem_filter] at ht
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := ht.2
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩

/-- A prime dividing a prime equals it. -/
theorem prime_eq_of_dvd_prime {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (h : p ∣ q) : p = q :=
  ((hq.dvd_iff_eq hp.ne_one).mp h).symm

theorem BLodTripleInj {x M Y : ℕ} {t t' : ℕ × ℕ × ℕ}
    (ht : t ∈ bTripleSet x M Y) (ht' : t' ∈ bTripleSet x M Y)
    (h : t.1 * t.2.1 * t.2.2 = t'.1 * t'.2.1 * t'.2.2) : t = t' := by
  obtain ⟨hp1, hp2, hp3, hM, hltY, hY, hle, hx⟩ := mem_bTripleSet_elim ht
  obtain ⟨hp1', hp2', hp3', hM', hltY', hY', hle', hx'⟩ := mem_bTripleSet_elim ht'
  -- Step 1: the smallest prime factor `t.1 < Y ≤ t'.2.1, t'.2.2` is forced.
  have hfirst : t.1 = t'.1 := by
    have hdvd : t.1 ∣ t'.1 * t'.2.1 * t'.2.2 := by
      rw [← h]
      exact dvd_mul_of_dvd_left (dvd_mul_right t.1 t.2.1) t.2.2
    rcases (hp1.dvd_mul).mp hdvd with hcase | hcase
    · rcases (hp1.dvd_mul).mp hcase with hA | hB
      · exact prime_eq_of_dvd_prime hp1 hp1' hA
      · exact absurd (prime_eq_of_dvd_prime hp1 hp2' hB) (by omega)
    · exact absurd (prime_eq_of_dvd_prime hp1 hp3' hcase) (by omega)
  -- Step 2: cancel the common factor `t.1 = t'.1`.
  have h2 : t.2.1 * t.2.2 = t'.2.1 * t'.2.2 := by
    have h' : t'.1 * (t.2.1 * t.2.2) = t'.1 * (t'.2.1 * t'.2.2) := by
      rw [hfirst] at h
      simp only [mul_assoc] at h
      exact h
    exact Nat.mul_left_cancel hp1'.pos h'
  -- Step 3: the ordered pair `(t.2.1, t.2.2)` is forced by the product.
  have h3 : t.2.1 = t'.2.1 := by
    have hdvd2 : t.2.1 ∣ t'.2.1 * t'.2.2 := by
      rw [← h2]
      exact dvd_mul_right t.2.1 t.2.2
    rcases (hp2.dvd_mul).mp hdvd2 with hA | hB
    · exact prime_eq_of_dvd_prime hp2 hp2' hA
    · have hb23 : t.2.1 = t'.2.2 := prime_eq_of_dvd_prime hp2 hp3' hB
      have hb32 : t.2.2 = t'.2.1 := by
        have key : t.2.1 * t.2.2 = t.2.1 * t'.2.1 := by
          calc t.2.1 * t.2.2 = t'.2.1 * t'.2.2 := h2
            _ = t'.2.1 * t.2.1 := by rw [← hb23]
            _ = t.2.1 * t'.2.1 := by ring
        exact Nat.mul_left_cancel hp2.pos key
      omega
  -- Step 4: the largest factor.
  have h4 : t.2.2 = t'.2.2 := by
    rw [h3] at h2
    exact Nat.mul_left_cancel hp2'.pos h2
  exact Prod.ext hfirst (Prod.ext h3 h4)

end Work.NumberTheory.Chen.BTermCount
