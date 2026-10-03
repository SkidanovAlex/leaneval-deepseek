import Mathlib.Algebra.Order.Star.Basic
import Mathlib.Data.Nat.Squarefree

namespace Commons.NumberTheory.Lcm

/-- For a pair `(a, b)` of squarefree naturals with `lcm (a ^ 2) b = k` (`k ≠ 0`),
a prime `p` divides `a` exactly when the exponent of `p` in `k` is at least two. -/
private lemma prime_dvd_left_iff {k : ℕ} (hk : k ≠ 0) {a b : ℕ} (ha : Squarefree a)
    (hb : Squarefree b) (hlcm : Nat.lcm (a ^ 2) b = k) {p : ℕ} (hp : p.Prime) :
    p ∣ a ↔ 2 ≤ k.factorization p := by
  have ha2 : a ^ 2 ≠ 0 := pow_ne_zero 2 ha.ne_zero
  have hb0 : b ≠ 0 := hb.ne_zero
  constructor
  · intro hpa
    have h2 : p ^ 2 ∣ a ^ 2 := by rw [pow_two, pow_two]; exact mul_dvd_mul hpa hpa
    have h3 : p ^ 2 ∣ k := by rw [← hlcm]; exact h2.trans (Nat.dvd_lcm_left _ _)
    exact (hp.pow_dvd_iff_le_factorization hk).1 h3
  · intro h2
    have hlcm0 : Nat.lcm (a ^ 2) b ≠ 0 := by rw [hlcm]; exact hk
    have hkdvd : p ^ 2 ∣ k := (hp.pow_dvd_iff_le_factorization hk).2 h2
    have hkdvd' : p ^ 2 ∣ Nat.lcm (a ^ 2) b := by rw [hlcm]; exact hkdvd
    have hle : 2 ≤ (Nat.lcm (a ^ 2) b).factorization p :=
      (hp.pow_dvd_iff_le_factorization hlcm0).1 hkdvd'
    rw [Nat.factorization_lcm ha2 hb0, Finsupp.sup_apply] at hle
    rcases le_max_iff.mp hle with h | h
    · have h4 : p ^ 2 ∣ a ^ 2 := (hp.pow_dvd_iff_le_factorization ha2).2 h
      have : p ∣ a ^ 2 := dvd_trans (dvd_pow_self p (by norm_num)) h4
      exact hp.dvd_of_dvd_pow this
    · exfalso
      have h4 : p ^ 2 ∣ b := (hp.pow_dvd_iff_le_factorization hb0).2 h
      exact Nat.squarefree_iff_prime_squarefree.mp hb p hp (by rwa [pow_two] at h4)

theorem card_lcm_sq_eq_le_tau (k : ℕ) :
    (((Finset.Icc 1 k).product (Finset.Icc 1 k)).filter
        (fun p : ℕ × ℕ => Squarefree p.1 ∧ Squarefree p.2 ∧ Nat.lcm (p.1 ^ 2) p.2 = k)).card
      ≤ k.divisors.card := by
  classical
  rcases eq_or_ne k 0 with rfl | hk
  · simp
  · refine Finset.card_le_card_of_injOn (fun p : ℕ × ℕ => p.2) ?_ ?_
    · intro p hp
      simp only [Finset.mem_coe, Finset.mem_filter] at hp
      obtain ⟨-, hsf1, hsf2, hlcm⟩ := hp
      exact Nat.mem_divisors.mpr ⟨by rw [← hlcm]; exact Nat.dvd_lcm_right _ _, hk⟩
    · intro p hp q hq hpq
      simp only [Finset.mem_coe, Finset.mem_filter] at hp hq
      obtain ⟨-, hp1, hp2, hk1⟩ := hp
      obtain ⟨-, hq1, hq2, hk2⟩ := hq
      have heq : p.1 = q.1 := by
        refine (Nat.Squarefree.ext_iff hp1 hq1).2 ?_
        intro r hr
        rw [prime_dvd_left_iff hk hp1 hp2 hk1 hr, prime_dvd_left_iff hk hq1 hq2 hk2 hr]
      exact Prod.ext heq hpq

end Commons.NumberTheory.Lcm