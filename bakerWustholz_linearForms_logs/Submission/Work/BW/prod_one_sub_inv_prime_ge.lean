import Mathlib
import Submission.Work.BW.card_add_one_le_max_prime
import Submission.Work.BW.one_div_le_one_sub_inv

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BW

/-- Main induction: for a finset of `k` primes the product of `1 - 1/p` is at least
`1/(k+1)`.  Peel off the largest prime `p`; the remaining `k` primes contribute
`≥ 1/(k+1)` by induction, and `p ≥ k + 2` (a finset of distinct primes all `≥ 2`
with maximum `p` has at most `p - 1` elements), so the extra factor `1 - 1/p`
keeps us above `1/(k+2)`. -/
private lemma main : ∀ (k : ℕ) (s : Finset ℕ), s.card = k → (∀ p ∈ s, p.Prime) →
    1 / ((k : ℝ) + 1) ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹) := by
  intro k
  induction k with
  | zero =>
    intro s hcard hs
    rw [Finset.card_eq_zero.mp hcard]
    simp
  | succ k ih =>
    intro s hcard hs
    have hne : s.Nonempty := Finset.card_pos.mp (by rw [hcard]; exact Nat.succ_pos k)
    set p := s.max' hne with hp_def
    have hp_mem : p ∈ s := by rw [hp_def]; exact Finset.max'_mem s hne
    have hmax : ∀ q ∈ s, q ≤ p := by
      intro q hq; rw [hp_def]; exact Finset.le_max' s q hq
    have hpprime : p.Prime := hs p hp_mem
    have hbound : k + 2 ≤ p := by
      have hb := card_add_one_le_max_prime s hne hs
      rw [hcard, ← hp_def] at hb
      omega
    have ht_card : (s.erase p).card = k := by
      rw [Finset.card_erase_of_mem hp_mem, hcard]
      omega
    have ht_prime : ∀ q ∈ s.erase p, q.Prime := fun q hq => hs q (Finset.mem_of_mem_erase hq)
    have hIH : 1 / ((k : ℝ) + 1) ≤ ∏ q ∈ s.erase p, (1 - (q : ℝ)⁻¹) :=
      ih (s.erase p) ht_card ht_prime
    have hprod : ∏ q ∈ s, (1 - (q : ℝ)⁻¹)
        = (1 - (p : ℝ)⁻¹) * ∏ q ∈ s.erase p, (1 - (q : ℝ)⁻¹) :=
      (Finset.mul_prod_erase s (fun q => (1 - (q : ℝ)⁻¹)) hp_mem).symm
    have hfp : 0 ≤ 1 - (p : ℝ)⁻¹ := by
      have h1 : (1 : ℝ) ≤ (p : ℝ) := by exact_mod_cast hpprime.one_lt.le
      have := inv_le_one_of_one_le₀ h1
      linarith
    rw [hprod]
    calc 1 / ((((k + 1 : ℕ)) : ℝ) + 1) = 1 / ((k : ℝ) + 2) := by push_cast; ring
      _ ≤ (1 - (p : ℝ)⁻¹) * (1 / ((k : ℝ) + 1)) :=
            one_div_le_one_sub_inv k (by exact_mod_cast hbound)
      _ ≤ (1 - (p : ℝ)⁻¹) * ∏ q ∈ s.erase p, (1 - (q : ℝ)⁻¹) :=
            mul_le_mul_of_nonneg_left hIH hfp

theorem prod_one_sub_inv_prime_ge (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime) :
    1 / ((s.card : ℝ) + 1) ≤ ∏ p ∈ s, (1 - (p : ℝ)⁻¹) :=
  main s.card s rfl hs

end Work.BW
