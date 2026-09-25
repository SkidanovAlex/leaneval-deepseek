import Mathlib
import Submission.Work.RHContract.A.RegionI.Defs

/-!
# Region I: the basic steps of the block certificate

A block certificate walks over the primes between `m` and `n`.  This file isolates the four
elementary "step" facts that the walk uses, together with the list-scanning lemma that turns
the computable primality test `RegionI.isP` into a primality-free interval:

* if no integer in `(m, n)` passes `isP`, then no integer there is prime;
* if moreover `n` is prime, then `Nat.primesLE n = insert n (Nat.primesLE m)`;
* consequently the Mertens log-ratio sum `logRatioSum`, the reciprocal-square sum over the
  primes `≤ n`, and `Chebyshev.theta` all advance by the single prime `n`.
-/

open scoped BigOperators

namespace Work.RHContract.A.RegionI

/-- The primes `≤ n` are the primes `≤ m` together with `n`, when `n` is prime and there is
no prime strictly between `m` and `n`. -/
private lemma primesLE_step {m n : ℕ} (hm : m < n) (hn : Nat.Prime n)
    (hgap : ∀ q : ℕ, m < q → q < n → ¬ Nat.Prime q) :
    Nat.primesLE n = insert n (Nat.primesLE m) := by
  ext p
  rw [Nat.mem_primesLE, Finset.mem_insert, Nat.mem_primesLE]
  constructor
  · rintro ⟨hpn, hp⟩
    rcases eq_or_lt_of_le hpn with rfl | hlt
    · exact Or.inl rfl
    · exact Or.inr ⟨le_of_not_gt (fun hpm => hgap p hpm hlt hp), hp⟩
  · rintro (rfl | ⟨hpm, hp⟩)
    · exact ⟨le_rfl, hn⟩
    · exact ⟨le_trans hpm (le_of_lt hm), hp⟩

/-- For `m < n`, the prime `n` is not among the primes `≤ m`. -/
private lemma notMem_primesLE {m n : ℕ} (hm : m < n) : n ∉ Nat.primesLE m := by
  intro hcon
  rw [Nat.mem_primesLE] at hcon
  omega

theorem steps_basic :
    (∀ {m n : ℕ}, m < n → (List.range (n - m - 1)).all (fun j => !Work.RHContract.RegionI.isP (m + 1 + j)) = true →
        ∀ q : ℕ, m < q → q < n → ¬ Nat.Prime q) ∧
    (∀ {m n : ℕ}, m < n → Nat.Prime n → (∀ q : ℕ, m < q → q < n → ¬ Nat.Prime q) →
        Nat.primesLE n = insert n (Nat.primesLE m)) ∧
    (∀ {m n : ℕ}, m < n → Nat.Prime n → (∀ q : ℕ, m < q → q < n → ¬ Nat.Prime q) →
        Commons.NumberTheory.Mertens.logRatioSum (n : ℝ)
          = Commons.NumberTheory.Mertens.logRatioSum (m : ℝ) + Real.log ((n : ℝ) / ((n : ℝ) - 1))) ∧
    (∀ {m n : ℕ}, m < n → Nat.Prime n → (∀ q : ℕ, m < q → q < n → ¬ Nat.Prime q) →
        (∑ p ∈ Nat.primesLE n, (p : ℝ) ^ (-2 : ℤ))
          = (∑ p ∈ Nat.primesLE m, (p : ℝ) ^ (-2 : ℤ)) + (n : ℝ) ^ (-2 : ℤ)) ∧
    (∀ {m n : ℕ}, m < n → Nat.Prime n → (∀ q : ℕ, m < q → q < n → ¬ Nat.Prime q) →
        Chebyshev.theta (n : ℝ) = Chebyshev.theta (m : ℝ) + Real.log (n : ℝ)) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · -- the `isP` scan rules out every prime in `(m, n)`
    intro m n hm h q hmq hqn
    have hmem : q - m - 1 < n - m - 1 := by omega
    have h' := (List.all_eq_true.mp h) (q - m - 1) (List.mem_range.mpr hmem)
    have heq : m + 1 + (q - m - 1) = q := by omega
    rw [heq] at h'
    intro hp
    have htrue : Work.RHContract.RegionI.isP q = true :=
      (Work.RHContract.RegionI.isP_iff q).mpr hp
    rw [htrue] at h'
    exact Bool.false_ne_true h'
  · intro m n hm hn hgap
    exact primesLE_step hm hn hgap
  · -- the Mertens log-ratio sum advances by the single prime `n`
    intro m n hm hn hgap
    have hset := primesLE_step hm hn hgap
    have hnot := notMem_primesLE (m := m) hm
    unfold Commons.NumberTheory.Mertens.logRatioSum
    rw [Nat.floor_natCast, Nat.floor_natCast, hset, Finset.sum_insert hnot]
    ring
  · -- the reciprocal-square sum advances by the single prime `n`
    intro m n hm hn hgap
    have hset := primesLE_step hm hn hgap
    have hnot := notMem_primesLE (m := m) hm
    rw [hset, Finset.sum_insert hnot]
    ring
  · -- `θ` advances by `log n`
    intro m n hm hn hgap
    have hset := primesLE_step hm hn hgap
    have hnot := notMem_primesLE (m := m) hm
    rw [Chebyshev.theta_eq_sum_primesLE_log, Chebyshev.theta_eq_sum_primesLE_log, hset,
      Finset.sum_insert hnot]
    ring

end Work.RHContract.A.RegionI
