import Mathlib.Algebra.Order.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.PrimeFin
import Mathlib.Data.Real.Basic

namespace Commons.NumberTheory.Nat

/-- If `U` is a finset of primes lying in the interval `[m, a)` and `a` is a prime with `m ≤ a`,
then the `U.card`-th prime at or above `m` (zero-indexed) is at most `a`.

Concretely: the primes `≥ m` that are `< a` number `Nat.count Nat.Prime a - Nat.count Nat.Prime m`,
which is at least `U.card`; hence the index `Nat.count Nat.Prime m + U.card` is at most
`Nat.count Nat.Prime a`, and the `n`-th prime is monotone in `n`. -/
private lemma nth_prime_le_of_primes_lt {U : Finset ℕ} {m a : ℕ} (ha : Nat.Prime a) (ham : m ≤ a)
    (hU : ∀ x ∈ U, Nat.Prime x) (hUm : ∀ x ∈ U, m ≤ x) (hUa : ∀ x ∈ U, x < a) :
    Nat.nth Nat.Prime (Nat.count Nat.Prime m + U.card) ≤ a := by
  classical
  have hp : (Set.ofPred Nat.Prime).Infinite := Nat.infinite_setOfPred_prime
  have hcount : Nat.count Nat.Prime m + U.card ≤ Nat.count Nat.Prime a := by
    rw [Nat.count_eq_card_filter_range (p := Nat.Prime) m,
        Nat.count_eq_card_filter_range (p := Nat.Prime) a]
    have hsub : (Finset.range m).filter Nat.Prime ∪ U ⊆ (Finset.range a).filter Nat.Prime := by
      intro x hx
      rw [Finset.mem_union, Finset.mem_filter] at hx
      rw [Finset.mem_filter]
      rcases hx with ⟨hxr, hxp⟩ | hx
      · exact ⟨Finset.mem_range.mpr (lt_of_lt_of_le (Finset.mem_range.mp hxr) ham), hxp⟩
      · exact ⟨Finset.mem_range.mpr (hUa x hx), hU x hx⟩
    have hdisj : Disjoint ((Finset.range m).filter Nat.Prime) U := by
      rw [Finset.disjoint_left]
      intro x hxB hxU
      rw [Finset.mem_filter] at hxB
      exact absurd (Finset.mem_range.mp hxB.1) (not_lt.mpr (hUm x hxU))
    calc ((Finset.range m).filter Nat.Prime).card + U.card
        = (((Finset.range m).filter Nat.Prime) ∪ U).card :=
          (Finset.card_union_of_disjoint hdisj).symm
      _ ≤ ((Finset.range a).filter Nat.Prime).card := Finset.card_le_card hsub
  calc Nat.nth Nat.Prime (Nat.count Nat.Prime m + U.card)
      ≤ Nat.nth Nat.Prime (Nat.count Nat.Prime a) := Nat.nth_monotone hp hcount
    _ = a := Nat.nth_count ha

theorem prod_nth_prime_le_prod_of_le (S : Finset ℕ) (m : ℕ) (hS : ∀ x ∈ S, Nat.Prime x)
    (hm : ∀ x ∈ S, m ≤ x) (g : ℕ → ℝ) (hg : Monotone g) (hg0 : ∀ x, 0 ≤ g x) :
    (∏ i ∈ Finset.range S.card, g (Nat.nth Nat.Prime (Nat.count Nat.Prime m + i)))
      ≤ ∏ x ∈ S, g x := by
  classical
  revert hS hm
  refine Finset.induction_on_max
    (motive := fun T => (∀ x ∈ T, Nat.Prime x) → (∀ x ∈ T, m ≤ x) →
      (∏ i ∈ Finset.range T.card, g (Nat.nth Nat.Prime (Nat.count Nat.Prime m + i)))
        ≤ ∏ x ∈ T, g x) S ?_ ?_
  · intro _ _
    simp
  · intro a s hlt ih hS hm
    have ha : Nat.Prime a := hS a (Finset.mem_insert_self a s)
    have ham : m ≤ a := hm a (Finset.mem_insert_self a s)
    have hs : ∀ x ∈ s, Nat.Prime x := fun x hx => hS x (Finset.mem_insert_of_mem hx)
    have hsm : ∀ x ∈ s, m ≤ x := fun x hx => hm x (Finset.mem_insert_of_mem hx)
    have hnotin : a ∉ s := fun h => absurd (hlt a h) (lt_irrefl a)
    have hih : (∏ i ∈ Finset.range s.card, g (Nat.nth Nat.Prime (Nat.count Nat.Prime m + i)))
        ≤ ∏ x ∈ s, g x := ih hs hsm
    have hkey : Nat.nth Nat.Prime (Nat.count Nat.Prime m + s.card) ≤ a :=
      nth_prime_le_of_primes_lt ha ham hs hsm hlt
    rw [Finset.prod_insert hnotin, Finset.card_insert_of_notMem hnotin, Finset.prod_range_succ]
    calc (∏ i ∈ Finset.range s.card, g (Nat.nth Nat.Prime (Nat.count Nat.Prime m + i))) *
          g (Nat.nth Nat.Prime (Nat.count Nat.Prime m + s.card))
        ≤ (∏ x ∈ s, g x) * g a :=
          mul_le_mul hih (hg hkey) (hg0 _) (Finset.prod_nonneg fun x _ => hg0 x)
      _ = g a * ∏ x ∈ s, g x := mul_comm _ _

end Commons.NumberTheory.Nat