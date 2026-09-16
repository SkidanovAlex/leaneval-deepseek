import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Tactic.Abel

open scoped BigOperators

namespace Commons.Data.Finset

/-- A double sum over a square range splits into the strict-below, strict-above and
diagonal parts. -/
lemma sum_range_double_split {M : Type*} [AddCommMonoid M] (d : ℕ) (f : ℕ → ℕ → M) :
    (∑ ℓ ∈ Finset.range d, ∑ m ∈ Finset.range d, f ℓ m) =
      (∑ ℓ ∈ Finset.range d, ∑ m ∈ Finset.range ℓ, f ℓ m) +
      (∑ m ∈ Finset.range d, ∑ ℓ ∈ Finset.range m, f ℓ m) +
      (∑ ℓ ∈ Finset.range d, f ℓ ℓ) := by
  induction d with
  | zero => simp
  | succ n ih =>
      simp_rw [Finset.sum_range_succ]
      rw [Finset.sum_add_distrib]
      rw [ih]
      abel

lemma sum_range_mul_split {R : Type*} [Semiring R] (d : ℕ) (a b : ℕ → R) :
    (∑ ℓ ∈ Finset.range d, a ℓ) * (∑ m ∈ Finset.range d, b m) =
      (∑ ℓ ∈ Finset.range d, ∑ m ∈ Finset.range ℓ, a ℓ * b m) +
      (∑ m ∈ Finset.range d, ∑ ℓ ∈ Finset.range m, a ℓ * b m) +
      (∑ ℓ ∈ Finset.range d, a ℓ * b ℓ) := by
  rw [Finset.sum_mul_sum]
  exact sum_range_double_split d (fun ℓ m => a ℓ * b m)

end Commons.Data.Finset