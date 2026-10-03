import Mathlib
import Submission.Lib.Unif2.Commons.Topology.Plane.union_of_retracts

namespace Commons.Topology.Plane

/-- If every `A n` is a retract of the plane and every `accumulate A n ∩ A (n+1)` is a retract of
the plane, then every accumulated union `accumulate A n` is a retract of the plane.

This is the unbounded form of `Commons.Topology.Plane.retract_accumulate_of_retracts_lt`: induction
on `n`, using `accumulate A (n+1) = accumulate A n ∪ A (n+1)` and the gluing theorem
`union_of_retracts`. -/
theorem retract_union_accumulate_of_retracts {A : ℕ → Set ℂ}
    (hA : ∀ n, ∃ r : C(ℂ, ↥(A n)), ∀ x : ↥(A n), r (x : ℂ) = x)
    (hI : ∀ n, ∃ r : C(ℂ, ↥(Set.accumulate A n ∩ A (n + 1))),
      ∀ x : ↥(Set.accumulate A n ∩ A (n + 1)), r (x : ℂ) = x) :
    ∀ n, ∃ r : C(ℂ, ↥(Set.accumulate A n)), ∀ x : ↥(Set.accumulate A n), r (x : ℂ) = x := by
  intro n
  induction n with
  | zero =>
      rw [Set.accumulate_zero_nat]
      exact hA 0
  | succ k ih =>
      rw [Set.accumulate_succ]
      exact union_of_retracts ih (hA (k + 1)) (hI k)

end Commons.Topology.Plane
