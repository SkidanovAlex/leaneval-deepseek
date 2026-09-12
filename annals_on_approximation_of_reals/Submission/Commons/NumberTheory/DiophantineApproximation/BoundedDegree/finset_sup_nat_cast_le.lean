import Mathlib.Algebra.CharP.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Mathlib.Order.Lattice.Nat

namespace Commons.NumberTheory.DiophantineApproximation.BoundedDegree

/-- The supremum (maximum) of a finite set of natural numbers, viewed as a real number,
is bounded above by any real `M ≥ 0` that bounds each element. -/
theorem finset_sup_nat_cast_le {s : Finset ℕ} {f : ℕ → ℕ} {M : ℝ} (hM0 : 0 ≤ M)
    (h : ∀ i ∈ s, (f i : ℝ) ≤ M) : (((s.sup f : ℕ) : ℝ)) ≤ M := by
  classical
  let P : Finset ℕ → Prop := fun t =>
    (∀ i ∈ t, (f i : ℝ) ≤ M) → (((t.sup f : ℕ) : ℝ)) ≤ M
  have hp : P s := by
    refine Finset.induction_on s ?empty ?insert
    · intro h_empty
      simp [hM0]
    · intro a t hat ih h_insert
      have hia : (f a : ℝ) ≤ M := h_insert a (by simp)
      have hit : (∀ i ∈ t, (f i : ℝ) ≤ M) := fun i hi => h_insert i (by simp [hi])
      have hts : ((t.sup f : ℕ) : ℝ) ≤ M := ih hit
      rw [Finset.sup_insert]
      change ((max (f a) (t.sup f : ℕ) : ℕ) : ℝ) ≤ M
      rw [Nat.cast_max]
      exact max_le hia hts
  exact hp h

end Commons.NumberTheory.DiophantineApproximation.BoundedDegree