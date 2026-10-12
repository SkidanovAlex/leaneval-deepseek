import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Star
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Submission.Work.UBBInputs3.MatLoc.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs3.MatLoc

theorem gamma_sum_cross (p : ℕ) (k : ℤ) {f : ℤ → ℝ}
    (hsupp : ∀ s, s ∉ Finset.Icc (-(p:ℤ)) (p:ℤ) → f s = 0) :
    (∑ s ∈ Finset.Icc (-(p:ℤ) - |k|) ((p:ℤ) + |k|), f (s+k) * f s)
      = ∑ t ∈ Finset.Icc (-(p:ℤ)) (p:ℤ), f t * f (t+k) := by
  -- The target interval [-p,p] is contained in the wide interval [-p-|k|, p+|k|].
  have hsub : Finset.Icc (-(p:ℤ)) (p:ℤ) ⊆ Finset.Icc (-(p:ℤ) - |k|) ((p:ℤ) + |k|) := by
    intro x hx
    simp only [Finset.mem_Icc] at hx ⊢
    obtain ⟨h1, h2⟩ := hx
    have hk : (0:ℤ) ≤ |k| := abs_nonneg k
    constructor <;> linarith
  -- Every term of the wide sum lying outside [-p,p] vanishes because f does.
  have hzero : ∀ x ∈ Finset.Icc (-(p:ℤ) - |k|) ((p:ℤ) + |k|),
      x ∉ Finset.Icc (-(p:ℤ)) (p:ℤ) → f (x+k) * f x = 0 := by
    intro x _ hx
    rw [hsupp x hx, mul_zero]
  -- Discard the vanishing terms of the wide sum.
  have hL : (∑ s ∈ Finset.Icc (-(p:ℤ) - |k|) ((p:ℤ) + |k|), f (s+k) * f s)
      = ∑ s ∈ Finset.Icc (-(p:ℤ)) (p:ℤ), f (s+k) * f s :=
    (Finset.sum_subset hsub hzero).symm
  rw [hL]
  -- The two sums now range over the same index set with the same summand.
  apply Finset.sum_congr rfl
  intro x hx
  ring

end Work.UBBInputs3.MatLoc
