import Mathlib.Algebra.CharP.Defs
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Real.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Tactic.Ring.RingNF
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.UBBInputs3.MatLoc

/-- Splitting a symmetric integer sum: the sum over `Icc (-N) N` (with `N ≥ 0`)
equals the central term `g 0` plus, over the positive range `1 ≤ k ≤ N`, the
symmetric pair `g k + g (-k)`. -/
theorem sum_Icc_neg_split (N : ℤ) (hN : 0 ≤ N) (g : ℤ → ℝ) :
    ∑ k ∈ Finset.Icc (-N) N, g k = g 0 + ∑ k ∈ Finset.Icc 1 N, (g k + g (-k)) := by
  obtain ⟨n, rfl⟩ := Int.eq_ofNat_of_zero_le hN
  clear hN
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Nat.cast_succ]
    have hIcc1 : Finset.Icc (-((n:ℤ)+1)) ((n:ℤ)+1) =
        insert (-((n:ℤ)+1)) (insert ((n:ℤ)+1) (Finset.Icc (-(n:ℤ)) (n:ℤ))) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; constructor <;> intro h <;> omega
    have hIcc2 : Finset.Icc (1:ℤ) ((n:ℤ)+1) = insert ((n:ℤ)+1) (Finset.Icc 1 (n:ℤ)) := by
      ext k; simp only [Finset.mem_Icc, Finset.mem_insert]; constructor <;> intro h <;> omega
    have hm1 : (-((n:ℤ)+1)) ∉ insert ((n:ℤ)+1) (Finset.Icc (-(n:ℤ)) (n:ℤ)) := by
      simp only [Finset.mem_insert, Finset.mem_Icc]; omega
    have hm2 : ((n:ℤ)+1) ∉ Finset.Icc (-(n:ℤ)) (n:ℤ) := by
      simp only [Finset.mem_Icc]; omega
    have hm3 : ((n:ℤ)+1) ∉ Finset.Icc (1:ℤ) (n:ℤ) := by
      simp only [Finset.mem_Icc]; omega
    rw [hIcc1, hIcc2, Finset.sum_insert hm1, Finset.sum_insert hm2,
        Finset.sum_insert hm3, ih]
    ring

end Work.UBBInputs3.MatLoc
