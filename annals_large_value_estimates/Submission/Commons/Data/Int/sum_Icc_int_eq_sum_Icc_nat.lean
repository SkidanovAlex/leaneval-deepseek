import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Data.Int.ConditionallyCompleteOrder
import Mathlib.Data.Int.Interval
import Mathlib.Data.Nat.Cast.Order.Basic
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Order.Interval.Finset.Nat

namespace Commons.Data.Int

theorem sum_Icc_int_eq_sum_Icc_nat {M : Type*} [AddCommMonoid M] {L R : ℤ}
    (hL : 0 ≤ L) (hR : 0 ≤ R) (f : ℤ → M) :
    (∑ m ∈ Finset.Icc L R, f m) = ∑ n ∈ Finset.Icc (Int.toNat L) (Int.toNat R), f (n : ℤ) := by
  classical
  -- Reindex the sum over integers `m ∈ [L, R]` by writing `m = (n : ℤ)` for naturals
  -- `n ∈ [L.toNat, R.toNat]`; this is a bijection because `0 ≤ L` (hence `0 ≤ R` is
  -- only needed to guarantee the interval endpoints match, via `Int.toNat_of_nonneg`).
  have h : (∑ n ∈ Finset.Icc (Int.toNat L) (Int.toNat R), f (n : ℤ)) =
      ∑ m ∈ Finset.Icc L R, f m := by
    refine Finset.sum_bij (fun n _ => (n : ℤ)) ?hi ?h_inj ?h_surj ?h_eq
    · intro n hn
      rw [Finset.mem_Icc] at hn ⊢
      have hLn : L ≤ (n : ℤ) := by
        rw [← Int.toNat_of_nonneg hL]
        exact_mod_cast hn.1
      have hRn : (n : ℤ) ≤ R := by
        rw [← Int.toNat_of_nonneg hR]
        exact_mod_cast hn.2
      exact ⟨hLn, hRn⟩
    · intro n₁ _ n₂ _ h
      exact Int.ofNat_inj.mp h
    · intro m hm
      rw [Finset.mem_Icc] at hm
      refine ⟨Int.toNat m, ?mem, ?eq⟩
      · rw [Finset.mem_Icc]
        exact ⟨Int.toNat_le_toNat hm.1, Int.toNat_le_toNat hm.2⟩
      · exact Int.toNat_of_nonneg (le_trans hL hm.1)
    · intro n hn
      rfl
  exact h.symm

end Commons.Data.Int