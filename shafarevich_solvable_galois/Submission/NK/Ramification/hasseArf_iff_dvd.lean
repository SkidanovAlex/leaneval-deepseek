import Mathlib
import Submission.NK.Ramification.Defs
import Submission.NK.Ramification.Herbrand
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.Ramification

/-- **The Hasse–Arf condition is exactly the divisibility of the partial lower-index sums by
`g_0` at the lower breaks.**

Since `φ(i) = (g_0 + ⋯ + g_{i-1})/g_0` and `g_0 > 0`, the value `φ(i)` is a natural number
precisely when `g_0` divides the partial sum `g_0 + ⋯ + g_{i-1}`.  Hasse–Arf asks this at every
lower break, so it is equivalent to the stated divisibility condition. -/
theorem hasseArf_iff_dvd {K L : Type*} [Field K] [Field L] [Algebra K L]
    (A : ValuationSubring L) [Finite ↥(A.decompositionSubgroup K)] :
    NK.Ramification.HasseArf (K := K) A ↔
      ∀ i : ℕ, NK.Ramification.LowerBreak (K := K) A i →
        NK.Ramification.lowerIndex (K := K) A 0 ∣
          ∑ j ∈ Finset.range i, NK.Ramification.lowerIndex (K := K) A j := by
  have hg0 : (lowerIndex (K := K) A 0 : ℚ) ≠ 0 := by
    exact_mod_cast Nat.pos_iff_ne_zero.mp (lowerIndex_zero_pos (K := K) A)
  constructor
  · intro h i hi
    obtain ⟨m, hm⟩ := h i hi
    have hmul := herbrand_mul_lowerIndex_zero (K := K) A i
    rw [hm] at hmul
    -- hmul : (↑g₀) * (↑m) = ∑ j ∈ range i, ↑(g j)
    refine ⟨m, ?_⟩
    exact Nat.cast_injective (R := ℚ) (by push_cast; exact hmul.symm)
  · intro h i hi
    obtain ⟨m, hm⟩ := h i hi
    refine ⟨m, ?_⟩
    rw [herbrand]
    have hnum : (∑ j ∈ Finset.range i, (lowerIndex (K := K) A j : ℚ))
        = (lowerIndex (K := K) A 0 : ℚ) * (m : ℚ) := by
      rw [← Nat.cast_sum, hm, Nat.cast_mul]
    rw [hnum]
    exact mul_div_cancel_left₀ _ hg0

end NK.Ramification
