import Mathlib

namespace Work.TMC16Core.Core

/-- If a finset has at most one element and every term of the sum is at least `C ≤ 0`,
then the sum is at least `C` (the empty sum being `0`). -/
theorem coll_sum_card_le_one {ι : Type*} {s : Finset ι} {f : ι → ℝ} {C : ℝ}
    (hcard : s.card ≤ 1) (hC : C ≤ 0) (hf : ∀ i ∈ s, C ≤ f i) :
    C ≤ ∑ i ∈ s, f i := by
  rcases s.eq_empty_or_nonempty with h | ⟨i, hi⟩
  · subst h
    simpa using hC
  · have hs : s = {i} :=
      Finset.eq_singleton_iff_unique_mem.mpr
        ⟨hi, fun x hx => (Finset.card_le_one.mp hcard) x hx i hi⟩
    rw [hs, Finset.sum_singleton]
    exact hf i hi

end Work.TMC16Core.Core
