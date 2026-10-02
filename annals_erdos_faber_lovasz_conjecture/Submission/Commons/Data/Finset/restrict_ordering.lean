import Mathlib.Data.Finset.Sort

set_option linter.style.haveILetI false

namespace Commons.Data.Finset

/--
Given a finite type `α` with an enumeration `ord : α ≃ Fin k`, the restriction of
`ord` to a finset `s` can be relabelled as an order-preserving bijection onto
`Fin s.card`: there is `ord' : ↥s ≃ Fin s.card` such that `ord' a ≤ ord' b`
exactly when `ord a ≤ ord b`.
-/
theorem restrict_ordering {α : Type*} [Fintype α] [DecidableEq α] (s : Finset α) {k : ℕ}
    (ord : α ≃ Fin k) :
    ∃ ord' : ↥s ≃ Fin s.card,
      ∀ a b : ↥s, ((ord' a : ℕ) ≤ (ord' b : ℕ)) ↔ ((ord a.1 : ℕ) ≤ (ord b.1 : ℕ)) := by
  -- Pull back the linear order of `Fin k` along `ord` to obtain a linear order on `α`
  -- for which `ord` is order preserving by definition.
  letI : LinearOrder α := LinearOrder.lift' ord ord.injective
  -- The increasing bijection between `Fin s.card` and `s`, inverted, is the desired `ord'`.
  refine ⟨(Finset.orderIsoOfFin s rfl).symm.toEquiv, ?_⟩
  intro a b
  rw [← Fin.le_iff_val_le_val, ← Fin.le_iff_val_le_val]
  show (Finset.orderIsoOfFin s rfl).symm a ≤ (Finset.orderIsoOfFin s rfl).symm b ↔
      (ord a.1 : Fin k) ≤ ord b.1
  rw [OrderIso.le_iff_le]
  rfl

end Commons.Data.Finset