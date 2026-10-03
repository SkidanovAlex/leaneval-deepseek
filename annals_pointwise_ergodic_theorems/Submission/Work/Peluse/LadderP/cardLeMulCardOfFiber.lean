import Mathlib

namespace Work.Peluse.LadderP

/-- If every element of `s` maps into `T` under `f` and every fibre of `f` over `T` has at most `K` elements of `s`, then `s.card ≤ K * T.card`. -/
theorem cardLeMulCardOfFiber {α β : Type*} [DecidableEq β] {s : Finset α} {f : α → β}
    {T : Finset β} {K : ℕ} (hmem : ∀ x ∈ s, f x ∈ T)
    (hfib : ∀ y ∈ T, (s.filter (fun x => f x = y)).card ≤ K) : s.card ≤ K * T.card := by
  calc s.card = ∑ y ∈ T, (s.filter (fun x => f x = y)).card :=
        Finset.card_eq_sum_card_fiberwise hmem
    _ ≤ ∑ _y ∈ T, K := Finset.sum_le_sum hfib
    _ = K * T.card := by
        rw [Finset.sum_const, Nat.mul_comm]
        simp

end Work.Peluse.LadderP
