import Mathlib

namespace Work.DSCOH

theorem negOne_pow_card_filter_erase_gen {ι : Type*} [DecidableEq ι] [LinearOrder ι]
    (T : Finset ι) {i j : ι} (hi : i ∈ T) (hj : j ∈ T) (hij : i ≠ j) :
    ((-1 : ℤ) ^ (T.filter (fun k => k < i)).card) *
        ((-1 : ℤ) ^ ((T.erase i).filter (fun k => k < j)).card)
      + ((-1 : ℤ) ^ (T.filter (fun k => k < j)).card) *
        ((-1 : ℤ) ^ ((T.erase j).filter (fun k => k < i)).card) = 0 := by
  -- The two summands are opposite signs: for `i < j` the exponents are `a + (c-1)`
  -- and `c + a`; for `j < i` they are `a + c` and `c + (a-1)`.
  have sign_key : ∀ a b : ℕ, 1 ≤ b →
      (-1 : ℤ)^a * (-1)^(b-1) + (-1)^b * (-1)^a = 0 := by
    intro a b hb
    have hab : a + (b - 1) + 1 = a + b := by omega
    have key : (-1:ℤ)^(b+a) = -(-1:ℤ)^(a+(b-1)) := by
      rw [add_comm b a, ← hab, pow_succ]; ring
    rw [← pow_add, ← pow_add, key]; ring
  rcases lt_or_gt_of_ne hij with h | h
  · -- Case `i < j`
    have hiB : i ∈ T.filter (fun k => k < j) := Finset.mem_filter.mpr ⟨hi, h⟩
    have hjA : j ∉ T.filter (fun k => k < i) := by
      intro hm; exact (not_lt.mpr h.le) (Finset.mem_filter.mp hm).2
    have hC1 : ((T.erase i).filter (fun k => k < j)).card
        = (T.filter (fun k => k < j)).card - 1 := by
      rw [Finset.filter_erase]; exact Finset.card_erase_of_mem hiB
    have hC2 : ((T.erase j).filter (fun k => k < i)).card
        = (T.filter (fun k => k < i)).card := by
      rw [Finset.filter_erase, Finset.erase_eq_of_notMem hjA]
    rw [hC1, hC2]
    exact sign_key _ _ (Finset.card_pos.mpr ⟨i, hiB⟩)
  · -- Case `j < i`
    have hjA : j ∈ T.filter (fun k => k < i) := Finset.mem_filter.mpr ⟨hj, h⟩
    have hiB : i ∉ T.filter (fun k => k < j) := by
      intro hm; exact (not_lt.mpr h.le) (Finset.mem_filter.mp hm).2
    have hC1 : ((T.erase i).filter (fun k => k < j)).card
        = (T.filter (fun k => k < j)).card := by
      rw [Finset.filter_erase, Finset.erase_eq_of_notMem hiB]
    have hC2 : ((T.erase j).filter (fun k => k < i)).card
        = (T.filter (fun k => k < i)).card - 1 := by
      rw [Finset.filter_erase]; exact Finset.card_erase_of_mem hjA
    rw [hC1, hC2, add_comm]
    exact sign_key _ _ (Finset.card_pos.mpr ⟨j, hjA⟩)

end Work.DSCOH
