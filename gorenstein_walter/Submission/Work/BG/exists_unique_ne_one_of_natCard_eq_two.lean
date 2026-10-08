import Mathlib

namespace Work.BG

theorem exists_unique_ne_one_of_natCard_eq_two {X : Type*} [Group X] (h : Nat.card X = 2) :
    ∃ a : X, a ≠ 1 ∧ a ^ 2 = 1 ∧ ∀ x : X, x = 1 ∨ x = a := by
  obtain ⟨x, y, hxy, hset⟩ := Nat.card_eq_two_iff.mp h
  have hmem : ∀ z : X, z = x ∨ z = y := by
    intro z
    have hz : z ∈ ({x, y} : Set X) := by rw [hset]; exact Set.mem_univ z
    simpa [Set.mem_insert_iff, Set.mem_singleton_iff] using hz
  rcases hmem 1 with h1 | h1
  · refine ⟨y, ?_, ?_, ?_⟩
    · intro hy; exact hxy (h1.symm.trans hy.symm)
    · rcases hmem (y ^ 2) with h2 | h2
      · rw [h2]; exact h1.symm
      · exfalso
        have hyy : y * y = y := by rwa [pow_two] at h2
        have hy1 : y = 1 := mul_right_cancel (by rw [hyy, one_mul])
        exact hxy (h1.symm.trans hy1.symm)
    · intro z
      rcases hmem z with hz | hz
      · exact Or.inl (hz.trans h1.symm)
      · exact Or.inr hz
  · refine ⟨x, ?_, ?_, ?_⟩
    · intro hx; exact hxy (hx.trans h1)
    · rcases hmem (x ^ 2) with h2 | h2
      · exfalso
        have hxx : x * x = x := by rwa [pow_two] at h2
        have hx1 : x = 1 := mul_right_cancel (by rw [hxx, one_mul])
        exact hxy (hx1.trans h1)
      · rw [h2]; exact h1.symm
    · intro z
      rcases hmem z with hz | hz
      · exact Or.inr hz
      · exact Or.inl (hz.trans h1.symm)

end Work.BG
