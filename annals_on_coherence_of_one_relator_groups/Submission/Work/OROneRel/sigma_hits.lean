import Mathlib

namespace Work.OROneRel

theorem sigma_hits (l : List ℤ) (hl : ∀ x ∈ l, x = 1 ∨ x = -1) :
    ∀ v : ℤ, ((0 ≤ v ∧ v ≤ l.sum) ∨ (l.sum ≤ v ∧ v ≤ 0)) →
      ∃ k : ℕ, k ≤ l.length ∧ (l.take k).sum = v := by
  revert hl
  induction l with
  | nil =>
    intro _hl v hv
    refine ⟨0, by simp, ?_⟩
    have hv0 : v = 0 := by
      rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · simp only [List.sum_nil] at h2; omega
      · simp only [List.sum_nil] at h1; omega
    simp [hv0]
  | cons a l ih =>
    intro hl v hv
    have ha : a = 1 ∨ a = -1 := hl a (by simp)
    have hl' : ∀ x ∈ l, x = 1 ∨ x = -1 := fun x hx => hl x (by simp [hx])
    by_cases hv0 : v = 0
    · exact ⟨0, by simp, by simp [hv0]⟩
    rcases lt_or_gt_of_ne hv0 with hvlt | hvgt
    · -- v < 0
      have hsum : (a :: l).sum ≤ v := by
        rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact absurd h1 (not_le.mpr hvlt)
        · exact h1
      have hb1 : l.sum ≤ v - a := by
        have : a + l.sum ≤ v := by simpa [List.sum_cons] using hsum
        omega
      have hb2 : v - a ≤ 0 := by
        rcases ha with h | h <;> simp [h] <;> omega
      obtain ⟨k, hk, hkval⟩ := ih hl' (v - a) (Or.inr ⟨hb1, hb2⟩)
      exact ⟨k + 1, by simp [List.length_cons]; omega, by
        rw [List.take_succ_cons, List.sum_cons, hkval]; ring⟩
    · -- 0 < v
      have hsum : v ≤ (a :: l).sum := by
        rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact h2
        · exact absurd h2 (not_le.mpr hvgt)
      have hb1 : 0 ≤ v - a := by
        rcases ha with h | h <;> simp [h] <;> omega
      have hb2 : v - a ≤ l.sum := by
        have : v ≤ a + l.sum := by simpa [List.sum_cons] using hsum
        omega
      obtain ⟨k, hk, hkval⟩ := ih hl' (v - a) (Or.inl ⟨hb1, hb2⟩)
      exact ⟨k + 1, by simp [List.length_cons]; omega, by
        rw [List.take_succ_cons, List.sum_cons, hkval]; ring⟩

end Work.OROneRel
