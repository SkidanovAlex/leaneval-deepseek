import Mathlib

namespace Work.CORE4.Counting

theorem XArithNat (qk' p1 : ℕ) (hq : 1 ≤ qk') (hp1 : 1 ≤ p1) :
    (p1 - 1) * qk' + 1 - p1 = (p1 - 1) * (qk' - 1) := by
  obtain ⟨m, rfl⟩ : ∃ m, p1 = m + 1 := ⟨p1 - 1, (Nat.sub_add_cancel hp1).symm⟩
  simp only [Nat.add_sub_cancel]
  rw [Nat.add_sub_add_right, Nat.mul_sub_left_distrib, Nat.mul_one]

end Work.CORE4.Counting
