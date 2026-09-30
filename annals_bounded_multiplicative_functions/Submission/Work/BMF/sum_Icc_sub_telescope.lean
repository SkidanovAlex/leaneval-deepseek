import Mathlib

set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false

namespace Work.BMF

theorem sum_Icc_sub_telescope {G : Type*} [AddCommGroup G] (w : ℕ → G) (a b : ℕ)
    (h : a ≤ b + 1) :
    ∑ n ∈ Finset.Icc a b, (w n - w (n + 1)) = w a - w (b + 1) := by
  revert a
  induction b with
  | zero =>
    intro a ha
    have : a = 0 ∨ a = 1 := by omega
    rcases this with rfl | rfl
    · simp
    · rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      simp
  | succ b ih =>
    intro a ha
    by_cases hle : a ≤ b + 1
    · rw [Finset.sum_Icc_succ_top hle, ih a hle]
      abel
    · have ha' : a = b + 2 := by omega
      subst ha'
      rw [Finset.Icc_eq_empty (by omega), Finset.sum_empty]
      simp

end Work.BMF
