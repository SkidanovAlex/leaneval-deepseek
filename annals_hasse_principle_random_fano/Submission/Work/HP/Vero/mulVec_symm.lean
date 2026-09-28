import Mathlib
import Submission.Work.HP.Vero.MulDefs

namespace Work.HP.Vero

theorem mulVec_symm {a b d n : ℕ} {R : Type*} [CommSemiring R]
    (A : Mon a n → R) (B : Mon b n → R) :
    mulVec a b d A B = mulVec b a d B A := by
  funext M
  simp only [mulVec]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl (fun q _ => ?_)
  refine Finset.sum_congr rfl (fun p _ => ?_)
  by_cases h : ∀ i, (p.1 i : ℕ) + (q.1 i : ℕ) = (M.1 i : ℕ)
  · have h' : ∀ i, (q.1 i : ℕ) + (p.1 i : ℕ) = (M.1 i : ℕ) :=
      fun i => by rw [Nat.add_comm]; exact h i
    simp [h, h', mul_comm]
  · have h' : ¬ ∀ i, (q.1 i : ℕ) + (p.1 i : ℕ) = (M.1 i : ℕ) := by
      intro hc
      exact h (fun i => by have := hc i; rw [Nat.add_comm] at this; exact this)
    simp [h, h']

end Work.HP.Vero
