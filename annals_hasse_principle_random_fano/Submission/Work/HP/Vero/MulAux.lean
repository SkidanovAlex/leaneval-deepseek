import Mathlib
import Submission.Work.HP.Defs
import Submission.Work.HP.Vero.MulDefs

/-! The exponent condition characterising `mulVec` at matching degrees. -/
set_option autoImplicit false
noncomputable section
open Finset
namespace Work.HP.Vero

lemma cond_iff_eq_addMon {a b n : ℕ} (p : Mon a n) (q : Mon b n) (M : Mon (a + b) n) :
    (∀ i, (p.1 i : ℕ) + (q.1 i : ℕ) = (M.1 i : ℕ)) ↔ addMon p q = M := by
  constructor
  · intro h
    apply Subtype.ext
    funext i
    apply Fin.ext
    show (p.1 i : ℕ) + (q.1 i : ℕ) = (M.1 i : ℕ)
    exact h i
  · intro h i
    rw [← h, addMon_val]

theorem mulVec_apply_addMon {a b n : ℕ} {R : Type*} [CommSemiring R]
    (A : Mon a n → R) (B : Mon b n → R) (M : Mon (a + b) n) :
    mulVec a b (a + b) A B M
      = ∑ p : Mon a n, ∑ q : Mon b n,
          if addMon p q = M then A p * B q else 0 := by
  simp only [mulVec, cond_iff_eq_addMon]

end Work.HP.Vero
