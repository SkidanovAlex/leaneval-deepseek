import Mathlib
import Submission.Work.DSEQ0.SurjBasic

namespace Work.DSEQ0

universe u

theorem surjCech_top (k : ℕ) {M : Type u} [AddCommGroup M] (a : M) :
    ∃! f : (Fin (k + 1) → Fin (k + 1)) → M,
      (∀ x : Fin (k + 1) → Fin (k + 1), (Finset.univ.image x).card < k + 1 → f x = 0) ∧
      (∀ x : Fin (k + 2) → Fin (k + 1),
        ∑ j : Fin (k + 2), (-1 : ℤ) ^ (j : ℕ) • f (x ∘ Fin.succAbove j) = 0) ∧
      f id = a := by sorry

end Work.DSEQ0
