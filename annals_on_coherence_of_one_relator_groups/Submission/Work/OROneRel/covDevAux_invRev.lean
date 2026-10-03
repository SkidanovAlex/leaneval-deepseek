import Mathlib
import Submission.Work.OROneRel.covCollapseDefs

namespace Work.OROneRel

theorem covDevAux_invRev {α : Type*} (W : ℤ → FreeGroup α) (c : α → ℤ) (i : ℤ) (L : List (α × Bool)) :
    Work.OROneRel.covDevAux W c (i + Work.OROneRel.lsig c L) (FreeGroup.invRev L) =
      (Work.OROneRel.covDevAux W c i L)⁻¹ := by
  induction L generalizing i with
  | nil => simp [covDevAux_nil, lsig_nil]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    rw [FreeGroup.invRev_cons, show FreeGroup.invRev [(a, b)] = [(a, !b)] from rfl, covDevAux_append]
    cases b
    · -- the letter is `(a, false)`: the reversed word starts with `(a, true)`
      simp only [Bool.not_false]
      rw [lsig_cons_false, show i + (-c a + lsig c L) = (i + -c a) + lsig c L by ring,
        ih (i + -c a), lsig_invRev, covDevAux_singleton_true,
        show (i + -c a) + lsig c L + -lsig c L = i + -c a by ring,
        show (i : ℤ) + -c a = i - c a by ring, covDevSym_true_eq_inv, covDevAux_cons_false,
        mul_inv_rev]
    · -- the letter is `(a, true)`: the reversed word starts with `(a, false)`
      simp only [Bool.not_true]
      rw [lsig_cons_true, show i + (c a + lsig c L) = (i + c a) + lsig c L by ring,
        ih (i + c a), lsig_invRev, covDevAux_singleton_false,
        show (i + c a) + lsig c L + -lsig c L = i + c a by ring,
        show (a, i + c a - c a) = (a, i) by rw [show i + c a - c a = i by ring],
        covDevSym_false_eq_inv, covDevAux_cons_true, mul_inv_rev]

end Work.OROneRel
