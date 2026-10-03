import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.wordOfDefs
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.twoLetter_cycle_decor

namespace Work.OROneRel

/-- The weight `tlW p q` at the first generator: `tlW p q 0 = q`. -/
theorem tlW_zero (p q : ℕ) : tlW p q 0 = (q : ℤ) := by
  simp [tlW]

/-- The weight `tlW p q` at the second generator: `tlW p q 1 = -p`. -/
theorem tlW_one (p q : ℕ) : tlW p q 1 = -(p : ℤ) := by
  simp only [tlW]
  rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]

/-- The reduced word of the two-letter relator `tlU p q = a ^ p * b ^ q`: the two blocks are already
reduced, and nothing cancels at the junction because the two generators are distinct. -/
theorem wordOf_tlU (p q : ℕ) :
    wordOf (tlU p q) =
      List.replicate p ((0 : Fin 2), true) ++ List.replicate q ((1 : Fin 2), true) := by
  show Work.OROneRel.wordOf (FreeGroup.of (0 : Fin 2) ^ p * FreeGroup.of (1 : Fin 2) ^ q) = _
  exact wordOf_of_pow_mul_of_pow (0 : Fin 2) (1 : Fin 2) (by decide) p q

/-- **The decorated walk of the two-letter cycle, at an arbitrary starting level.**  Decorating the
reduced word of `tlU p q = a ^ p * b ^ q` by the weight `tlW p q` (`a ↦ q`, `b ↦ -p`) and starting
the running level at `N`, the `p` copies of `a` are read at the levels `N, N + q, …, N + (p-1) q`
and the `q` copies of `b` are read at the levels `N + p q, N + p q - p, …, N + p q - (q-1) p`.

This is the level-`N` form of `decor_two_letter` (which is the case `N = 0`): the running level
starts at `N` instead of `0` and every read level is shifted by `N`. -/
theorem decor_tlU_tlW_at (p q : ℕ) (N : ℤ) :
    Work.OROneRel.decor (Work.OROneRel.tlW p q) N (Work.OROneRel.wordOf (Work.OROneRel.tlU p q))
      = List.ofFn (fun j : Fin p => (((0 : Fin 2), N + (j : ℤ) * (q : ℤ)), true))
        ++ List.ofFn (fun k : Fin q =>
            (((1 : Fin 2), N + (p : ℤ) * (q : ℤ) - (k : ℤ) * (p : ℤ)), true)) := by
  classical
  have h1 : decor (tlW p q) N (List.replicate p ((0 : Fin 2), true))
      = List.ofFn (fun j : Fin p => (((0 : Fin 2), N + (j : ℤ) * (q : ℤ)), true)) := by
    rw [decor_replicate_true, tlW_zero]
  have hlsig : lsig (tlW p q) (List.replicate p ((0 : Fin 2), true)) = (p : ℤ) * (q : ℤ) := by
    rw [lsig_replicate_true, tlW_zero]
  have h2 : decor (tlW p q) (N + (p : ℤ) * (q : ℤ)) (List.replicate q ((1 : Fin 2), true))
      = List.ofFn (fun k : Fin q =>
            (((1 : Fin 2), N + (p : ℤ) * (q : ℤ) - (k : ℤ) * (p : ℤ)), true)) := by
    rw [decor_replicate_true, tlW_one]
    rw [List.ofFn_injective.eq_iff]
    funext k
    simp only [Prod.mk.injEq, true_and, and_true]
    ring
  rw [wordOf_tlU, decor_append, h1, hlsig, h2]

end Work.OROneRel
