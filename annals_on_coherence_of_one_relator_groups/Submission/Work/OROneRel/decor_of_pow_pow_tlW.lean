import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.twoLetter_cycle_decor
import Submission.Work.OROneRel.wordOf_of_pow_mul_of_pow

namespace Work.OROneRel

/-- The decoration of `a ^ s * b ^ t` by the weight `tlW p q` (`a ↦ q`, `b ↦ -p`): the first block
`a ^ s` is decorated at levels `j * q` (`j < s`) and the second block `b ^ t` at levels
`s * q - k * p` (`k < t`). -/
theorem decor_of_pow_pow_tlW (p q s t : ℕ) :
    Work.OROneRel.decor (Work.OROneRel.tlW p q) 0
        (Work.OROneRel.wordOf (FreeGroup.of (0 : Fin 2) ^ s * FreeGroup.of (1 : Fin 2) ^ t))
      = List.ofFn (fun j : Fin s => (((0 : Fin 2), (j : ℤ) * (q : ℤ)), true))
        ++ List.ofFn (fun k : Fin t =>
            (((1 : Fin 2), (s : ℤ) * (q : ℤ) - (k : ℤ) * (p : ℤ)), true)) := by
  classical
  have hc0 : Work.OROneRel.tlW p q 0 = (q : ℤ) := by simp [Work.OROneRel.tlW]
  have hc1 : Work.OROneRel.tlW p q 1 = -(p : ℤ) := by
    simp only [Work.OROneRel.tlW]
    rw [if_neg (by decide : ¬ ((1 : Fin 2) = 0))]
  rw [wordOf_of_pow_mul_of_pow (0 : Fin 2) (1 : Fin 2) (by decide) s t,
    decor_append, decor_replicate_true, decor_replicate_true, lsig_replicate_true, hc0, hc1]
  congr 1
  · rw [List.ofFn_injective.eq_iff]
    funext j
    simp
  · rw [List.ofFn_injective.eq_iff]
    funext k
    simp only [Prod.mk.injEq, true_and, and_true, zero_add]
    ring

end Work.OROneRel
