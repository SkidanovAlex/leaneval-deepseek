import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.GaugeDefs
import Submission.Work.OROneRel.wordOfDefs
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.walkDefs
import Submission.Work.OROneRel.walk_mk_decompose
import Submission.Work.OROneRel.walk_mem
import Submission.Work.OROneRel.cohom_mk
import Submission.Work.OROneRel.decor_tlU_tlW_at
import Submission.Work.OROneRel.twoLetter_cycle_decor
import Submission.Work.OROneRel.decor_pow_flatMap
import Submission.Work.OROneRel.decor_flatten_replicate_gen
import Submission.Work.OROneRel.wordOf_pow_flatten
import Submission.Work.OROneRel.lsig_wordOf_eq_zero
import Submission.Work.OROneRel.exists_common_power

/-!
# The decorated walk of the two-letter cycle steps up one window

This file proves `Work.OROneRel.walkWord_step_up`, the "step up" half of the identification of the
band windows of the two-letter one-relator complex with the `ℤ`-cover.

Let `tlU p q = a ^ p * b ^ q` (`p, q ≥ 1`), let `tlW p q` be the weight `a ↦ q`, `b ↦ -p` which
kills it, and let `b : ℤ` be an integer with `b + 1 ≥ p q` (`hm`).  Starting the decorated walk of
`tlU p q` at the level `N = b + 1 - p q` places the walk inside the window `[0, b + 1]`: the `a`-block
climbs from `N ≥ 0` to `N + p q = b + 1`, and the `b`-block climbs back down to `N`, never exceeding
`b + 1`.  The *last* `a`-symbol (read at level `b + 1 - q`, stepping up to `b + 1`) and the *first*
`b`-symbol (read at level `b + 1`) are the only two symbols that leave the window `[0, b]`; deleting
them leaves two words `walkA p q N` and `walkB p q N` all of whose symbols lie in the window, hence
two elements of `Subgroup.closure (FreeGroup.of '' winE (tlW p q) 0 b)`.  Since the walk of
`tlU p q ^ l` is the `l`-fold repetition of the walk of `tlU p q` (`mk_decor_tlU_pow`, via the
vanishing of the total weight), the decorated word of `tlU p q ^ l` is the `l`-th power of the word

  `walkA * (0, b + 1 - q) * (1, b + 1) * walkB`,

which is exactly the statement.

The two ingredients are `Work.OROneRel.walk_mk_decompose` (the one-copy splitting of the decorated
walk) and `Work.OROneRel.walk_mem` (the window membership of the two interior factors); everything
else is proved here.
-/

namespace Work.OROneRel

/-- **The weight `tlW p q` kills the two-letter relator.**  The exponent sum of `a` is `q` and of
`b` is `-p`; along `a ^ p * b ^ q` these contribute `p q` and `-q p`. -/
theorem cohom_tlW_tlU (p q : ℕ) : cohom (tlW p q) (tlU p q) = 1 := by
  rw [← mk_wordOf (tlU p q), cohom_mk, wordOf_tlU, decor_lsig_append, lsig_replicate_true,
    lsig_replicate_true, tlW_zero, tlW_one]
  have h : (p : ℤ) * (q : ℤ) + (q : ℤ) * (-(p : ℤ)) = 0 := by ring
  rw [h]
  simp

/-- **The decorated walk of the `l`-th power is the `l`-th power of the decorated walk.**  The walk
of `tlU p q` at starting level `N` returns to the level `N` (the total weight vanishes,
`cohom_tlW_tlU`), so the `l`-fold repetition of the walk of `tlU p q` is precisely the walk of
`tlU p q ^ l`. -/
theorem mk_decor_tlU_pow (p q l : ℕ) (hp : 1 ≤ p) (hq : 1 ≤ q) (N : ℤ) :
    FreeGroup.mk (decor (tlW p q) N (wordOf (tlU p q ^ l))) =
      (FreeGroup.mk (decor (tlW p q) N (wordOf (tlU p q)))) ^ l := by
  rw [wordOf_pow_flatten (tlU p q) l (tlU_isCyclicallyReduced p q hp hq),
    decor_flatten_replicate_at (tlW p q) (wordOf (tlU p q))
      (lsig_wordOf_eq_zero (tlW p q) (tlU p q) (cohom_tlW_tlU p q)) N l,
    mk_flatten_replicate l (decor (tlW p q) N (wordOf (tlU p q)))]

theorem walkWord_step_up {p q l : ℕ} (hp : 1 ≤ p) (hq : 1 ≤ q) (b : ℤ)
    (hm : 0 ≤ b + 1 - (p:ℤ)*(q:ℤ)) :
    ∃ A B : FreeGroup (Fin 2 × ℤ),
      A ∈ Subgroup.closure (FreeGroup.of '' Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 b) ∧
      B ∈ Subgroup.closure (FreeGroup.of '' Work.OROneRel.winE (Work.OROneRel.tlW p q) 0 b) ∧
      FreeGroup.mk (Work.OROneRel.decor (Work.OROneRel.tlW p q) (b + 1 - (p:ℤ)*(q:ℤ))
          (Work.OROneRel.wordOf (Work.OROneRel.tlU p q ^ l))) =
        (A * FreeGroup.of ((0 : Fin 2), b + 1 - (q : ℤ)) *
          FreeGroup.of ((1 : Fin 2), b + 1) * B) ^ l := by
  obtain ⟨hmemA, hmemB⟩ := walk_mem hp hq b hm
  refine ⟨walkA p q (b + 1 - (p:ℤ)*(q:ℤ)), walkB p q (b + 1 - (p:ℤ)*(q:ℤ)),
    hmemA, hmemB, ?_⟩
  rw [mk_decor_tlU_pow p q l hp hq (b + 1 - (p:ℤ)*(q:ℤ)),
    walk_mk_decompose hp hq (b + 1 - (p:ℤ)*(q:ℤ))]
  congr 1
  congr 1
  congr 1
  · congr 1
    push_cast
    ring
  · congr 1
    ring

end Work.OROneRel
