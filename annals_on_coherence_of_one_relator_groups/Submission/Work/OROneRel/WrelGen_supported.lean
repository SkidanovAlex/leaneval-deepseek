import Mathlib
import Submission.Work.OROneRel.levelChain
import Submission.Work.OROneRel.decor_tlU_tlW_at
import Submission.Work.OROneRel.WrelUp_supported
import Submission.Work.OROneRel.WrelGen_decor_tlU_letters_mem

/-!
# The `2`-cell relators supported in a general level window `[a,b]` lie in the window subgroup

`WrelGen p q l a b` (`Submission.Work.OROneRel.levelChain`) is the set of the `2`-cell relators of
the level chain that are supported in the level window `[a,b]`:

`FreeGroup.mk (decor (tlW p q) m (wordOf (tlU p q ^ l)))`,  `a ≤ m`,  `m + p q ≤ b`.

The decorated walk of `u = tlU p q = a^p b^q` at level `m` climbs from the level `m` to the level
`m + p q` (the `p` copies of the first generator, each of weight `q`) and comes back down to `m`
(the `q` copies of the second generator, each of weight `-p`).  Hence *every* edge of the walk has
both endpoints in `[m, m + p q] ⊆ [a, b]`, i.e. lies in `Wedge p q a b`; each relator is therefore a
product of window generators.

This is the two-sided generalisation of `WrelUp_supported` (`[0,b]`, `0 ≤ m`) and of the private
`Wedge_decor_tlU_mem` of `WrelDown_supported` (window `[a,pq]`, `m ≤ 0`).  It is exactly the
hypothesis `hsup` of `chain_up_iterate_gen`, and hence the missing ingredient of the general
(two-sided) level chain.

The two ingredients are

* `WrelGen_decor_tlU_letters_mem` (proved elsewhere): every letter of the decorated walk of
  `tlU p q` at level `m` lies in `Wedge p q a b`, given `a ≤ m` and `m + p q ≤ b`;
* `wrelUp_mk_decor_pow` (`WrelUp_supported`): the class of the decorated walk of `tlU p q ^ l` is the
  `l`-th power of the class of the decorated walk of `tlU p q`, because the weight `tlW p q` kills
  `tlU p q` and `tlU p q` is cyclically reduced as soon as `p ≥ 1`.
-/

namespace Work.OROneRel

theorem WrelGen_supported (p q l : ℕ) (hp : 1 ≤ p) {a b : ℤ} :
    Work.OROneRel.WrelGen p q l a b ⊆
      Subgroup.closure (FreeGroup.of '' Work.OROneRel.Wedge p q a b) := by
  rintro w ⟨m, ham, hmb, rfl⟩
  rw [wrelUp_mk_decor_pow (tlW p q) (tlU p q) l m (wrelUp_tlU_isCyclicallyReduced p q hp)
    (wrelUp_lsig_tlW_tlU p q)]
  exact Subgroup.pow_mem _ (mk_mem_closure (WrelGen_decor_tlU_letters_mem p q hp ham hmb)) l

end Work.OROneRel
