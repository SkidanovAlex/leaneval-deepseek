/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The one-copy decoration of the two-letter cycle: the two interior factors

The decorated walk of the two-letter relator `tlU p q = a ^ p * b ^ q` at a starting level `N`
(`decor_tlU_tlW_at`) is the list

`[(a, N + j * q) : j < p] ++ [(b, N + p * q - k * p) : k < q]`.

The *first* symbol of the second block and the *last* symbol of the first block are the two symbols
which fail to lie in a window `[0, b]` ending exactly at the top of the cycle: the last `a`-symbol is
read at level `N + (p - 1) q` and steps up to `N + p q`, and the first `b`-symbol is read at level
`N + p q`.  When the starting level is `N = b + 1 - p q` these are the levels `b + 1 - q` and
`b + 1`, i.e. exactly the two generators

`(0, b + 1 - q)`   and   `(1, b + 1)`

of the statement of `Work.OROneRel.walkWord_step_up`; every *other* symbol of the walk lies in the
window `winE (tlW p q) 0 b` and therefore in the subgroup
`Subgroup.closure (FreeGroup.of '' winE (tlW p q) 0 b)`.

This file fixes the two interior factors as explicit elements `walkA p q N` (the first `p - 1`
symbols of the `a`-block, with the last one deleted) and `walkB p q N` (the last `q - 1` symbols of
the `b`-block, with the first one deleted), together with the general list lemma
`mk_mem_closure`-style membership criterion used to place them in the subgroup.  The identifications

* `Work.OROneRel.walk_mk_decompose` -- `mk (decor ...) = walkA * of (0, N + (p-1) q) * of (1, N + p q) * walkB`,
* `Work.OROneRel.walkA_mem`, `Work.OROneRel.walkB_mem` -- the two factors lie in the window subgroup

are delegated separately (they import this file).
-/
import Mathlib
import Submission.Work.OROneRel.twoLetterTlDefs
import Submission.Work.OROneRel.winBasisDefs
import Submission.Work.OROneRel.wordOfDefs
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.decor_tlU_tlW_at

namespace Work.OROneRel

/-- **The `a`-part of the decorated two-letter cycle, minus its last symbol.**  The `a`-block of the
decorated walk of `tlU p q` at starting level `N` reads the letters `(0, true)` at the levels
`N, N + q, …, N + (p - 1) q`; this is the product of the first `p - 1` of them, i.e. the levels
`N, …, N + (p - 2) q`.  (For `p = 1` the list is empty and `walkA = 1`.) -/
noncomputable def walkA (p q : ℕ) (N : ℤ) : FreeGroup (Fin 2 × ℤ) :=
  FreeGroup.mk (List.ofFn fun j : Fin (p - 1) => (((0 : Fin 2), N + (j : ℤ) * (q : ℤ)), true))

/-- **The `b`-part of the decorated two-letter cycle, minus its first symbol.**  The `b`-block of the
decorated walk of `tlU p q` at starting level `N` reads the letters `(1, true)` at the levels
`N + p q, N + p q - p, …, N + p q - (q - 1) p`; this is the product of all but the first of them,
i.e. the levels `N + p q - k p` for `k = 1, …, q - 1`.  (For `q = 1` the list is empty and
`walkB = 1`.) -/
noncomputable def walkB (p q : ℕ) (N : ℤ) : FreeGroup (Fin 2 × ℤ) :=
  FreeGroup.mk (List.ofFn fun k : Fin (q - 1) =>
    (((1 : Fin 2), N + (p : ℤ) * (q : ℤ) - ((k : ℤ) + 1) * (p : ℤ)), true))

end Work.OROneRel
