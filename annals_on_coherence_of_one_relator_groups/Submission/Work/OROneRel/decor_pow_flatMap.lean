/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The decoration of a power of a cyclically reduced relator

`decor c i L` is the running-weight decoration of a word `L`: the letter `(x, true)` read at running
weight `i` becomes the symbol `((x, i), true)` and the letter `(x, false)` read at running weight `i`
becomes `((x, i - c x), false)`.  Equivalently, `decor` is the fold that walks along `L` and shifts
the level by `lsig c` of the part already read.

The main point of this file is the *multiplicativity* of `decor` with respect to taking powers of a
cyclically reduced relator: if `cohom c u = 1`, i.e. the total `c`-weight of `u` vanishes
(`lsig c (wordOf u) = 0`), then the decoration of `u ^ n` is the concatenation of `n` copies of the
decoration of `u`:

`decor c 0 (wordOf (u ^ n)) = (replicate n (decor c 0 (wordOf u))).flatten`.

Two ingredients go in:

* `wordOf_pow_flatten` (`Submission.Work.OROneRel.wordOf_pow_flatten`): for a cyclically reduced
  `u`, `wordOf (u ^ n)` is the concatenation of `n` copies of `wordOf u` -- this is exactly where
  cyclic reducedness (the hypothesis `hcyc`) is used;
* `lsig_wordOf_eq_zero` (`Submission.Work.OROneRel.lsig_wordOf_eq_zero`): `cohom c u = 1` forces the
  vanishing of the weight, so that the running level of `decor` returns to `0` after each copy.

The combinatorial content is then the additivity of `decor` under concatenation
(`decor_append`: concatenating words adds the weights, so the second block is decorated starting at
the level reached at the end of the first) together with the immediate consequence
`decor_flatten_replicate` for repeated blocks.
-/

import Mathlib
import Submission.Work.OROneRel.MagnusGenDefs
import Submission.Work.OROneRel.wordOfDefs
import Submission.Work.OROneRel.wordOf_pow_flatten
import Submission.Work.OROneRel.lsig_wordOf_eq_zero

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ### Additivity of the weight -/

/-- The weight `lsig` is additive under concatenation of words. -/
theorem decor_lsig_append (c : α → ℤ) (L₁ L₂ : List (α × Bool)) :
    lsig c (L₁ ++ L₂) = lsig c L₁ + lsig c L₂ := by
  simp only [lsig, List.map_append, List.sum_append]

/-- The weight of a word beginning with a positive letter. -/
theorem decor_lsig_cons_true (c : α → ℤ) (a : α) (L : List (α × Bool)) :
    lsig c ((a, true) :: L) = c a + lsig c L := rfl

/-- The weight of a word beginning with a negative letter. -/
theorem decor_lsig_cons_false (c : α → ℤ) (a : α) (L : List (α × Bool)) :
    lsig c ((a, false) :: L) = -c a + lsig c L := rfl

/-! ### Additivity of the decoration -/

/-- **The decoration is additive in the word.**  Because the running level of `decor` advances by
the weight of the letters already read, the decoration of `L₁ ++ L₂` is the decoration of `L₁`
followed by the decoration of `L₂` started at the level `i + lsig c L₁` reached at the end of
`L₁`. -/
theorem decor_append (c : α → ℤ) (i : ℤ) (L₁ L₂ : List (α × Bool)) :
    Work.OROneRel.decor c i (L₁ ++ L₂) =
      Work.OROneRel.decor c i L₁ ++ Work.OROneRel.decor c (i + lsig c L₁) L₂ := by
  induction L₁ generalizing i with
  | nil => simp [decor, lsig]
  | cons p L ih =>
    obtain ⟨a, b⟩ := p
    cases b
    · rw [List.cons_append,
        show decor c i ((a, false) :: (L ++ L₂)) =
          ((a, i - c a), false) :: decor c (i - c a) (L ++ L₂) from rfl,
        show decor c i ((a, false) :: L) =
          ((a, i - c a), false) :: decor c (i - c a) L from rfl,
        List.cons_append, ih (i - c a), decor_lsig_cons_false]
      congr 1
      ring_nf
    · rw [List.cons_append,
        show decor c i ((a, true) :: (L ++ L₂)) =
          ((a, i), true) :: decor c (i + c a) (L ++ L₂) from rfl,
        show decor c i ((a, true) :: L) =
          ((a, i), true) :: decor c (i + c a) L from rfl,
        List.cons_append, ih (i + c a), decor_lsig_cons_true]
      congr 1
      ring_nf

/-- **The decoration of a repeated block.**  If a word `L` has vanishing total weight, then the
decoration of the concatenation of `n` copies of `L` is the concatenation of `n` copies of the
decoration of `L` (each copy starting afresh at level `0`). -/
theorem decor_flatten_replicate (c : α → ℤ) (L : List (α × Bool)) (hL : lsig c L = 0) (n : ℕ) :
    Work.OROneRel.decor c 0 (List.flatten (List.replicate n L)) =
      List.flatten (List.replicate n (Work.OROneRel.decor c 0 L)) := by
  induction n with
  | zero => simp [decor]
  | succ n ih =>
    simp only [List.replicate_succ, List.flatten_cons]
    rw [decor_append, hL, add_zero, ih]

/-! ### The decoration of a power of a cyclically reduced relator -/

theorem decor_pow_flatMap {α : Type u} (c : α → ℤ) (u : FreeGroup α) (n : ℕ)
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator u)
    (hu : Work.OROneRel.cohom c u = 1) :
    Work.OROneRel.decor c 0 (Work.OROneRel.wordOf (u ^ n))
      = List.flatten (List.replicate n (Work.OROneRel.decor c 0 (Work.OROneRel.wordOf u))) := by
  classical
  rw [wordOf_pow_flatten u n hcyc,
    decor_flatten_replicate c (wordOf u) (lsig_wordOf_eq_zero c u hu) n]

end Work.OROneRel
