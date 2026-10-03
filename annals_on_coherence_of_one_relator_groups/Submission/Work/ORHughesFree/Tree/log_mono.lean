/-
Copyright (c) 2025. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

# Monotonicity of the logarithm of a finite rooted tree

The tree order `Tree.le` of [DHS04, Lemma 3.3] (see `order_defs.lean` / `Log.lean`) is the
Dershowitz–Manna multiset order on the families of children.  The logarithm `log X` is the largest
element of `fam X` (`log_spec`).  Here we record that `log` is monotone for `Tree.le`:

* if `x < y` then `log x ≤ log y` (`le_log_of_lt`);
* consequently `x ≤ y` implies `log x ≤ log y` (`log_mono`), the statement
  [JZLA20, Lemma 4.3(ix)] (cf. `lt_of_log_lt`, the converse implication at the level of the
  strict order).

The argument is short.  Write `x < y` as `fam x = X + Y`, `fam y = X + Z` with `Z ≠ 0` and every
element of `Y` below some element of `Z` (the unfolding `lt_iff` of the recursive definition).
Let `a` be the maximum of `fam x = X + Y` and `b` the maximum of `fam y = X + Z`.

* If `a ∈ X ⊆ fam y` then `a ≤ b` because `b` is the maximum of `fam y`.
* If `a ∈ Y` there is `b' ∈ Z` with `a < b'`, and `b' ∈ fam y`, so `a ≤ b' ≤ b`.

The second case is where the strict order on the elements of `Z` is used; in the first case the
common part `X` needs no comparison at all.  This is exactly why the conclusion is `≤` and not `<`.
-/
import Mathlib
import Submission.Work.ORHughesFree.Tree.Log

set_option autoImplicit false

namespace Work.ORHughesFree.Tree

open Work.ORHughesFree

/-- **The logarithm is monotone for the strict tree order.**  If `x < y` and `log x = some a`,
`log y = some b` then `a ≤ b`.  (`x = 0` or `y = 0` are impossible under `x < y`, so the
hypotheses `log x = some a`, `log y = some b` lose nothing.) -/
theorem le_log_of_lt {x y a b : Tree} (hxy : lt x y) (hx : log x = some a)
    (hy : log y = some b) : le a b := by
  obtain ⟨hmemx, -⟩ := (log_spec x).2.1 a hx
  obtain ⟨-, hmaxy⟩ := (log_spec y).2.1 b hy
  obtain ⟨X, Y, Z, -, h1, h2, hstep⟩ := (lt_iff x y).mp hxy
  have ha : a ∈ X + Y := by rw [← h1]; exact hmemx
  rcases Multiset.mem_add.mp ha with haX | haY
  · -- `a` lies in the common part `X`, hence in `fam y` and below its maximum `b`.
    exact hmaxy a (by rw [h2]; exact Multiset.mem_add.mpr (Or.inl haX))
  · -- `a` is replaced in `fam y` by a strictly larger element `b' ∈ Z`, and `b' ≤ b`.
    obtain ⟨b', hb'Z, hab'⟩ := hstep a haY
    exact le_trans (le_of_lt hab')
      (hmaxy b' (by rw [h2]; exact Multiset.mem_add.mpr (Or.inr hb'Z)))

/-- **The logarithm is monotone.**  If `x ≤ y` and `log x = some a`, `log y = some b` then
`a ≤ b` ([JZLA20, Lemma 4.3(ix)]). -/
theorem log_mono {x y a b : Work.ORHughesFree.Tree}
    (hxy : Work.ORHughesFree.Tree.le x y)
    (hx : Work.ORHughesFree.Tree.log x = some a) (hy : Work.ORHughesFree.Tree.log y = some b) :
    Work.ORHughesFree.Tree.le a b := by
  rcases hxy with hxy | hxy
  · -- `x = y`, so `log x = log y` and hence `a = b`.
    subst hxy
    have hab : a = b := Option.some.inj (hx.symm.trans hy)
    rw [hab]
    exact le_refl b
  · exact le_log_of_lt hxy hx hy

end Work.ORHughesFree.Tree
