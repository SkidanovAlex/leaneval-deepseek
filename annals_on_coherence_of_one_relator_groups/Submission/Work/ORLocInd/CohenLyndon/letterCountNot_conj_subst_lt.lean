import Mathlib
import Submission.Work.OROneRel.letterCountNot_conj_cyclicReduced_le
import Submission.Work.OROneRel.nt_lt_relatorNorm
import Submission.Work.OROneRel.nt_subst_toWord_le

/-!
# The Case-2 substitution shrinks the `t`-avoiding letter count of a cyclically reduced conjugate

Let `r` be a relator over the generating type `α` in which the letter `t` occurs, and let `v` be a
cyclically reduced conjugate of the substituted relator
`subst t x (σ_x r) (σ_t r) r` of Case 2 of the Freiheitssatz.  The main result of this file,

`Work.ORLocInd.CohenLyndon.letterCountNot_conj_subst_lt`,

says that `v` has strictly fewer letters different from `t` than `r` has letters:

`letterCountNot t v < relatorNorm r`.

This is the abstract inequality behind `Work.OROneRel.magRewRel_subst_lt` (which additionally
identifies `relatorNorm (magRewRel t v)` with `nt t v.toWord`): the Cohen--Lyndon induction of the
substitution step is applied to the Magnus rewriting of `v`, whose norm is `letterCountNot t v`.

The proof is a three-step chain of the landscape developed in `Work.OROneRel`:

* a cyclically reduced conjugate does not increase the count of letters different from `t`
  (`letterCountNot_conj_cyclicReduced_le`);
* the substitution `t ↦ t^p`, `x ↦ x · t^{-q}` never increases it either (`nt_subst_toWord_le`);
* and `nt t r.toWord < relatorNorm r`, since `t` occurs in `r` and the letters of `r` equal to `t`
  are not counted (`nt_lt_relatorNorm`).

The only mismatch to bridge between these lemmas is the `DecidableEq` instance with respect to which
`FreeGroup.toWord` is computed: `letterCountNot`/`nt` are instance-independent (`letterCountNot_eq_nt`
uses `Classical.decEq` internally), while `nt_subst_toWord_le` and `nt_lt_relatorNorm` are stated for
an ambient instance.  Since any two instances are equal (`DecidableEq α` is a subsingleton), this is
harmless; the two `private` lemmas below record it.
-/

set_option autoImplicit false

namespace Work.ORLocInd.CohenLyndon

universe u

/-- `FreeGroup.toWord` does not depend on the `DecidableEq` instance used to compute it: that
instance type is a subsingleton. -/
private lemma toWord_inst_congr {α : Type u} (i j : DecidableEq α) (x : FreeGroup α) :
    @FreeGroup.toWord α i x = @FreeGroup.toWord α j x := by
  rw [Subsingleton.elim i j]

/-- `letterCountNot` agrees with `nt` of the reduced word computed with any `DecidableEq`
instance. -/
private lemma letterCountNot_eq_nt_inst {α : Type u} (i : DecidableEq α) (t : α)
    (w : FreeGroup α) :
    Work.OROneRel.letterCountNot t w = Work.OROneRel.nt t (@FreeGroup.toWord α i w) := by
  rw [Work.OROneRel.letterCountNot_eq_nt, toWord_inst_congr (Classical.decEq α) i w]

theorem letterCountNot_conj_subst_lt {α : Type u} [DecidableEq α] (r : FreeGroup α) (t x : α)
    (ht : t ∈ Work.OROneRel.relatorLetters r) {v : FreeGroup α}
    (hcyc : Work.OROneRel.IsCyclicallyReducedRelator v)
    (hconj : IsConj v (Work.OROneRel.subst t x (Multiplicative.toAdd (Work.OROneRel.sigma x r))
      (Multiplicative.toAdd (Work.OROneRel.sigma t r)) r)) :
    Work.OROneRel.letterCountNot t v < Work.OROneRel.relatorNorm r := by
  -- Abbreviate the substituted relator (on which `v` is a cyclically reduced conjugate).
  set X : FreeGroup α := Work.OROneRel.subst t x (Multiplicative.toAdd (Work.OROneRel.sigma x r))
      (Multiplicative.toAdd (Work.OROneRel.sigma t r)) r with hX
  -- `hconj` is a conjugacy from `v` to `X`; `letterCountNot_conj_cyclicReduced_le` wants the
  -- other direction, and `IsConj` is symmetric.
  have hconj' : IsConj X v := hconj.symm
  -- Step 1: a cyclically reduced conjugate has no more non-`t` letters.
  have h1 : Work.OROneRel.letterCountNot t v ≤ Work.OROneRel.letterCountNot t X :=
    Work.OROneRel.letterCountNot_conj_cyclicReduced_le X v t hconj' hcyc
  -- Step 2: the substitution does not increase the number of non-`t` letters.
  have h2 : Work.OROneRel.letterCountNot t X ≤ Work.OROneRel.nt t r.toWord := by
    rw [letterCountNot_eq_nt_inst (inferInstance : DecidableEq α) t X, hX]
    exact Work.OROneRel.nt_subst_toWord_le t x _ _ r
  -- Step 3: `t` occurs in `r`, so the reference letter is itself not counted.
  have h3 : Work.OROneRel.nt t r.toWord < Work.OROneRel.relatorNorm r :=
    Work.OROneRel.nt_lt_relatorNorm ht
  omega

end Work.ORLocInd.CohenLyndon
