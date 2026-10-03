/-
Copyright: subproject `OROneRel` -- one-relator combinatorics (node N2).

# The Magnus rewriting preserves cyclic reducedness in the exponent-sum-zero case

The requested lemma

```
theorem rewrite_isCyclicallyReduced {α : Type u} (t : α) {L : List (α × Bool)}
    (hL : FreeGroup.IsCyclicallyReduced L) :
    FreeGroup.IsCyclicallyReduced (Work.OROneRel.rewrite t L)
```

is false without a hypothesis on the exponent sum of `t` (see
`Submission.Work.OROneRel.rewrite_isCyclicallyReduced` for the counterexample
`t · x · y · x⁻¹ · t`).  This file proves the correct statement, which carries the
hypothesis `sigmaList t L = 0` -- exactly the hypothesis available in the
Magnus--Moldavanskii step (`Submission.Work.OROneRel.mmStep_of_expsum_zero`), where the
relator `r` satisfies `eps t r = 0`.

The proof is short once one has the right characterization of cyclic reducedness:

* `isCyclicallyReduced_iff_isReduced_append_self`: `L` is cyclically reduced iff the doubled
  word `L ++ L` is reduced (immediate from `List.isChain_append`);
* the Magnus rewriting is additive over concatenation (`rewriteAux_append`), so when
  `sigmaList t L = 0` the doubling of `L` rewrites to the doubling of `rewrite t L`;
* `rewriteAux_isReduced` (`Submission.Work.OROneRel.rewrite_isReduced`) says that the rewriting of
  a reduced word is reduced, and `L ++ L` is reduced because `L` is cyclically reduced.
-/
import Mathlib
import Submission.Work.OROneRel.FreiheitssatzDefs
import Submission.Work.OROneRel.rewrite_isReduced
import Submission.Work.OROneRel.rewriteAux_append
import Submission.Work.OROneRel.MagnusRewrite

namespace Work.OROneRel

universe u

/-- A word is cyclically reduced exactly when its "doubling" `L ++ L` is reduced: by
`List.isChain_append` the chain condition on `L ++ L` is the conjunction of the chain conditions on
the two copies together with the wrap-around condition, which is precisely the second conjunct in
the definition of `FreeGroup.IsCyclicallyReduced`. -/
theorem isCyclicallyReduced_iff_isReduced_append_self {α : Type u} {L : List (α × Bool)} :
    FreeGroup.IsCyclicallyReduced L ↔ FreeGroup.IsReduced (L ++ L) := by
  simp only [FreeGroup.IsCyclicallyReduced, FreeGroup.IsReduced]
  rw [List.isChain_append]
  tauto

/-- **The Magnus rewriting of a cyclically reduced word of exponent sum zero is cyclically
reduced.**  This is the correct form of the requested lemma `rewrite_isCyclicallyReduced` (which is
false without the hypothesis `sigmaList t L = 0`). -/
theorem rewrite_isCyclicallyReduced_of_sigmaList_eq_zero {α : Type u} (t : α) {L : List (α × Bool)}
    (hL : FreeGroup.IsCyclicallyReduced L) (h0 : sigmaList t L = 0) :
    FreeGroup.IsCyclicallyReduced (rewrite t L) := by
  have hLL : FreeGroup.IsReduced (L ++ L) := isCyclicallyReduced_iff_isReduced_append_self.mp hL
  have hsplit : rewrite t (L ++ L) = rewrite t L ++ rewrite t L := by
    simp [rewrite, rewriteAux_append, h0]
  have hred : FreeGroup.IsReduced (rewrite t (L ++ L)) :=
    rewriteAux_isReduced t (L ++ L) hLL 0
  rw [hsplit] at hred
  exact isCyclicallyReduced_iff_isReduced_append_self.mpr hred

/-- `sigmaList` (the vocabulary of `FreiheitssatzDefs`) and `wordEps` (the vocabulary of
`MagnusRewrite`) are the same function: the exponent sum of the letters `t` in a word. -/
theorem sigmaList_eq_wordEps {α : Type u} (t : α) (L : List (α × Bool)) :
    sigmaList t L = wordEps t L := by
  classical
  induction L with
  | nil => simp [sigmaList, wordEps]
  | cons p L ih =>
    simp only [sigmaList, wordEps, List.map_cons, List.sum_cons] at ih ⊢
    rw [ih, letterSign]

/-- **The exponent-sum-zero case, in the vocabulary of `FreiheitssatzDefs` and
`Submission.Work.OROneRel.MagnusRewrite`.**  `sigmaList` and `wordEps` are the same function
(`sigmaList_eq_wordEps`); for a relator `r` with `IsCyclicallyReducedRelator r` and `eps t r = 0`
one applies this to `L := r.toWord` (see `isCyclicallyReducedRelator_rewrite_toWord`). -/
theorem rewrite_isCyclicallyReduced_of_wordEps_eq_zero {α : Type u} (t : α) {L : List (α × Bool)}
    (hL : FreeGroup.IsCyclicallyReduced L) (h0 : wordEps t L = 0) :
    FreeGroup.IsCyclicallyReduced (rewrite t L) :=
  rewrite_isCyclicallyReduced_of_sigmaList_eq_zero t hL (by rw [sigmaList_eq_wordEps]; exact h0)

section RelatorLevel

attribute [local instance] Classical.decEq

/-- The exponent-sum-zero case in the relator vocabulary of `Basic`/`MagnusRewrite`: the Magnus
rewriting of a cyclically reduced relator `r` with `eps t r = 0` is a cyclically reduced word in the
decorated alphabet `{x : α // x ≠ t} × ℤ`.  This is exactly what the Magnus--Moldavanskii step
needs: after rewriting, the induction hypothesis applies again to a cyclically reduced relator, now
in the smaller alphabet. -/
theorem isCyclicallyReducedRelator_rewrite_toWord {α : Type u} (t : α) {r : FreeGroup α}
    (hr : IsCyclicallyReducedRelator r) (h : eps t r = 0) :
    FreeGroup.IsCyclicallyReduced (rewrite t r.toWord) := by
  classical
  have hr' : FreeGroup.IsCyclicallyReduced r.toWord := by
    simpa [IsCyclicallyReducedRelator] using hr
  have h0 : sigmaList t r.toWord = 0 := by
    rw [sigmaList_eq_wordEps]
    simpa [eps] using h
  exact rewrite_isCyclicallyReduced_of_sigmaList_eq_zero t hr' h0

end RelatorLevel

end Work.OROneRel
