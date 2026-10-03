import Mathlib
import Submission.Work.Peluse.SwapC.concatState

/-!
# Vocabulary for the bookkeeping of the depth-first refinement of `{0,1}^s`

`Work.Peluse.SwapC.cproc s k` is the subdivision of `{0,1}^s` after `k` applications of
`csplitFirst`, each split replacing the first leaf of depth `< s` by its two children
(`CLeaf.children`).  This file collects the vocabulary used to state and prove the bookkeeping
facts:

* `Agree x l` — the point `x` lies in the cell of the leaf `l` (it agrees with `l.str` on the
  first `l.dep` coordinates);
* `Covers Λ` — the cells of the leaves of `Λ` cover `{0,1}^s`;
* `PairDisj Λ` — two leaves of `Λ` whose cells meet are equal (`Λ` still possibly with repeated
  leaves, but its distinct leaves have disjoint cells);
* `IsSubdiv Λ ↔ Covers Λ ∧ PairDisj Λ` (proved in `Work.Peluse.SwapC.cellTheory`);
* `HasSplit Λ` — some leaf of `Λ` has depth `< s`;
* `cellSum Λ` — the sum of the cell sizes `2 ^ (s - l.dep)` over the leaves; for a subdivision
  with `Nodup` leaves this is `2 ^ s`.
-/

set_option autoImplicit false

open scoped BigOperators

namespace Work.Peluse.SwapC

/-- The point `x` lies in the cell of the leaf `l`: it agrees with `l.str` on the first `l.dep`
coordinates. -/
def Agree {s : ℕ} (x : Fin s → Bool) (l : CLeaf s) : Prop :=
  ∀ i : Fin s, i.val < l.dep → l.str i = x i

/-- The cells of the leaves of `Λ` cover `{0,1}^s`. -/
def Covers {s : ℕ} (Λ : List (CLeaf s)) : Prop :=
  ∀ x : Fin s → Bool, ∃ l ∈ Λ, Agree x l

/-- Distinct leaves of `Λ` have disjoint cells. -/
def PairDisj {s : ℕ} (Λ : List (CLeaf s)) : Prop :=
  ∀ l₁ ∈ Λ, ∀ l₂ ∈ Λ, (∃ x : Fin s → Bool, Agree x l₁ ∧ Agree x l₂) → l₁ = l₂

/-- Some leaf of `Λ` has depth `< s`, i.e. the depth-first process has not finished. -/
def HasSplit {s : ℕ} (Λ : List (CLeaf s)) : Prop :=
  ∃ l ∈ Λ, l.dep < s

/-- The sum of the cell sizes `2 ^ (s - l.dep)` over the leaves. -/
def cellSum {s : ℕ} (Λ : List (CLeaf s)) : ℕ :=
  (Λ.map (fun l => 2 ^ (s - l.dep))).sum

end Work.Peluse.SwapC
