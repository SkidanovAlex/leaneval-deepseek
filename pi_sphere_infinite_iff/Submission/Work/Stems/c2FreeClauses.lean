import Mathlib
import Submission.Work.Stems.Engine.C2FreeTop

/-!
# The free-top `C2` interfaces, level by level

*(Area STEMS.  See `Submission/Work/Stems/C2ODD_PLAN.md`, `C2ODD_STEP_STATE.md`,
`Engine/C2FreeTop.lean`.)*

`Work.Stems.Engine.C2evenFree c` / `C2oddFree c` quantify over **all** levels at once.  The two
mutual-induction steps, however, are *level-local*: the even step at level `j` uses the odd
statement at level `2j-1` only, and the odd step at level `2j+1` uses the even statement at level
`j` only.  This module splits the two interfaces into their level-`N` clauses, so that the mutual
induction can be run as an ordinary strong induction on the level (`Stems/c2FreeMain.lean`).

* `EvenClause c j hj N` — the clause of `C2evenFree c` at level `j` and top `N`;
* `OddClause c n hn N` — the clause of `C2oddFree c` at level `n` and top `N`.

The two `iff` lemmas record that the interfaces are the level-by-level conjunctions of the clauses,
so nothing is lost or added by the split.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Stems

noncomputable section

/-- **The clause of `C2evenFree c` at level `j` and top `N`**: a range model of `K(ℤ,2j)` through
degree `N` has `H_{2jk}(−;ℚ) ≅ ℚ` for `2jk < N - c·2j` and vanishing rational homology in the other
degrees `< N - c·2j`. -/
def EvenClause (c : ℕ) (j : ℕ) (hj : 1 ≤ j) (N : ℕ) : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (pt : X),
    Work.Serre.IsEMSpaceUpTo ℤ (2 * j) (by omega) N X pt →
    (∀ k : ℕ, 2 * j * k < N - c * (2 * j) →
      Nonempty (Work.Serre.ratH (TopCat.of X) (2 * j * k) ≅ ModuleCat.of ℚ ℚ)) ∧
    (∀ d : ℕ, d < N - c * (2 * j) → (∀ k : ℕ, d ≠ 2 * j * k) →
      IsZero (Work.Serre.ratH (TopCat.of X) d))

/-- **The clause of `C2oddFree c` at level `n` and top `N`**: a range model of `K(ℤ,n)` through
degree `N` (`n` odd) has `H_n(−;ℚ) ≅ ℚ` and vanishing rational homology in the other degrees
`0 < d < N - c·n`. -/
def OddClause (c : ℕ) (n : ℕ) (hn : 1 ≤ n) (N : ℕ) : Prop :=
  ∀ (X : Type) [TopologicalSpace X] (pt : X),
    Work.Serre.IsEMSpaceUpTo ℤ n (by omega) N X pt →
    Nonempty (Work.Serre.ratH (TopCat.of X) n ≅ ModuleCat.of ℚ ℚ) ∧
    (∀ d : ℕ, 0 < d → d < N - c * n → d ≠ n →
      IsZero (Work.Serre.ratH (TopCat.of X) d))

/-- **The even interface is the conjunction of its level clauses.** -/
theorem c2evenFree_iff (c : ℕ) :
    Work.Stems.Engine.C2evenFree c ↔ ∀ (j : ℕ) (hj : 1 ≤ j) (N : ℕ), EvenClause c j hj N :=
  Iff.rfl

/-- **The odd interface is the conjunction of its level clauses.** -/
theorem c2oddFree_iff (c : ℕ) :
    Work.Stems.Engine.C2oddFree c ↔ ∀ (n : ℕ) (hn : 1 ≤ n), Odd n → ∀ N : ℕ, OddClause c n hn N :=
  Iff.rfl

end

end Work.Stems
