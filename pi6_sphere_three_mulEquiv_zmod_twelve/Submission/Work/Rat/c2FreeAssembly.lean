import Mathlib
import Submission.Work.Stems.c2EvenStepLocal
import Submission.Work.Stems.c2OddStepLocal
import Submission.Work.Stems.c2OddBase

/-!
# The free-top `C2` mutual induction, assembled

`Work.Stems.Engine.C2evenFree c` / `C2oddFree c` (`Submission/Work/Stems/Engine/C2FreeTop.lean`)
are the corrected, free-top forms of the `K(ℤ,n)` layer of the Serre blueprint, whose mutual
induction *does* close (with `c = 1`).  The two steps are proved level-locally in

* `Work.Stems.evenStepLocal` (the even clause at level `j` from the odd clause at level `2j-1`),
* `Work.Stems.oddStepLocal` (the odd clause at level `2j+1` from the even clause at level `j`),
* `Work.Stems.oddClauseOne` (the level-1 base case).

This file runs the strong induction on the level that combines them into the two interfaces.
-/

open CategoryTheory CategoryTheory.Limits
open scoped Topology

namespace Work.Rat

noncomputable section

/-- **The level-`1` odd clause**, as an unfold of `Work.Stems.oddClauseOne`. -/
theorem oddClause_one (c N : ℕ) : Work.Stems.OddClause c 1 (by omega) N := by
  intro X _ pt hX
  obtain ⟨hgen, hvan⟩ := Work.Stems.oddClauseOne X pt N hX (Work.Stems.bottomCellOne X pt N hX)
  exact ⟨hgen, fun d hd hdN hdn => hvan d hd (by omega) hdn⟩

/-- **The mutual induction, level by level.**  For every `j`, the even clause at level `j+1` and the
odd clause at level `2j+1`. -/
theorem c2FreeKey (c : ℕ) (hE3b : Work.Serre.SerreE3b) (hE3a : Work.Serre.SerreE3a) :
    ∀ j : ℕ, (∀ N : ℕ, Work.Stems.EvenClause c (j + 1) (by omega) N) ∧
      (∀ N : ℕ, Work.Stems.OddClause c (2 * j + 1) (by omega) N) := by
  intro j
  induction j with
  | zero =>
    refine ⟨?_, ?_⟩
    · intro N
      exact Work.Stems.evenStepLocal c hE3b 1 (by omega) 1 (by omega) (fun M => oddClause_one c M) N
    · intro N
      exact oddClause_one c N
  | succ j ih =>
    have hOdd : ∀ N : ℕ, Work.Stems.OddClause c (2 * (j + 1) + 1) (by omega) N :=
      fun N => Work.Stems.oddStepLocal c hE3a (j + 1) (by omega) (fun M => ih.1 M) N
    have hEven : ∀ N : ℕ, Work.Stems.EvenClause c (j + 1 + 1) (by omega) N := by
      intro N
      exact Work.Stems.evenStepLocal c hE3b (j + 1 + 1) (by omega) (2 * (j + 1) + 1)
        (by omega) hOdd N
    exact ⟨hEven, hOdd⟩

/-- **`C2evenFree c` and `C2oddFree c` from the two steps.** -/
theorem c2Free_both (c : ℕ) (hE3b : Work.Serre.SerreE3b) (hE3a : Work.Serre.SerreE3a) :
    Work.Stems.Engine.C2evenFree c ∧ Work.Stems.Engine.C2oddFree c := by
  have hkey := c2FreeKey c hE3b hE3a
  constructor
  · intro j hj N X _ pt hX
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    exact (hkey j').1 N X pt hX
  · intro n hn hodd N X _ pt hX
    rcases hodd with ⟨j, rfl⟩
    exact (hkey j).2 N X pt hX

end

end Work.Rat
