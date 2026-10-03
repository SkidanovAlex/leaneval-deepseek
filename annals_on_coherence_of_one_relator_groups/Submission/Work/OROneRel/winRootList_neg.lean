import Mathlib
import Submission.Work.OROneRel.reflectData

/-!
# `winRootList_neg`: the deleted walk word of the weight `-c` is the reflection of the walk word of `c`

The reflection `(x, i) ↦ (x, -i)` of the level graph (`reflectData.lean`) carries

* the walk of `u` at level `0` for the weight `-c` to the walk of `u` at level `0` for the weight
  `c` (`decor_neg_zero`),
* the window `[lo,hi]` to the window `[-hi,-lo]` (`mem_winE_neg`),
* the loop class of an edge for the weight `-c` to the loop class of the reflected edge for the
  reflected gauge `j ↦ Wt (-j)` (`coverClassAt_neg`),

and the alphabet `winBeta Wt (fun a => -c a) lo hi` to the alphabet
`winBeta (fun j => Wt (-j)) c (-hi) (-lo)` through `sigmaBeta`.  Hence the deleted walk word
`winRootList` is reflected too.

## The structure of the proof

`winRootList` is the `filterMap` of a step function (`winRootList_eq_stepL`), the decorated walk of
`-c` is the reflection under `reflSym` of the decorated walk of `c` (`decor_neg_zero`), and each
decorated letter is treated the same way on both sides (`winRootStepL_reflSym`).  The pointwise
comparison of lists under `reflSym` is converted with `List.filterMap_map` (`filterMap` of a `map`)
and `List.map_filterMap` (`map` of a `filterMap`).

The step function of `winRootList` and its two evaluation lemmas are restated here — they are
literally the anonymous function appearing in the definition of `winRootList` and the two branches
of its `if` — so that this leaf module does not have to import the telescoping identity
`Work.OROneRel.winRho_winRoot`.
-/

namespace Work.OROneRel

universe u

variable {α : Type u}

/-! ## The step function of `winRootList`, restated -/

/-- The function whose `filterMap` is `winRootList`: a decorated letter is kept -- with the sign of
its traversal -- exactly if its edge lies in the window and has non-trivial loop class. -/
noncomputable def winRootStepL (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) :
    ((α × ℤ) × Bool) → Option (winBeta Wt c lo hi × Bool) := by
  classical
  exact fun p => if h : coverEdge p ∈ winE c lo hi ∧ coverClassAt Wt c (coverEdge p) ≠ 1
    then some (⟨coverEdge p, h.1, h.2⟩, p.2) else none

/-- `winRootList` is the `filterMap` of `winRootStepL`. -/
theorem winRootList_eq_stepL (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (u : FreeGroup α) :
    winRootList Wt c lo hi u = (decor c 0 (wordOf u)).filterMap (winRootStepL Wt c lo hi) := by
  classical
  unfold winRootList winRootStepL
  rfl

/-- The value of `winRootStepL` on a decorated letter whose edge lies in the window and has
non-trivial loop class. -/
theorem winRootStepL_of (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (p : (α × ℤ) × Bool)
    (hp : coverEdge p ∈ winE c lo hi) (hcl : coverClassAt Wt c (coverEdge p) ≠ 1) :
    winRootStepL Wt c lo hi p = some (⟨coverEdge p, hp, hcl⟩, p.2) := by
  classical
  unfold winRootStepL
  rw [dif_pos ⟨hp, hcl⟩]

/-- The value of `winRootStepL` on a decorated letter whose edge is rejected. -/
theorem winRootStepL_none (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ) (p : (α × ℤ) × Bool)
    (h : ¬ (coverEdge p ∈ winE c lo hi ∧ coverClassAt Wt c (coverEdge p) ≠ 1)) :
    winRootStepL Wt c lo hi p = none := by
  classical
  unfold winRootStepL
  rw [dif_neg h]

/-! ## The pointwise comparison -/

/-- **The step function reflects.**  The step of the deleted walk word for the weight `-c` at the
reflected letter is the reflection through `sigmaBeta` of the step for the weight `c`, the reflected
gauge `j ↦ Wt (-j)` and the reflected window. -/
theorem winRootStepL_reflSym (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (p : (α × ℤ) × Bool) :
    winRootStepL Wt (fun a => -c a) lo hi (reflSym p)
      = Option.map (fun q => ((sigmaBeta Wt c lo hi).symm q.1, q.2))
          (winRootStepL (fun j => Wt (-j)) c (-hi) (-lo) p) := by
  classical
  by_cases h : coverEdge p ∈ winE c (-hi) (-lo) ∧
      coverClassAt (fun j => Wt (-j)) c (coverEdge p) ≠ 1
  · have hmem : coverEdge (reflSym p) ∈ winE (fun a => -c a) lo hi := by
      rw [coverEdge_reflSym]
      exact mem_winE_reflEdge.mpr h.1
    have hcls : coverClassAt Wt (fun a => -c a) (coverEdge (reflSym p)) ≠ 1 := by
      rw [coverEdge_reflSym, coverClassAt_reflEdge_neg Wt c (coverEdge p)]
      exact h.2
    have hval : (⟨coverEdge (reflSym p), hmem, hcls⟩ : winBeta Wt (fun a => -c a) lo hi)
        = (sigmaBeta Wt c lo hi).symm ⟨coverEdge p, h.1, h.2⟩ :=
      Subtype.ext (coverEdge_reflSym p)
    rw [winRootStepL_of Wt (fun a => -c a) lo hi (reflSym p) hmem hcls,
      winRootStepL_of (fun j => Wt (-j)) c (-hi) (-lo) p h.1 h.2]
    exact congrArg some (Prod.ext hval rfl)
  · have hnone : ¬ (coverEdge (reflSym p) ∈ winE (fun a => -c a) lo hi ∧
        coverClassAt Wt (fun a => -c a) (coverEdge (reflSym p)) ≠ 1) := by
      rintro ⟨hm, hc⟩
      simp only [coverEdge_reflSym] at hm hc
      exact h ⟨mem_winE_reflEdge.mp hm, by
        rw [← coverClassAt_reflEdge_neg Wt c (coverEdge p)]
        exact hc⟩
    rw [winRootStepL_none Wt (fun a => -c a) lo hi (reflSym p) hnone,
      winRootStepL_none (fun j => Wt (-j)) c (-hi) (-lo) p h]
    rfl

/-! ## The reflection of the deleted walk word -/

/-- **The reflection of the deleted walk word.**  The list of traversals of the walk of `u` whose edge lies in the window `[lo, hi]` of the weight `-c` and has non-trivial loop class is the reflection (through `sigmaBeta`) of the corresponding list for the weight `c`, the reflected gauge `j ↦ Wt (-j)` and the window `[-hi, -lo]`. -/
theorem winRootList_neg {α : Type*} (Wt : ℤ → FreeGroup α) (c : α → ℤ) (lo hi : ℤ)
    (u : FreeGroup α) :
    Work.OROneRel.winRootList Wt (fun a => -c a) lo hi u
      = (Work.OROneRel.winRootList (fun j => Wt (-j)) c (-hi) (-lo) u).map
          (fun p => ((Work.OROneRel.sigmaBeta Wt c lo hi).symm p.1, p.2)) := by
  classical
  rw [winRootList_eq_stepL Wt (fun a => -c a) lo hi u,
    winRootList_eq_stepL (fun j => Wt (-j)) c (-hi) (-lo) u,
    decor_neg_zero c (wordOf u), List.filterMap_map]
  rw [List.filterMap_congr
    (f := winRootStepL Wt (fun a => -c a) lo hi ∘ reflSym)
    (g := fun p => Option.map (fun q => ((sigmaBeta Wt c lo hi).symm q.1, q.2))
      (winRootStepL (fun j => Wt (-j)) c (-hi) (-lo) p))
    (l := decor c 0 (wordOf u))
    (fun p _ => by simpa only [Function.comp_apply] using winRootStepL_reflSym Wt c lo hi p)]
  rw [List.map_filterMap]

end Work.OROneRel
