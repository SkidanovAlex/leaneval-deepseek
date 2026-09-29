import Mathlib
import Submission.Work.Resample.auLoopDefs
import Submission.Work.Resample.auLoopHyp
import Submission.Work.Resample.auWinRec
import Submission.Work.Resample.auElemsElem
import Submission.Work.Resample.auWinSlice
import Submission.Work.Resample.auKSum
import Submission.Work.Resample.auSizes
import Submission.Work.Resample.auKArith
import Submission.Work.Resample.dropAppTakeCongr
import Submission.Work.Resample.auWinRecGen

namespace Work.Resample

/-- The window recurrence `auWinRec`, valid for **every** output index `k < t` (not only
`k + 1 < t`): the appended entry is the element of the run `auElems` exposed by the pointer, whose
position is the telescoping sum `∑_{j<k} (auK s t (j+1) - auK s t j) = auK s t k`.

The telescoping sum is silently the centre `auK s t k` (`auKSum`).  Writing `d` for the slide
`auK s t (k+1) - auK s t k ∈ {0,1}`:

* if `d = 0` the appended entry is truncated away by the final `take (auL p α)` (the dropped window
  already has length `auL p α`), so the identity follows from the definition of `auWin` alone;
* if `d = 1` the appended entry survives (the dropped window has length `auL p α - 1`) and must be
  the entry exposed by the pointer: when `d = 1` we have `auK s t k + 1 = auK s t (k+1) ≤ s`
  (`auK_le_s`, using `k + 1 ≤ t`), hence `auK s t k ≤ s - 1`, the look-up at
  `auK s t k + auL p α` is inside the extended array (`auK_add_auL_lt`) and the pointer entry is
  `auElems_getD_eq`.

Both cases are the statement of `dropAppTakeCongr`, and the case `d = 1` of the recurrence is
`auWinRecGen` (the `auWinRec` identity with the side condition dropped).  In particular the case
`k = t - 1` of the original recurrence is covered without any bound on the window centre at index
`t`. -/
theorem auWinRecAll (p α s t : ℕ) (u : List (ℤ × ℤ)) (hs : 2 ≤ s) (hst : s < t) (hu : u.length = s) :
    ∀ k < t, Work.Resample.auWinV p α s t u (k + 1) =
      ((Work.Resample.auWinV p α s t u k).drop (Work.Resample.auK s t (k + 1) - Work.Resample.auK s t k) ++
        [(Work.Resample.auElems p α s u).getD
          (((List.range k).map (fun j => Work.Resample.auK s t (j + 1) - Work.Resample.auK s t j)).sum)
          HvdH.Val.nil]).take (Work.Resample.auL p α) := by
  intro k hk
  have ht : 0 < t := by omega
  have hs1 : 1 ≤ s := by omega
  have hd : auK s t (k + 1) - auK s t k ≤ 1 := auK_step_sub hst ht
  have hsum : ((List.range k).map (fun j => auK s t (j + 1) - auK s t j)).sum = auK s t k :=
    auKSum s t k
  have hA : ((auWin p α s t u k).map HvdH.cfxVal).length = auL p α := by
    simpa only [auWinV] using auWinV_length p α s t u k
  have hx : auK s t (k + 1) - auK s t k = 1 →
      HvdH.cfxVal ((auExt p α s u).getD (auK s t k + auL p α) (0, 0))
        = (auElems p α s u).getD (auK s t k) HvdH.Val.nil := by
    intro h1
    have hKle : auK s t (k + 1) ≤ s := auK_le_s hs1 ht (by omega)
    have hKk : auK s t k ≤ s - 1 := by omega
    exact (auElems_getD_eq p α s t u k (auK_add_auL_lt p α s t k hs hKk u hu)).symm
  rw [hsum]
  simp only [auWinV]
  rw [auWinRecGen p α s t hs hst u hu k]
  exact dropAppTakeCongr ((auWin p α s t u k).map HvdH.cfxVal)
    (HvdH.cfxVal ((auExt p α s u).getD (auK s t k + auL p α) (0, 0)))
    ((auElems p α s u).getD (auK s t k) HvdH.Val.nil) (auL p α)
    (auK s t (k + 1) - auK s t k) hA hd hx

end Work.Resample
