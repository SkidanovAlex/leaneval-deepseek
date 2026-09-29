import Mathlib
import Submission.Work.Resample.auWinRec

namespace Work.Resample

open HvdH

/-- The window-recursion identity `auWinRec` **without** the side condition `k + 1 < t`.

Neither the proof of `auWinRec` nor the underlying slide identity (`auSlideMap`) uses `k < t`:
`auK s t` is monotone with unit steps as soon as `s < t` (`auK_step_sub`), and the window of
output `k + 1` is `awWin … k` slid by `auK s t (k+1) - auK s t k ∈ {0,1}`.  For `k ≥ t` the
"centre" `auK s t k` may exceed `s`, so that `auExt`-entries are read beyond the data; both
sides then agree entrywise through `getD _ (0,0)`, which is why the identity survives. -/
theorem auWinRecGen (p α s t : ℕ) (hs : 2 ≤ s) (hst : s < t) (u : List (ℤ × ℤ)) (hu : u.length = s) (k : ℕ) :
    (Work.Resample.auWin p α s t u (k+1)).map HvdH.cfxVal
      = (((Work.Resample.auWin p α s t u k).map HvdH.cfxVal).drop (Work.Resample.auK s t (k+1) - Work.Resample.auK s t k)
          ++ [HvdH.cfxVal ((Work.Resample.auExt p α s u).getD (Work.Resample.auK s t k + Work.Resample.auL p α) (0,0))]).take (Work.Resample.auL p α) := by
  have ht : 0 < t := by omega
  have hd : auK s t (k + 1) - auK s t k ≤ 1 := auK_step_sub hst ht
  have hK : auK s t k + (auK s t (k + 1) - auK s t k) = auK s t (k + 1) := by
    have hmono : auK s t k ≤ auK s t (k + 1) := auKArith_mono s t (Nat.le_succ k)
    omega
  have hwin : ∀ m : ℕ, (auWin p α s t u m).map HvdH.cfxVal
      = (List.range (auL p α)).map (fun i =>
          HvdH.cfxVal ((auExt p α s u).getD (auK s t m + i) (0,0))) := by
    intro m
    rw [auWin, List.map_map]
    rfl
  have hkey : (fun i => HvdH.cfxVal ((auExt p α s u).getD (auK s t (k+1) + i) (0,0)))
      = (fun i => HvdH.cfxVal ((auExt p α s u).getD
          (auK s t k + (auK s t (k+1) - auK s t k) + i) (0,0))) := by
    funext i
    rw [hK]
  rw [hwin (k+1), hwin k, hkey]
  exact auSlideMap (fun j => HvdH.cfxVal ((auExt p α s u).getD j (0,0))) (auK s t k)
    (auL p α) (auK s t (k + 1) - auK s t k) hd

end Work.Resample
