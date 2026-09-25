import Mathlib
import Submission.Work.RHContract.A.regionII.abnum

/-!
# Region II: the final numeric check (finite range `173 ≤ n ≤ 501`), variant A

Here the term `caUbd n` carries coefficient `1` (rather than `36/100` as in
`num_check`).  All of `caUbd n`, `abAbd n` and `abJbd` are built from rational
constants by `+ - * /` and powers, hence take rational values; the inequality is
therefore a finite arithmetic check on the `329` values `n = 173, …, 501`,
discharged case by case by `norm_num`.
-/

set_option maxHeartbeats 8000000

namespace Work.RHContract.A.regionII

open Work.RHContract.A.RegionII

theorem num_checkA (n : ℕ) (h1 : 173 ≤ n) (h2 : n ≤ 501) :
    Work.RHContract.A.RegionII.caUbd n
      + (498/1000) * Work.RHContract.A.RegionII.abAbd n + 5/10^6
      ≤ (498/1000) * Work.RHContract.A.RegionII.abJbd := by
  interval_cases n <;>
    norm_num [Work.RHContract.A.RegionII.caUbd, Work.RHContract.A.RegionII.abAbd,
      Work.RHContract.A.RegionII.abJbd, Work.RHContract.A.RegionII.chordA,
      Work.RHContract.A.RegionII.chordB, Work.RHContract.A.RegionII.logl,
      Work.RHContract.A.RegionII.logU, Work.RHContract.A.RegionII.sqL,
      Work.RHContract.A.RegionII.chiU,
      Work.RHContract.A.RegionII.sq173l, Work.RHContract.A.RegionII.sq273l,
      Work.RHContract.A.RegionII.sq274l, Work.RHContract.A.RegionII.sq30000l,
      Work.RHContract.A.RegionII.lg30000l, Work.RHContract.A.RegionII.lg173,
      Work.RHContract.A.RegionII.lg273, Work.RHContract.A.RegionII.lg513,
      Work.RHContract.A.RegionII.lg25u, Work.RHContract.A.RegionII.inv25,
      Work.RHContract.A.RegionII.sq501u, Work.RHContract.A.RegionII.sq501l,
      Work.RHContract.A.RegionII.u501l, Work.RHContract.A.RegionII.u501u,
      Work.RHContract.A.RegionII.uzu, Work.RHContract.A.RegionII.uzl,
      Work.RHContract.A.RegionII.chi501u, Work.RHContract.A.RegionII.inv501_32_lb,
      Work.RHContract.A.RegionII.inv501_32_ub, Work.RHContract.A.RegionII.lg100ku,
      Work.RHContract.A.RegionII.lg501l, Work.RHContract.A.RegionII.lg512u,
      Work.RHContract.A.RegionII.lg274u]

end Work.RHContract.A.regionII
