import Mathlib
import Submission.Work.Peluse.Ulower.boxNormPow_two_dilate
import Submission.Work.Peluse.Ulower.ss_aux_symIcc_ratio

namespace Work.Peluse.Ulower

theorem symIcc_ratio_lower {P : Polynomial ℤ} {c : ℤ} (hc : c ≠ 0) {Ns N D : ℕ}
    (hc1 : 1 ≤ c.natAbs) (hNs : 1 ≤ Ns) (hD : 1 ≤ D)
    (hL'' : max ((Work.Peluse.dSup P Ns N) / c.natAbs + 1) D ≤ Work.Peluse.Ulower.ssAmax P * Ns) :
    2 / (3 * (Work.Peluse.Ulower.ssAmax P : ℝ) * (c.natAbs : ℝ)) ≤
      ((Work.Peluse.symIcc (Work.Peluse.dSup P Ns N)).card : ℝ) /
        ((c.natAbs : ℝ) *
          ((Work.Peluse.symIcc (max ((Work.Peluse.dSup P Ns N) / c.natAbs + 1) D)).card : ℝ)) :=
  ss_aux_symIcc_ratio hc hc1 hNs hD hL''

end Work.Peluse.Ulower
