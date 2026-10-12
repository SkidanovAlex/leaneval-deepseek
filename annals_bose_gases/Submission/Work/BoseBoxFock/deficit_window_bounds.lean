import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBoxFock.sharpAlias
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.BoseBoxFock

/-!
# `Work.BoseBoxFock.deficit_window_bounds` — the two-sided window for the profile deficit

The profile deficit is `deficit c r = [r − c]₊² − c²·tauPhi (r/c)`, where `tauPhi` is the explicit
smooth kinetic profile of `TauProf.lean` (the convolution of the kink `(·₊)²` with the bump
`tauKer`, supported in `[−1/4,1/4]`, evaluated at `r − 3/2`).  This file pins the deficit between
the two windows

    [r − c]₊² − [r − 5c/4]₊²  ≤  deficit c r  ≤  [r − c]₊²      (`c > 0`, `r ≥ 0`),

i.e. `0 ≤ c²·tauPhi (r/c) ≤ [r − 5c/4]₊²`.  Both halves are *pointwise* consequences of the
elementary profile facts:

* the upper half `c²·tauPhi (r/c) ≥ 0` is `tauPhi_nonneg` (`c² ≥ 0`);
* the lower half `c²·tauPhi (r/c) ≤ (max 0 (r − 5c/4))²` is the convolution-support bound
  `rescaled_tauPhi_le_conv` (`tauPhi_row.lean`): for `|t| < 1/4` one has
  `tauH (r/c − 3/2 − t) ≤ tauH (r/c − 5/4)`, so integrating against the nonnegative normalised
  kernel `K` gives `tauPhi (r/c) ≤ (max 0 (r/c − 5/4))²`, and rescaling by `c` (with `c > 0`)
  turns `c·max 0 (r/c − 5/4)` into `max 0 (r − 5c/4)`.

The window is *sharp in the small-frequency regime*: `tauPhi` vanishes identically for `r ≤ 5c/4`
(`rescaled_tauPhi_eq_zero`), so on the whole interval `r ≤ 5c/4` both bounds hold with
`deficit c r = [r−c]₊²` and the lower window equal to the upper one.  For `r ≥ 2c` the quadratic
tail `c²·tauPhi (r/c) = (r − 3c/2)² + C₀c²` takes over and the two windows separate, the deficit
then growing linearly (`deficit_ge_linear`).  Only the two inequalities above are needed here.
-/

/-- **The window bounds for the profile deficit.** -/
theorem deficit_window_bounds {c r : ℝ} (hc : 0 < c) (hr : 0 ≤ r) :
    (max (r - c) 0) ^ 2 - (max 0 (r - 5 * c / 4)) ^ 2 ≤ Work.BoseBoxFock.deficit c r
      ∧ Work.BoseBoxFock.deficit c r ≤ (max (r - c) 0) ^ 2 := by
  have hconv : c ^ 2 * tauPhi (r / c) ≤ (max 0 (r - 5 * c / 4)) ^ 2 :=
    rescaled_tauPhi_le_conv hc hr
  have hnn : 0 ≤ c ^ 2 * tauPhi (r / c) :=
    mul_nonneg (sq_nonneg c) (tauPhi_nonneg (r / c))
  unfold deficit
  exact ⟨by linarith, by linarith⟩

end Work.BoseBoxFock
