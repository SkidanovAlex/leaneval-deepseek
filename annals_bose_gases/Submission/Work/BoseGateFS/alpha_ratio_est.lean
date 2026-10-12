import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseGateFS.ratio_diff_bound
import Submission.Work.BoseK15.alphaCoef_eq_h
import Submission.Work.BoseK15.h_lipschitz
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseGateFS.alpha_ratio_est` — Lipschitz estimate for the squeezing parameter
in the two arguments `(A,B)`

The Bogoliubov squeezing parameter `α(𝒜,ℬ) = ℬ/(𝒜+√(𝒜²-ℬ²))` depends on the pair
only through the ratio `ℬ/𝒜`:

`α(𝒜,ℬ) = h(ℬ/𝒜)` (`Work.BoseK15.alphaCoef_eq_h`), `h r = r/(1+√(1-r²))`.

Since `h` is `4`-Lipschitz on `[-1/2,1/2]` (`Work.BoseK15.h_lipschitz`) and the
ratio `ℬ/𝒜` is controlled by the numerators `ℬ` and denominators `𝒜` separately
(`Work.BoseGateFS.ratio_diff_bound`), we get

`|α(Ap,Bp) - α(Aq,Bq)| ≤ 4 (|Bp-Bq| / max Ap Aq
    + max (|Bp|/Ap) (|Bq|/Aq) * |Ap-Aq| / max Ap Aq)`,

valid on FS's regime `2|ℬ| ≤ 𝒜` (which is exactly what `|ℬ/𝒜| ≤ 1/2` needs).
-/

noncomputable section

namespace Work.BoseGateFS

/-- The two-argument Lipschitz estimate for the Bogoliubov squeezing parameter,
in the regime `2|ℬ| ≤ 𝒜` of FS `eq:BoverA`. -/
theorem alpha_ratio_est {Ap Aq Bp Bq : ℝ} (hAp : 0 < Ap) (hAq : 0 < Aq)
    (hBp : 2 * |Bp| ≤ Ap) (hBq : 2 * |Bq| ≤ Aq) :
    |Work.BoseB7.alphaCoef Ap Bp - Work.BoseB7.alphaCoef Aq Bq| ≤
      4 * (|Bp - Bq| / max Ap Aq
        + max (|Bp| / Ap) (|Bq| / Aq) * |Ap - Aq| / max Ap Aq) := by
  -- both parameters are the one-variable `h` evaluated at the ratio
  rw [Work.BoseK15.alphaCoef_eq_h hAp (by linarith : |Bp| ≤ Ap / 2),
    Work.BoseK15.alphaCoef_eq_h hAq (by linarith : |Bq| ≤ Aq / 2)]
  -- the ratios lie in the Lipschitz range `[-1/2,1/2]`
  have hp : |Bp / Ap| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hAp, div_le_iff₀ hAp]
    linarith
  have hq : |Bq / Aq| ≤ 1 / 2 := by
    rw [abs_div, abs_of_pos hAq, div_le_iff₀ hAq]
    linarith
  have h1 := Work.BoseK15.h_lipschitz hp hq
  have h2 := ratio_diff_bound (aP := Ap) (aQ := Aq) (bP := Bp) (bQ := Bq) hAp hAq
  linarith

end Work.BoseGateFS
