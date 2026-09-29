import Mathlib
import Submission.Work.TMC16Core.Core.windows

/-!
# Auxiliary definitions for the resonant uniformity (`Core.uni_res5`)

The resonant windows `J1resG h ∪ J2resG q h ℓ` are, in the *index* variable `k`, the block
`resK q n h = [-(h:ℤ), 2q - h - 1]` of length `2q` together with the shift function
`resLsh h ℓ k = 0` for `k < h` and `= ℓ - 1` for `k ≥ h`: the site map
`resSite k = k + resLsh k * q` maps `resK` bijectively onto `resW`.

`resB1`, `resB2` are the two `q`-blocks into which `resK` splits; they are the blocks to which
the shifted block estimate `Core.irrat_blk_shift` is applied.
-/

namespace Work.TMC16Core.Core

open Work.TMC16Core

noncomputable section

/-- The shift (in units of `q n`) of the site with index `k`: `0` for `k < h`, `ℓ - 1` for
`k ≥ h`. -/
def resLsh (h ℓ : ℕ) (k : ℤ) : ℤ := if k < (h : ℤ) then 0 else (ℓ : ℤ) - 1

/-- The site corresponding to the index `k` in the resonant windows. -/
def resSite (qn h ℓ : ℕ) (k : ℤ) : ℤ := k + resLsh h ℓ k * (qn : ℤ)

/-- The block of indices of the resonant windows: `[-(h:ℤ), 2 * qn - h - 1]`, of length `2 qn`. -/
def resK (qn h : ℕ) : Finset ℤ := Finset.Icc (-(h : ℤ)) ((2 * (qn : ℤ)) - (h : ℤ) - 1)

/-- The first `q`-block of `resK`: `[-(h:ℤ), qn - h - 1]`. -/
def resB1 (qn h : ℕ) : Finset ℤ := Finset.Icc (-(h : ℤ)) ((qn : ℤ) - (h : ℤ) - 1)

/-- The second `q`-block of `resK`: `[qn - h, 2 qn - h - 1]`. -/
def resB2 (qn h : ℕ) : Finset ℤ := Finset.Icc ((qn : ℤ) - (h : ℤ)) ((2 * (qn : ℤ)) - (h : ℤ) - 1)

/-- The union of the two resonant windows. -/
def resW (qn h ℓ : ℕ) : Finset ℤ := J1resG h ∪ J2resG qn h ℓ

end

end Work.TMC16Core.Core
