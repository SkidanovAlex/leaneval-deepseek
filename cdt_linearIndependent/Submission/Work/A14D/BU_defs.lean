import Mathlib
import Submission.Work.A14.defs
import Submission.Work.A14D.LC_A_defs

/-!
# `Work.A14D.BU_defs`

Two auxiliary definitions used by `Work.A14D.BU_analytic_agree`:

* `Yser f w = Σ_k [yᵏ]f · (yC w)ᵏ` — the value of the `y`-series `f` at `y = yC w`;
* `BUint a b c HU HL i` — the integrand of the `i`-th integral slot of `BU`
  (`BUi a b c HU HL i z = Yser (intY (tq i (GZ a b c))) cSU + primSeg (BUint … i) cSU z`).
-/

namespace Work.A14D

open Complex Metric

noncomputable section

/-- The value of a `y`-series at `y = yC w = w²/(w−1)`. -/
def Yser (f : PowerSeries ℚ) (w : ℂ) : ℂ :=
  ∑' k : ℕ, ((PowerSeries.coeff k f : ℚ) : ℂ) * (yC w) ^ k

/-- The integrand of the `i`-th integral slot of `BU`: `y'(G − jets)/y^i`, where
`G = Sym⁺H` is represented by `HU` on `SU` and by `HL` on `SL`. -/
def BUint (a b c : ℤ) (HU HL : ℂ → ℂ) (i : Fin 3) : ℂ → ℂ :=
  fun ζ => dyC ζ * (yC ζ)⁻¹ ^ (i : ℕ) * ((HU ζ + HL (wC ζ)) - GjetA a b c (i : ℕ) ζ)

end

end Work.A14D
