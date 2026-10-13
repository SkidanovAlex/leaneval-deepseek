/-
# `FTS/PhiStar/Honesty/Fstar_psiSeries_eq_zero_of_hkMem` — the moment of the mode series, with
the coefficient summability discharged

`Honesty.Fstar_psiSeries_eq_zero` proves `Fstar (psiSeries α F) z = 0` for `z > 0` from three
inputs: the source's moment `F_* F ≡ 0` on `z > 0`, the pointwise coefficient summability
`Summable (m ↦ (m+1)|acoeff α m F z|)`, and `z > 0`.

With the `hcoef` chain of this directory (`Honesty.hcoef_psiSeries`, proved from
`Honesty.radGreen_abs_le_L2` + `Honesty.cmode_bessel_L2`) the middle hypothesis is *automatic*
from `SmoothOpen F` and `HkMem α 0 F` alone.  This file records that corollary: it is the form in
which the moment conjunct of `TT.EllWeakPos` is available for the modal solution, and it removes
`hcoef` from the input list of every consumer of `Fstar_psiSeries_eq_zero`.

No moment hypothesis on the *solution* is used or produced here; the source's moment is what
kills the `m = 0` kernel direction.
-/
import Mathlib.Basic.Real.Basic
import Mathlib.Order.Filter.Defs
import Submission.Work.FTS.PhiStar.Honesty.hcoef_psiSeries
import Submission.Work.FTS.PhiStar.Honesty.Fstar_psiSeries_eq_zero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.PhiStar.Honesty

set_option autoImplicit false

/-- **The moment of the mode series vanishes, from `ℋ⁰`-honesty of the source.** -/
theorem Fstar_psiSeries_eq_zero_of_hkMem {α : ℝ} (hα : 0 < α) (hα4 : α ≤ 1 / 4)
    {F : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen F)
    (hF : Work.Spaces.HkMem α 0 F)
    (hFs : ∀ t : ℝ, 0 < t → Work.Elliptic.Fstar F t = 0) :
    ∀ z : ℝ, 0 < z → Work.Elliptic.Fstar (Work.FTS.PhiStar.Series.psiSeries α F) z = 0 :=
  fun z hz => Fstar_psiSeries_eq_zero hz (hcoef_psiSeries hα hα4 hsm hF z hz) hFs

end Work.FTS.PhiStar.Honesty
