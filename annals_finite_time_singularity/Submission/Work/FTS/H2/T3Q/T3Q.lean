import Mathlib.Algebra.Order.Ring.Star
import Mathlib.Algebra.Order.Star.Real
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Submission.Work.FTS.H2.T1Defs
import Submission.Work.FTS.H2.T3Q.HardTheta
import Submission.Work.FTS.H2.WPQ.Interior
import Submission.Work.FTS.TransportS.Defs
import Submission.Work.FTS.Vocab
import Submission.Work.Spaces.sin_two_rpow
import Submission.Work.Stability.CutFactorFderivZero

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.T3Q

open scoped Real
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 4000000

/-! ## The `D_θ` half of `Transport3`

`Work.FTS.H2.T3Q.HardTheta` (the order-five terms, via the angular integration by parts) and
`Work.FTS.H2.T3Q.EasyTheta` (the pointwise bound of the remainder) give the bound for the
pairing `(f ∂_θ g, g)_{ℋ⁴}` by assembling exactly as in `Work.FTS.H2.T1Q` does for the
`ℋ⁴`-coefficient: split `H4PairInt = T1Easy + T1Hard` pointwise, integrate the pointwise (in `z`)
bound, and use `abs_integral_le_integral_abs` plus `integral_mono_of_nonneg` (which needs no
measurability of the dominated function). -/


/-! ## The `D_z` half of `Transport3`

The pairing `(f ∂_z g, g)_{ℋ⁴}` splits pointwise as `H4PairInt = GoodZ + Badz2`, where
`Badz2 = Badz + Mismatchz` is the "exceptional" part (the order-five "all derivatives on `g`"
summands together with the "mismatch" summands, in which every `D_θ`-derivative falls on `f`).
`Work.FTS.H2.T3Q.GoodZPt` bounds `GoodZ` pointwise by `C |f|_𝒲 · HkIntegrand α 4 g`, so only
`Badz2` needs an integration by parts.

**The mismatch family must not be estimated separately.**  Its individual summands are *not*
bounded with an `α`-uniform constant: for `(i,j,b) = (1,3,0)` the block `D_z^4g` has the
natural `η`-weight while the pairing weight is `sin(2θ)^{-γ}`, so the deficit
`sin(2θ)^{-(γ-η)} = sin(2θ)^{-(0.01+α/10)}` is only paid by the factor
`(α+sin2θ)sin(2θ)^{α/5}` of the `𝒲^{4,∞}`-bound on `D_θf` when `α ≥ 1/30` (this is the
`(1,3,0)`-obstruction analysed in `Transport3Aux/MismatchBad/`).  What rescues the estimate is
the cancellation with the *hard* summands of the same slot: after the two integrations by parts
(radial for `Badz`, angular for `Mismatchz`) the two `θ`-integrated pieces combine into a single
`D_θ^i(f·…)`, i.e. a total `θ`-derivative, which is bounded by the slots.  Hence `Badz2` must be
estimated as a single object — the two `Prop`s below are exactly the missing inputs. -/




end Work.FTS.H2.T3Q
