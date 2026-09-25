import Mathlib

namespace Work.RHContract.B

open MeasureTheory Filter Asymptotics
open scoped Topology

/-!
# `Work.RHContract.B.deriv_mellin_const_sub`

The derivative, with respect to the exponent, of a Mellin transform along the map `z ↦ c - z`:
if `f : ℝ → ℂ` is locally integrable on `(0, ∞)`, is `O(x ^ (-a))` at `∞` and `O(x ^ (-b))` at
`0`, and `b < (c - s).re < a`, then

`deriv (fun z => mellin f (c - z)) s = - mellin (fun t => log t • f t) (c - s)`.

This is the chain rule applied to Mathlib's `mellin_hasDerivAt_of_isBigO_rpow`, which states
that the Mellin transform of `f` is differentiable at the point `c - s` with derivative the
Mellin transform of `log • f`, combined with the derivative `-1` of the affine coordinate
change `z ↦ c - z`.
-/

theorem deriv_mellin_const_sub {f : ℝ → ℂ} {a b : ℝ} {c s : ℂ}
    (hfc : MeasureTheory.LocallyIntegrableOn f (Set.Ioi 0))
    (hf_top : Asymptotics.IsBigO Filter.atTop f (fun x : ℝ => x ^ (-a)))
    (hs_top : (c - s).re < a)
    (hf_bot : Asymptotics.IsBigO (nhdsWithin 0 (Set.Ioi 0)) f (fun x : ℝ => x ^ (-b)))
    (hs_bot : b < (c - s).re) :
    deriv (fun z : ℂ => mellin f (c - z)) s
      = - mellin (fun t : ℝ => Real.log t • f t) (c - s) := by
  -- Mathlib: the Mellin transform of `f` is differentiable at `c - s`, with derivative the
  -- Mellin transform of `log • f`.
  have hmellin :=
    (mellin_hasDerivAt_of_isBigO_rpow hfc hf_top hs_top hf_bot hs_bot).2
  -- The coordinate change `z ↦ c - z` has derivative `-1`.
  have hinner : HasDerivAt (fun z : ℂ => c - z) (-1) s := by
    have := (hasDerivAt_id s).const_sub c
    simpa using this
  -- Chain rule.
  have hcomp := hmellin.comp s hinner
  rw [show (fun z : ℂ => mellin f (c - z)) = (mellin f) ∘ (fun z : ℂ => c - z) from rfl,
    hcomp.deriv]
  ring

end Work.RHContract.B
