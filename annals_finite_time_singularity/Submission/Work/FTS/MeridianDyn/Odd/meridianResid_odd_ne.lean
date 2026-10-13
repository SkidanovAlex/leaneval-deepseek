import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.CoreResiduals.SelfSimReduction
import Submission.Work.FTS.MeridianDyn.Odd.meridianResid_odd

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.MeridianDyn.Odd.meridianResid_odd_ne`

The meridian residual `Work.CoreResiduals.meridianResid` is **odd in `z`** whenever the vorticity
profile `W` and the stream function `ψ` are odd in the axial variable `z` *off the axis* `z = 0`
(the hypothesis carriers `z ≠ 0`).  This is the "away from the axis" refinement of
`Work.FTS.MeridianDyn.Odd.meridianResid_odd`, whose hypothesis is global pointwise oddness: for
the applications one only ever knows `W r (-z) t = -W r z t` for `z ≠ 0` (the value at `z = 0` is
an arbitrary junk value of the coordinate chart), and the unconditioned lemma is not applicable
verbatim.

The one new ingredient beyond the sibling file is `deriv_neg_of_odd_ne`: the derivative of a
function that is odd *away from the origin* is even *away from the origin*.  For the derivative at
a point `x ≠ 0` only the germ at `x` matters, and there oddness gives the agreement of `f` with
`-(f ∘ Neg.neg)` on a whole neighbourhood of `x` (which can be taken to avoid `0`), so
`Filter.EventuallyEq.deriv_eq` applies and the chain rule `deriv_comp_neg` finishes.  Global
oddness (hence `deriv_neg_of_odd`) is *not* available here: the value at the origin is unconstrained
and the functions need not satisfy `f 0 = 0`.

The time derivative `∂ₜ`, the radial derivative `∂_r` and the undifferentiated values use only the
pointwise oddness at the *fixed* nonzero axial coordinate, so they need no germ argument; the axial
derivatives `∂_z` are the even ones and are handled by `deriv_neg_of_odd_ne`.

The residual is
`∂ₜW + (∂_zψ)(∂_rW) + ( -(ψ/r) - ∂_rψ )(∂_zW) - ((∂_zψ)/r)W`, an odd·even / odd·odd
combination of these, hence odd; the factor `1/r` is not differentiated and plays no role beyond
the (harmless) hypothesis `r ≠ 0`.
-/

open scoped Topology

namespace Work.FTS.MeridianDyn.Odd

/-- **The derivative of a function that is odd away from the origin is even away from the
origin**: if `f (-x) = -f x` for every `x ≠ 0`, then `deriv f (-x) = deriv f x` for every
`x ≠ 0`.

No regularity hypothesis is needed: `deriv` is total, so the two sides agree both where `f` is
differentiable (chain rule, `deriv_comp_neg`) and where it is not (both sides are the junk value
`0`, differentiability at `x` and at `-x` being equivalent by oddness).  Since `x ≠ 0`, a
neighbourhood of `x` avoids `0` and on it `f` coincides with `-(f ∘ Neg.neg)`; the derivative only
sees this germ. -/
theorem deriv_neg_of_odd_ne {f : ℝ → ℝ} (hf : ∀ x : ℝ, x ≠ 0 → f (-x) = -f x)
    {x : ℝ} (hx : x ≠ 0) : deriv f (-x) = deriv f x := by
  have hne : (-x) ≠ 0 := neg_ne_zero.mpr hx
  -- near `-x` (which is nonzero) the function `f` agrees with `-(f ∘ Neg.neg)`
  have hev : f =ᶠ[𝓝 (-x)] fun y : ℝ => -f (-y) := by
    filter_upwards [isOpen_ne.mem_nhds hne] with y hy
    exact (by simpa using hf (-y) (by simpa using hy : -y ≠ 0))
  rw [hev.deriv_eq]
  have hcomp : deriv (fun y : ℝ => f (-y)) (-x) = -deriv f x := by
    have h := deriv_comp_neg (f := f) (x := -x)
    simpa using h
  rw [show (fun y : ℝ => -f (-y)) = -(fun y : ℝ => f (-y)) from rfl, deriv.neg, hcomp, neg_neg]

/-- The meridian residual is odd in `z` for a pair that is odd in `z` off the axis. -/
theorem meridianResid_odd_ne {W ψ : ℝ → ℝ → ℝ → ℝ}
    (hW : ∀ r z t : ℝ, z ≠ 0 → W r (-z) t = -W r z t)
    (hψ : ∀ r z t : ℝ, z ≠ 0 → ψ r (-z) t = -ψ r z t) :
    ∀ r z t : ℝ, r ≠ 0 → z ≠ 0 →
      Work.CoreResiduals.meridianResid W ψ r (-z) t
        = -Work.CoreResiduals.meridianResid W ψ r z t := by
  intro r z t _ hz
  -- time derivative: the two time-slices are pointwise opposite (`z ≠ 0` is fixed)
  have h1 : deriv (fun s : ℝ => W r (-z) s) t = -deriv (fun s : ℝ => W r z s) t := by
    rw [show (fun s : ℝ => W r (-z) s) = fun s => -(W r z s) from
      funext (fun s => hW r z s hz)]
    exact deriv.neg
  -- `∂_z`: even in `z`
  have h2 : deriv (fun z' : ℝ => ψ r z' t) (-z) = deriv (fun z' : ℝ => ψ r z' t) z :=
    deriv_neg_of_odd_ne (f := fun z' : ℝ => ψ r z' t) (fun x hx => hψ r x t hx) hz
  have h3 : deriv (fun z' : ℝ => W r z' t) (-z) = deriv (fun z' : ℝ => W r z' t) z :=
    deriv_neg_of_odd_ne (f := fun z' : ℝ => W r z' t) (fun x hx => hW r x t hx) hz
  -- `∂_r`: odd in `z` (the axial coordinate is held fixed at `z ≠ 0`)
  have h4 : deriv (fun r' : ℝ => ψ r' (-z) t) r = -deriv (fun r' : ℝ => ψ r' z t) r := by
    rw [show (fun r' : ℝ => ψ r' (-z) t) = fun r' => -(ψ r' z t) from
      funext (fun r' => hψ r' z t hz)]
    exact deriv.neg
  have h5 : deriv (fun r' : ℝ => W r' (-z) t) r = -deriv (fun r' : ℝ => W r' z t) r := by
    rw [show (fun r' : ℝ => W r' (-z) t) = fun r' => -(W r' z t) from
      funext (fun r' => hW r' z t hz)]
    exact deriv.neg
  -- the undifferentiated values
  have h6 : W r (-z) t = -W r z t := hW r z t hz
  have h7 : ψ r (-z) t = -ψ r z t := hψ r z t hz
  simp only [Work.CoreResiduals.meridianResid, Work.Cyl.pdZ, Work.Cyl.pdR]
  rw [h1, h2, h3, h4, h5, h6, h7]
  ring

end Work.FTS.MeridianDyn.Odd
