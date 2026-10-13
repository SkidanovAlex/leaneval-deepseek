import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.CoreResiduals.SelfSimReduction

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.MeridianDyn.Odd.meridianResid_odd`

The meridian residual `Work.CoreResiduals.meridianResid` is **odd in `z`** whenever the vorticity
profile `W` and the stream function `ψ` are pointwise odd in the axial variable `z` (i.e. the
physical meridional half-plane `z > 0` determines the whole picture through the reflection
`z ↦ -z`).

Term by term: writing `f = W r · t` and `g = ψ r · t` for the two `z`-slices,

* `∂ₜW` is odd in `z`, because `z ↦ W r z s` is pointwise `-` the reflected slice for every
  time `s`, and `deriv` is additive (`deriv.neg`); this needs **no** differentiability
  hypothesis, since `deriv` is total and totalised to `0` off the differentiable points —
  oddness at `z` and at `-z` are interchangeable pointwise, so the junk values match too;
* `∂_zψ` and `∂_zW` are **even** in `z`: the derivative of an odd function is even
  (`deriv_neg_of_odd`, from the unconditional identity `deriv_comp_neg`);
* `∂_rW` and `∂_rψ` are odd in `z`: for fixed `r` the `r`-slice at `-z` is pointwise `-` the
  slice at `z`, so its derivative is the negative (`deriv.neg`);
* `W r z t`, `ψ r z t` are odd by hypothesis.

The residual is
`∂ₜW + (∂_zψ)(∂_rW) + ( -(ψ/r) - ∂_rψ )(∂_zW) - ((∂_zψ)/r)W`, an odd·even / odd·odd
combination of these, hence odd.  The factor `1/r` is *not* differentiated and plays no role
beyond the (harmless) hypothesis `r ≠ 0` carried by the statement.
-/

namespace Work.FTS.MeridianDyn.Odd

/-- **The derivative of a pointwise odd function is even**: if `f (-x) = -f x` for all `x` then
`deriv f (-x) = deriv f x`.

No regularity hypothesis is needed: `deriv` is a total function and Mathlib's `deriv_comp_neg`
is unconditional, so the identity holds both where `f` is differentiable (where the chain rule
gives it) and where it is not (where both sides are the junk value `0`, the two points being
differentiable simultaneously by the oddness relation `f y = -f (-y)`). -/
theorem deriv_neg_of_odd {f : ℝ → ℝ} (hf : ∀ x, f (-x) = -f x) (x : ℝ) :
    deriv f (-x) = deriv f x := by
  have h := deriv_comp_neg (f := f) (x := x)
  rw [show (fun y : ℝ => f (-y)) = fun y => -f y from funext hf] at h
  have h2 : deriv (fun y : ℝ => -f y) x = -deriv f x := deriv.neg
  linarith [h, h2]

/-- The meridian residual is odd in `z` for a pair that is odd in `z`. -/
theorem meridianResid_odd {W ψ : ℝ → ℝ → ℝ → ℝ}
    (hW : ∀ r z t : ℝ, W r (-z) t = -W r z t)
    (hψ : ∀ r z t : ℝ, ψ r (-z) t = -ψ r z t) :
    ∀ r z t : ℝ, r ≠ 0 →
      Work.CoreResiduals.meridianResid W ψ r (-z) t
        = -Work.CoreResiduals.meridianResid W ψ r z t := by
  intro r z t _
  -- time derivative: the two time-slices are pointwise opposite
  have h1 : deriv (fun s => W r (-z) s) t = -deriv (fun s => W r z s) t := by
    rw [show (fun s : ℝ => W r (-z) s) = fun s => -(W r z s) from
      funext (fun s => hW r z s)]
    exact deriv.neg
  -- `∂_z`: even in `z`
  have h2 : deriv (fun z' => ψ r z' t) (-z) = deriv (fun z' => ψ r z' t) z :=
    deriv_neg_of_odd (f := fun z' => ψ r z' t) (fun x => hψ r x t) z
  have h3 : deriv (fun z' => W r z' t) (-z) = deriv (fun z' => W r z' t) z :=
    deriv_neg_of_odd (f := fun z' => W r z' t) (fun x => hW r x t) z
  -- `∂_r`: odd in `z`
  have h4 : deriv (fun r' => ψ r' (-z) t) r = -deriv (fun r' => ψ r' z t) r := by
    rw [show (fun r' : ℝ => ψ r' (-z) t) = fun r' => -(ψ r' z t) from
      funext (fun r' => hψ r' z t)]
    exact deriv.neg
  have h5 : deriv (fun r' => W r' (-z) t) r = -deriv (fun r' => W r' z t) r := by
    rw [show (fun r' : ℝ => W r' (-z) t) = fun r' => -(W r' z t) from
      funext (fun r' => hW r' z t)]
    exact deriv.neg
  -- the undifferentiated values
  have h6 : W r (-z) t = -W r z t := hW r z t
  have h7 : ψ r (-z) t = -ψ r z t := hψ r z t
  simp only [Work.CoreResiduals.meridianResid, Work.Cyl.pdZ, Work.Cyl.pdR]
  rw [h1, h2, h3, h4, h5, h6, h7]
  ring

end Work.FTS.MeridianDyn.Odd
