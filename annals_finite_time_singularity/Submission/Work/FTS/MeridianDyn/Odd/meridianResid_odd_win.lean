import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Topology.GDelta.MetrizableSpace
import Submission.Work.FTS.MeridianDyn.Defs
import Submission.Work.CoreResiduals.SelfSimReduction
import Submission.Work.FTS.MeridianDyn.Odd.meridianResid_odd
import Submission.Work.FTS.MeridianDyn.Odd.meridianResid_odd_ne

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `Work.FTS.MeridianDyn.Odd.meridianResid_odd_win`

The meridian residual `Work.CoreResiduals.meridianResid` is **odd in `z`** whenever the vorticity
profile `W` and the stream function `ψ` are odd in the axial variable `z` *on the time window*
`(0,T)`, off the axis `z = 0`.

This is the windowed variant of `Work.FTS.MeridianDyn.Odd.meridianResid_odd_ne`: the oddness of
`W r · ·` and `ψ r · ·` is only known for times `s ∈ Ioo 0 T`, and the conclusion is likewise only
claimed for `t ∈ Ioo 0 T`.  The residual is
`∂ₜW + (∂_zψ)(∂_rW) + ( -(ψ/r) - ∂_rψ )(∂_zW) - ((∂_zψ)/r)W`, so it suffices to know the
parity of each ingredient at the point `(r,z,t)`:

* the time derivative `∂ₜ`: the two time-slices `s ↦ W r (-z) s` and `s ↦ -(W r z s)` agree on
  the neighbourhood `Ioo 0 T` of `t ∈ Ioo 0 T`, and `deriv` only sees the germ, so
  `Filter.EventuallyEq.deriv_eq` followed by `deriv.neg` gives the oddness;
* the radial derivative `∂_r`: for fixed `(-z)` (resp. `z`) with `z ≠ 0`, the `r`-slices agree
  with their negations on a neighbourhood of `r ≠ 0` (which avoids the origin), so again
  `Filter.EventuallyEq.deriv_eq` + `deriv.neg`;
* the axial derivative `∂_z`: oddness in `z` makes the derivative even.  Since the axial
  coordinate is held at a *fixed* `t ∈ Ioo 0 T`, this is exactly `deriv_neg_of_odd_ne` of the
  sibling `meridianResid_odd_ne` (which needs `z ≠ 0` and the oddness only away from the origin);
* the undifferentiated values are odd by hypothesis.

The residual is then an odd·even / odd·odd combination, hence odd.
-/

open scoped Topology

namespace Work.FTS.MeridianDyn.Odd

/-- **Windowed oddness of the meridian residual.**  If `W r (-z) t = -W r z t` and
`ψ r (-z) t = -ψ r z t` for all `r ≠ 0`, `z ≠ 0` and `t ∈ Ioo 0 T`, then
`meridianResid W ψ` is odd in `z` on that same window. -/
theorem meridianResid_odd_win {W ψ : ℝ → ℝ → ℝ → ℝ} {T : ℝ}
    (hW : ∀ r z t : ℝ, r ≠ 0 → z ≠ 0 → t ∈ Set.Ioo (0 : ℝ) T → W r (-z) t = -W r z t)
    (hψ : ∀ r z t : ℝ, r ≠ 0 → z ≠ 0 → t ∈ Set.Ioo (0 : ℝ) T → ψ r (-z) t = -ψ r z t) :
    ∀ r z t : ℝ, r ≠ 0 → z ≠ 0 → t ∈ Set.Ioo (0 : ℝ) T →
      Work.CoreResiduals.meridianResid W ψ r (-z) t
        = -Work.CoreResiduals.meridianResid W ψ r z t := by
  intro r z t hr hz ht
  -- time derivative: the two time-slices agree on the neighbourhood `Ioo 0 T` of `t`
  have h1 : deriv (fun s : ℝ => W r (-z) s) t = -deriv (fun s : ℝ => W r z s) t := by
    have hev : (fun s : ℝ => W r (-z) s) =ᶠ[𝓝 t] fun s => -(W r z s) := by
      filter_upwards [isOpen_Ioo.mem_nhds ht] with s hs
      exact hW r z s hr hz hs
    rw [hev.deriv_eq]
    exact deriv.neg
  -- `∂_z`: even in `z` (odd function of `z`, at the fixed time `t`)
  have h2 : deriv (fun z' : ℝ => ψ r z' t) (-z) = deriv (fun z' : ℝ => ψ r z' t) z :=
    deriv_neg_of_odd_ne (f := fun z' : ℝ => ψ r z' t) (fun x hx => hψ r x t hr hx ht) hz
  have h3 : deriv (fun z' : ℝ => W r z' t) (-z) = deriv (fun z' : ℝ => W r z' t) z :=
    deriv_neg_of_odd_ne (f := fun z' : ℝ => W r z' t) (fun x hx => hW r x t hr hx ht) hz
  -- `∂_r`: odd in `z` (germ at `r ≠ 0`, hence avoiding the origin)
  have h4 : deriv (fun r' : ℝ => ψ r' (-z) t) r = -deriv (fun r' : ℝ => ψ r' z t) r := by
    have hev : (fun r' : ℝ => ψ r' (-z) t) =ᶠ[𝓝 r] fun r' => -(ψ r' z t) := by
      filter_upwards [isOpen_ne.mem_nhds hr] with r' hr'
      exact hψ r' z t hr' hz ht
    rw [hev.deriv_eq]
    exact deriv.neg
  have h5 : deriv (fun r' : ℝ => W r' (-z) t) r = -deriv (fun r' : ℝ => W r' z t) r := by
    have hev : (fun r' : ℝ => W r' (-z) t) =ᶠ[𝓝 r] fun r' => -(W r' z t) := by
      filter_upwards [isOpen_ne.mem_nhds hr] with r' hr'
      exact hW r' z t hr' hz ht
    rw [hev.deriv_eq]
    exact deriv.neg
  -- the undifferentiated values
  have h6 : W r (-z) t = -W r z t := hW r z t hr hz ht
  have h7 : ψ r (-z) t = -ψ r z t := hψ r z t hr hz ht
  simp only [Work.CoreResiduals.meridianResid, Work.Cyl.pdZ, Work.Cyl.pdR]
  rw [h1, h2, h3, h4, h5, h6, h7]
  ring

end Work.FTS.MeridianDyn.Odd
