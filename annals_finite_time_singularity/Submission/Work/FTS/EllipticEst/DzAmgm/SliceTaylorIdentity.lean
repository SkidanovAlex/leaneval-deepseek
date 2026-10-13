/-
Copyright: work module for the Elgindi finite-time singularity project.

# The slice Taylor identity with integral remainder

This file proves `Work.FTS.EllipticEst.DzAmgm.SliceTaylorIdentity`: for a function
`V` of class `C²` on the open quadrant `(0,∞) × (0,π/2)`, a base point `z₀ > 0`, an
increment `δ > 0` and an angle `θ ∈ (0,π/2)`,

`∂_z V (z₀,θ)
   = δ⁻¹ * (V (z₀+δ,θ) - V (z₀,θ) - ∫_0^δ (δ-t) ∂_z²V (z₀+t,θ) dt)`,

i.e. Taylor's formula with the remainder in integral form along the radial slice
`z ↦ V z θ`, solved for the first derivative.  This is the ("solve for `∂_z f`")
form in which the second-order Taylor expansion is used to bound `∂_z` by a finite
difference plus the second derivative in the radial Agmon–Nirenberg estimate
`Work.FTS.EllipticEst.HkNorm_Dz_amgm`.

The analytic content is isolated in the general one-dimensional statement
`taylorIntegralRemainder_two` (Taylor for an arbitrary `C²` function `g` on `(0,∞)`,
`∫_a^{a+δ} (a+δ-s) g''(s) ds = g(a+δ) - g a - δ g'(a)`); the target theorem is then
the slice `g := fun z => V z θ`, whose `C²`-regularity on `(0,∞)` follows from `hV`
by restricting the `C²` uncurried function `Function.uncurry V` to the line
`z ↦ (z, θ)`.
-/
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Order.CompletePartialOrder
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real
open MeasureTheory Set

namespace Work.FTS.EllipticEst.DzAmgm

set_option autoImplicit false

/-- **Taylor's formula with integral remainder, in dimension one, solved for the first
derivative.**  If `g` is `C²` on `(0,∞)`, `a > 0` and `δ > 0`, then

`∫_0^δ (δ - t) g''(a + t) dt = g (a + δ) - g a - δ g'(a)`,

an identity about an *open* condition: the hypotheses only require the `C²` behaviour of `g`
near the points of the segment `[a, a+δ]`, all of which are `> 0`. -/
theorem taylorIntegralRemainder_two {g : ℝ → ℝ} {a δ : ℝ} (ha : 0 < a) (hδ : 0 < δ)
    (hg : ContDiffOn ℝ 2 g (Set.Ioi 0)) :
    ∫ t in (0 : ℝ)..δ, (δ - t) * deriv (deriv g) (a + t)
      = g (a + δ) - g a - δ * deriv g a := by
  have hle : a ≤ a + δ := by linarith
  -- `g` is `C²` at every point of the segment `[a, a+δ]`, since all are `> 0`.
  have hca : ∀ s ∈ Set.uIcc a (a + δ), ContDiffAt ℝ 2 g s := by
    intro s hs
    have hs' : 0 < s := by
      rw [Set.uIcc_of_le hle, Set.mem_Icc] at hs
      linarith [hs.1]
    exact hg.contDiffAt (isOpen_Ioi.mem_nhds hs')
  -- Change of variable `s = a + t`.
  have hstep1 : ∫ t in (0 : ℝ)..δ, (δ - t) * deriv (deriv g) (a + t)
      = ∫ s in a..a + δ, (a + δ - s) * deriv (deriv g) s := by
    have h := intervalIntegral.integral_comp_add_left (a := (0 : ℝ)) (b := δ)
      (fun s : ℝ => (a + δ - s) * deriv (deriv g) s) a
    have h' : ∫ t in (0 : ℝ)..δ, (a + δ - (a + t)) * deriv (deriv g) (a + t)
        = ∫ s in a..a + δ, (a + δ - s) * deriv (deriv g) s := by
      simpa using h
    rw [← h']
    apply intervalIntegral.integral_congr
    intro t _
    ring
  rw [hstep1]
  -- The fundamental theorem of calculus applied to
  -- `s ↦ (a + δ - s) * g'(s) + g(s)`, whose derivative is `(a + δ - s) * g''(s)`.
  have hH : ∀ s ∈ Set.uIcc a (a + δ),
      HasDerivAt (fun s : ℝ => (a + δ - s) * deriv g s + g s)
        ((a + δ - s) * deriv (deriv g) s) s := by
    intro s hs
    have h2 : ContDiffAt ℝ 2 g s := hca s hs
    have h1 : ContDiffAt ℝ 1 (deriv g) s := h2.derivWithin (m := 1) (by norm_num)
    have hd2 : HasDerivAt (deriv g) (deriv (deriv g) s) s :=
      (h1.hasStrictDerivAt (by norm_num)).hasDerivAt
    have hd0 : HasDerivAt g (deriv g s) s := (h2.differentiableAt (by norm_num)).hasDerivAt
    have hd1 : HasDerivAt (fun s : ℝ => a + δ - s) (-1) s := by
      have h : HasDerivAt (fun s : ℝ => a + δ - s) (0 - 1) s :=
        (hasDerivAt_const s (a + δ)).sub (hasDerivAt_id s)
      simpa using h
    have h := (hd1.mul hd2).add hd0
    have hA : (-1 * deriv g s + (a + δ - s) * deriv (deriv g) s + deriv g s)
        = (a + δ - s) * deriv (deriv g) s := by ring
    rw [hA] at h
    exact h
  have hint : IntervalIntegrable (fun s : ℝ => (a + δ - s) * deriv (deriv g) s)
      MeasureTheory.volume a (a + δ) := by
    apply ContinuousOn.intervalIntegrable
    intro s hs
    have h2 : ContDiffAt ℝ 2 g s := hca s hs
    have h1 : ContDiffAt ℝ 1 (deriv g) s := h2.derivWithin (m := 1) (by norm_num)
    have h0 : ContinuousAt (deriv (deriv g)) s :=
      (h1.derivWithin (m := 0) (by norm_num)).continuousAt
    exact ((continuous_const.sub continuous_id).continuousAt.mul h0).continuousWithinAt
  have hFTC : ∫ y in a..a + δ, (a + δ - y) * deriv (deriv g) y
      = (a + δ - (a + δ)) * deriv g (a + δ) + g (a + δ)
          - ((a + δ - a) * deriv g a + g a) := by
    have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hH hint
    simpa using h
  rw [hFTC]
  ring

/-- **The slice Taylor identity.**  For `V` of class `C²` on the open quadrant, `z₀ > 0`,
`δ > 0` and `θ ∈ (0,π/2)`,

`∂_z V (z₀,θ) = δ⁻¹ * (V (z₀+δ,θ) - V (z₀,θ) - ∫_0^δ (δ-t) ∂_z²V (z₀+t,θ) dt)`.

This is Taylor's formula with integral remainder for the slice `z ↦ V z θ`, solved for the
first derivative: it expresses `∂_z` as a finite difference of `V` plus the second derivative,
which is exactly the form used to interpolate `D_z` against `z² ∂_z²` in the radial
Agmon–Nirenberg estimate. -/
theorem SliceTaylorIdentity (V : ℝ → ℝ → ℝ)
    (hV : ContDiffOn ℝ 2 (Function.uncurry V) (Set.Ioi 0 ×ˢ Set.Ioo 0 (Real.pi / 2)))
    {z₀ δ θ : ℝ} (hz₀ : 0 < z₀) (hδ : 0 < δ) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pz V z₀ θ
      = δ⁻¹ * (V (z₀ + δ) θ - V z₀ θ
          - ∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ) := by
  -- The `θ`-slice of a `C²` function on the quadrant is `C²` on `(0,∞)`.
  have hslice : ContDiffOn ℝ 2 (fun z => V z θ) (Set.Ioi 0) := by
    have h1 : ContDiffOn ℝ 2 (fun z : ℝ => (z, θ)) (Set.Ioi 0) := by fun_prop
    exact hV.comp h1 (by intro z hz; exact ⟨hz, hθ⟩)
  have hkey := taylorIntegralRemainder_two hz₀ hδ hslice
  have hpz : Work.Spaces.pz V z₀ θ = deriv (fun z => V z θ) z₀ := rfl
  -- `pzIter 2 V z θ` is `deriv (deriv (fun z => V z θ)) z` by definition.
  have hint : ∫ t in (0 : ℝ)..δ, (δ - t) * Work.Spaces.pzIter 2 V (z₀ + t) θ
      = ∫ t in (0 : ℝ)..δ, (δ - t) * deriv (deriv (fun z => V z θ)) (z₀ + t) := by
    apply intervalIntegral.integral_congr
    intro t _
    simp only [Work.Spaces.pzIter_succ, Work.Spaces.pzIter_zero, Work.Spaces.pz]
  rw [hpz, hint, hkey]
  field_simp
  ring

end Work.FTS.EllipticEst.DzAmgm
