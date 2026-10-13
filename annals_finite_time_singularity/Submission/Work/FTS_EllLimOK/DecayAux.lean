/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.DecayAux` — tools for the `ZDecay` of a limit on the closed quadrant

`Work.FTS.EllipticEst.ZDecay Ψ` is a statement about the *plain* `θ`-derivatives
`pth Ψ z θ`, `pthIter 2 Ψ z θ` at **every** `θ ∈ Iθ = [0,π/2]`, including the two endpoints
`θ = 0` and `θ = π/2`.  For the limit function `Ψ` produced by the compactness argument, `Ψ` is
only known on the open quadrant, and the two endpoint slices are the ones where the *plain*
`θ`-derivative sees the (arbitrary) behaviour of the extension: if that extension is chosen to
vanish off the open strip — as the assembly of `ClosedCompact3` does — then the *one-sided*
difference quotients at `θ = 0` (resp. `θ = π/2`) are `0`, and Lean's `deriv` (which is the junk
value `0` when the two-sided derivative does not exist, and the unique limit when it does) must
therefore be `0`.

This module isolates that elementary fact and the two "one-sided vanishing" consequences used by
the decay estimate, together with the elementary squeezing lemma for limits at `+∞` against
`(1+z)^{-1}`.

Everything here is `sorry`-free and rests on `[propext, Classical.choice, Quot.sound]`.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

/-! ## The derivative at a one-sided vanishing point is `0` -/

/-- A function which vanishes on a left-neighbourhood of `x` and at `x` has `deriv 0` at `x`.

Lean's `deriv f x` is the (unique) limit of the two-sided slopes when it exists and the junk
value `0` otherwise.  On the left the slopes are identically `0` (since `f = 0` there and
`f x = 0`), so either the two-sided limit does not exist (junk `0`) or it exists and equals the
left limit `0`. -/
theorem deriv_eq_zero_of_eventuallyEq_zero_left {f : ℝ → ℝ} {x : ℝ} (hx : f x = 0)
    (h : ∀ᶠ t in nhdsWithin x (Set.Iio x), f t = 0) : deriv f x = 0 := by
  by_cases hd : DifferentiableAt ℝ f x
  · have h1 : derivWithin f (Set.Iio x) x = deriv f x :=
      (hd.hasDerivAt.hasDerivWithinAt).derivWithin (uniqueDiffWithinAt_Iio x)
    have hev : f =ᶠ[nhdsWithin x (Set.Iio x)] (fun _ => (0 : ℝ)) := by
      filter_upwards [h] with t ht
      exact ht
    have h2 : derivWithin f (Set.Iio x) x = 0 := by
      rw [hev.derivWithin_eq (show f x = (fun _ : ℝ => (0 : ℝ)) x from by simpa using hx)]
      simp
    linarith
  · rw [deriv, fderiv_zero_of_not_differentiableAt hd]
    rfl

/-- A function which vanishes on a right-neighbourhood of `x` and at `x` has `deriv 0` at `x`
(the mirror of `deriv_eq_zero_of_eventuallyEq_zero_left`). -/
theorem deriv_eq_zero_of_eventuallyEq_zero_right {f : ℝ → ℝ} {x : ℝ} (hx : f x = 0)
    (h : ∀ᶠ t in nhdsWithin x (Set.Ioi x), f t = 0) : deriv f x = 0 := by
  by_cases hd : DifferentiableAt ℝ f x
  · have h1 : derivWithin f (Set.Ioi x) x = deriv f x :=
      (hd.hasDerivAt.hasDerivWithinAt).derivWithin (uniqueDiffWithinAt_Ioi x)
    have hev : f =ᶠ[nhdsWithin x (Set.Ioi x)] (fun _ => (0 : ℝ)) := by
      filter_upwards [h] with t ht
      exact ht
    have h2 : derivWithin f (Set.Ioi x) x = 0 := by
      rw [hev.derivWithin_eq (show f x = (fun _ : ℝ => (0 : ℝ)) x from by simpa using hx)]
      simp
    linarith
  · rw [deriv, fderiv_zero_of_not_differentiableAt hd]
    rfl

/-! ## The endpoint `θ`-derivatives of a function vanishing off the open strip -/

/-- If `Ψ` vanishes at every angle outside the open strip `(0,π/2)`, then its `θ`-slice at
`θ = 0` vanishes on a left-neighbourhood of `0`, and hence `pth Ψ z 0 = 0`. -/
theorem pth_eq_zero_of_vanishing_left {Ψ : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, θ ∉ Set.Ioo (0 : ℝ) (π / 2) → Ψ z θ = 0) (z : ℝ) :
    Work.Spaces.pth Ψ z 0 = 0 := by
  refine deriv_eq_zero_of_eventuallyEq_zero_left (h z 0 (by simp)) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact h z t (by
    simp only [Set.mem_Iio] at ht
    intro hmem
    exact absurd hmem.1 (not_lt.mpr ht.le))

/-- If `Ψ` vanishes at every angle outside the open strip `(0,π/2)`, then
`pth Ψ z (π/2) = 0`. -/
theorem pth_eq_zero_of_vanishing_right {Ψ : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, θ ∉ Set.Ioo (0 : ℝ) (π / 2) → Ψ z θ = 0) (z : ℝ) :
    Work.Spaces.pth Ψ z (π / 2) = 0 := by
  refine deriv_eq_zero_of_eventuallyEq_zero_right (h z (π / 2) (by simp)) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact h z t (by
    simp only [Set.mem_Ioi] at ht
    intro hmem
    exact absurd hmem.2 (not_lt.mpr ht.le))

/-- If `Ψ` vanishes at every angle outside the open strip `(0,π/2)`, then `pth Ψ z θ = 0` for
every `θ < 0`. -/
theorem pth_eq_zero_of_lt_zero {Ψ : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, θ ∉ Set.Ioo (0 : ℝ) (π / 2) → Ψ z θ = 0) (z θ : ℝ) (hθ : θ < 0) :
    Work.Spaces.pth Ψ z θ = 0 := by
  have h0 : (fun θ' : ℝ => Ψ z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Iio.mem_nhds hθ] with t ht
    exact h z t (by
      intro hmem
      exact absurd hmem.1 (not_lt.mpr ht.le))
  have h1 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 θ := hasDerivAt_const θ 0
  have := h1.congr_of_eventuallyEq h0
  simpa [Work.Spaces.pth] using this.deriv

/-- If `Ψ` vanishes at every angle outside the open strip `(0,π/2)`, then `pth Ψ z θ = 0` for
every `θ > π/2`. -/
theorem pth_eq_zero_of_pi_div_two_lt {Ψ : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, θ ∉ Set.Ioo (0 : ℝ) (π / 2) → Ψ z θ = 0) (z θ : ℝ) (hθ : π / 2 < θ) :
    Work.Spaces.pth Ψ z θ = 0 := by
  have h0 : (fun θ' : ℝ => Ψ z θ') =ᶠ[𝓝 θ] (fun _ => (0 : ℝ)) := by
    filter_upwards [isOpen_Ioi.mem_nhds hθ] with t ht
    exact h z t (by
      intro hmem
      exact absurd hmem.2 (not_lt.mpr ht.le))
  have h1 : HasDerivAt (fun _ : ℝ => (0 : ℝ)) 0 θ := hasDerivAt_const θ 0
  have := h1.congr_of_eventuallyEq h0
  simpa [Work.Spaces.pth] using this.deriv

/-- If `Ψ` vanishes at every angle outside the open strip `(0,π/2)`, then
`pthIter 2 Ψ z 0 = 0`. -/
theorem pthIter_two_eq_zero_of_vanishing_left {Ψ : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, θ ∉ Set.Ioo (0 : ℝ) (π / 2) → Ψ z θ = 0) (z : ℝ) :
    Work.Spaces.pthIter 2 Ψ z 0 = 0 := by
  show deriv (fun θ' : ℝ => Work.Spaces.pth Ψ z θ') 0 = 0
  refine deriv_eq_zero_of_eventuallyEq_zero_left
    (show Work.Spaces.pth Ψ z 0 = 0 from pth_eq_zero_of_vanishing_left h z) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact pth_eq_zero_of_lt_zero h z t (by simpa [Set.mem_Iio] using ht)

/-- If `Ψ` vanishes at every angle outside the open strip `(0,π/2)`, then
`pthIter 2 Ψ z (π/2) = 0`. -/
theorem pthIter_two_eq_zero_of_vanishing_right {Ψ : ℝ → ℝ → ℝ}
    (h : ∀ z θ : ℝ, θ ∉ Set.Ioo (0 : ℝ) (π / 2) → Ψ z θ = 0) (z : ℝ) :
    Work.Spaces.pthIter 2 Ψ z (π / 2) = 0 := by
  show deriv (fun θ' : ℝ => Work.Spaces.pth Ψ z θ') (π / 2) = 0
  refine deriv_eq_zero_of_eventuallyEq_zero_right
    (show Work.Spaces.pth Ψ z (π / 2) = 0 from pth_eq_zero_of_vanishing_right h z) ?_
  filter_upwards [self_mem_nhdsWithin] with t ht
  exact pth_eq_zero_of_pi_div_two_lt h z t (by simpa [Set.mem_Ioi] using ht)

/-! ## Squeezing at `+∞` -/

/-- `(1+z)^{-1} → 0` as `z → +∞`. -/
theorem tendsto_one_add_inv_zero : Tendsto (fun z : ℝ => (1 + z)⁻¹) atTop (𝓝 0) := by
  have h : Tendsto (fun z : ℝ => z + 1) atTop atTop :=
    tendsto_atTop_add_const_right atTop (1 : ℝ) tendsto_id
  have h' : Tendsto (fun z : ℝ => (z + 1)⁻¹) atTop (𝓝 0) := h.inv_tendsto_atTop
  simpa only [add_comm] using h'

/-- If `|g z| ≤ C/(1+z)` eventually, then `g z → 0` as `z → +∞`. -/
theorem tendsto_zero_of_abs_le_inv {g : ℝ → ℝ} {C : ℝ} (hC : 0 ≤ C)
    (h : ∀ᶠ z in atTop, |g z| ≤ C / (1 + z)) : Tendsto g atTop (𝓝 0) := by
  have hbound : Tendsto (fun z : ℝ => C / (1 + z)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun z : ℝ => C * (1 + z)⁻¹) atTop (𝓝 (C * 0)) :=
      tendsto_one_add_inv_zero.const_mul C
    rw [mul_zero] at h1
    simpa only [div_eq_mul_inv] using h1
  have hneg : Tendsto (fun z : ℝ => -(C / (1 + z))) atTop (𝓝 0) := by
    have := hbound.neg
    rwa [neg_zero] at this
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hneg hbound ?_ ?_
  · filter_upwards [h] with z hz
    simpa only [neg_div] using neg_le_of_abs_le hz
  · filter_upwards [h] with z hz
    exact le_of_abs_le hz

end Work.FTS_EllLimOK
