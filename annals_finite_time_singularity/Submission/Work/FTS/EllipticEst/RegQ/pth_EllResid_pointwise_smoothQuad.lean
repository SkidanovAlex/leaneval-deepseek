import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Topology.Algebra.Module.ModuleTopology
import Submission.Work.FTS.LocData.Defs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.LocData.SmoothChain

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.EllipticEst.RegQ

open scoped Real Topology
open Filter

set_option autoImplicit false

/-!
# The two `θ`-derivatives of the residual `EllResid α F Ψ` in the class `SmoothQuad`

`EllResid α F Ψ = fun z θ => Ψ z θ - (1/(4α)) · sin(2θ) · L₁₂(F)(z)` is a `Ψ`-part, which is
`C^∞` on the open quadrant, minus a *radial* function `L₁₂(F)` times the *angular* profile
`sin 2θ`.  Differentiating in `θ` therefore only sees the angular factor:

  `∂_θ (EllResid α F Ψ)   = ∂_θΨ   - (1/(4α))·2cos 2θ·L₁₂(F)`,
  `∂_θ² (EllResid α F Ψ)  = ∂_θ²Ψ  + (1/α)·(sin 2θ·L₁₂(F))`.

This file proves both, *pointwise on the open quadrant* `z > -1`, `0 < θ < π/2`, from the only
smoothness hypothesis that is available in the localised-data chapter: `SmoothQuad Ψ` (genuine
`C^∞` on `Ioi (-1) ×ˢ Ioo 0 (π/2)`, i.e. `ContDiffOn ℝ smoothOrder`).  Nothing is assumed about
`F`: only `L₁₂(F)(z)` as a number occurs, and it is treated as a constant in `θ`.

Everything rests on `[propext, Classical.choice, Quot.sound]`.
-/

noncomputable section

/-! ## Auxiliary calculus: `SmoothQuad` and the `θ`-slices of the `∂_θ`-iterates -/

/-- `Work.Spaces.pth` preserves `SmoothQuad` (`C^∞`-smoothness on the open quadrant
`z > -1`, `0 < θ < π/2`). -/
private theorem smoothQuad_pth_aux {G : ℝ → ℝ → ℝ} (hG : Work.FTS.LocData.SmoothQuad G) :
    Work.FTS.LocData.SmoothQuad (Work.Spaces.pth G) :=
  Work.FTS.LocData.contDiffOn_pth Work.FTS.LocData.isOpen_quadU hG

/-- Every iterated `∂_θ`-derivative of a `SmoothQuad` function is `SmoothQuad`. -/
private theorem smoothQuad_pthIter_aux {G : ℝ → ℝ → ℝ} (hG : Work.FTS.LocData.SmoothQuad G)
    (n : ℕ) : Work.FTS.LocData.SmoothQuad (Work.Spaces.pthIter n G) := by
  induction n with
  | zero => simpa using hG
  | succ n ih => rw [Work.Spaces.pthIter_succ]; exact smoothQuad_pth_aux ih

/-- **The `θ`-derivative of the `θ`-slice of `∂_θ^n f`.**  For `SmoothQuad f` and an interior
point of the open quadrant, the slice `θ' ↦ ∂_θ^n f z θ'` has derivative `∂_θ^{n+1} f z θ`
(the plain partial `∂_θ`). -/
private theorem hasDerivAt_slice_pthIter_aux {G : ℝ → ℝ → ℝ}
    (hG : Work.FTS.LocData.SmoothQuad G) (n : ℕ) {z θ : ℝ} (hz : -1 < z)
    (hθ0 : 0 < θ) (hθ1 : θ < Real.pi / 2) :
    HasDerivAt (fun θ' : ℝ => Work.Spaces.pthIter n G z θ')
      (Work.Spaces.pthIter (n + 1) G z θ) θ := by
  have hcurl : Work.FTS.LocData.SmoothQuad (Work.Spaces.pthIter n G) :=
    smoothQuad_pthIter_aux hG n
  have hd : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.pthIter n G z θ') θ :=
    ((hcurl.curry_θ hz).differentiableOn
      Work.FTS.LocData.smoothOrder_ne_zero).differentiableAt
      (isOpen_Ioo.mem_nhds ⟨hθ0, hθ1⟩)
  simpa only [Work.Spaces.pthIter_succ, Work.Spaces.pth] using hd.hasDerivAt

/-! ## Auxiliary calculus: the two elementary angular profiles -/

/-- `deriv (fun θ' => sin (2 θ')) θ = 2 cos (2 θ)`. -/
private theorem hasDerivAt_sin_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => Real.sin (2 * θ')) (2 * Real.cos (2 * θ)) θ := by
  simpa [Function.comp_def, mul_comm] using
    (Real.hasDerivAt_sin (2 * θ)).comp θ
      ((hasDerivAt_const (x := θ) (c := (2 : ℝ))).mul (hasDerivAt_id θ))

/-- `deriv (fun θ' => 2 cos (2 θ')) θ = -4 sin (2 θ)`. -/
private theorem hasDerivAt_two_cos_two (θ : ℝ) :
    HasDerivAt (fun θ' : ℝ => 2 * Real.cos (2 * θ')) (-(4 * Real.sin (2 * θ))) θ := by
  have h1 : HasDerivAt (fun θ' : ℝ => Real.cos (2 * θ')) (-(2 * Real.sin (2 * θ))) θ := by
    simpa [Function.comp_def, mul_comm, mul_assoc] using
      (Real.hasDerivAt_cos (2 * θ)).comp θ
        ((hasDerivAt_const (x := θ) (c := (2 : ℝ))).mul (hasDerivAt_id θ))
  have h2 := h1.const_mul (2 : ℝ)
  have he : (2 : ℝ) * (-(2 * Real.sin (2 * θ))) = -(4 * Real.sin (2 * θ)) := by ring
  rwa [he] at h2

/-! ## The first `θ`-derivative of the residual -/

/-- **`∂_θ (EllResid α F Ψ) = ∂_θΨ - (1/(4α))·2 cos 2θ·L₁₂(F)`** on the open quadrant. -/
private theorem pth_EllResid_aux (α : ℝ) (F Ψ : ℝ → ℝ → ℝ)
    (hΨ : Work.FTS.LocData.SmoothQuad Ψ) :
    ∀ z θ, -1 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z θ
        = Work.Spaces.pth Ψ z θ
          - (1 / (4 * α)) * (2 * Real.cos (2 * θ)) * Work.Elliptic.L12 F z := by
  intro z θ hz hθ0 hθ1
  -- the `θ`-slice of `Ψ` at this `z`
  have hslice : HasDerivAt (fun θ' : ℝ => Ψ z θ') (Work.Spaces.pth Ψ z θ) θ := by
    have h := hasDerivAt_slice_pthIter_aux hΨ 0 hz hθ0 hθ1
    simpa using h
  -- the singular part is a constant multiple of `sin (2 θ')`
  have hprod := (hasDerivAt_sin_two θ).const_mul (1 / (4 * α))
  have hprod' := hprod.mul_const (Work.Elliptic.L12 F z)
  have hd := hslice.sub hprod'
  have hdeq : ((fun θ' : ℝ => Ψ z θ')
          - (fun θ' : ℝ => ((1 / (4 * α)) * Real.sin (2 * θ'))
              * Work.Elliptic.L12 F z))
      = (fun θ' : ℝ => Ψ z θ'
        - ((1 / (4 * α)) * Real.sin (2 * θ')) * Work.Elliptic.L12 F z) := by
    funext θ'
    simp only [Pi.sub_apply]
  rw [hdeq] at hd
  have hfin : Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z θ
      = deriv (fun θ' : ℝ => Ψ z θ'
          - ((1 / (4 * α)) * Real.sin (2 * θ')) * Work.Elliptic.L12 F z) θ := by
    simp only [Work.Spaces.pth, Work.Elliptic.EllResid, Pi.sub_apply]
  rw [hfin, hd.deriv]

/-! ## The second `θ`-derivative of the residual -/

/-- **`∂_θ² (EllResid α F Ψ) = ∂_θ²Ψ + (1/α)·(sin 2θ·L₁₂(F))`** on the open quadrant. -/
private theorem pthIter2_EllResid_aux (α : ℝ) (hα : 0 < α) (F Ψ : ℝ → ℝ → ℝ)
    (hΨ : Work.FTS.LocData.SmoothQuad Ψ) :
    ∀ z θ, -1 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
        = Work.Spaces.pthIter 2 Ψ z θ
          + (1 / α) * (Real.sin (2 * θ) * Work.Elliptic.L12 F z) := by
  intro z θ hz hθ0 hθ1
  -- the first derivative as a function of `θ'`, on the whole angular interval
  have hstep1 : ∀ θ' : ℝ, 0 < θ' → θ' < Real.pi / 2 →
      Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z θ'
        = Work.Spaces.pth Ψ z θ'
          - ((1 / (4 * α)) * (2 * Real.cos (2 * θ'))) * Work.Elliptic.L12 F z := by
    intro θ' h0 h1
    exact pth_EllResid_aux α F Ψ hΨ z θ' hz h0 h1
  -- eventually equal to `∂_θΨ` minus the explicit profile
  have hev : (fun θ' : ℝ => Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z θ')
      =ᶠ[𝓝 θ] (fun θ' : ℝ => Work.Spaces.pth Ψ z θ'
        - ((1 / (4 * α)) * (2 * Real.cos (2 * θ'))) * Work.Elliptic.L12 F z) := by
    filter_upwards [isOpen_Ioo.mem_nhds ⟨hθ0, hθ1⟩] with θ' hθ'
    exact hstep1 θ' hθ'.1 hθ'.2
  have hmain : Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
      = deriv (fun θ' : ℝ => Work.Spaces.pth Ψ z θ'
          - ((1 / (4 * α)) * (2 * Real.cos (2 * θ'))) * Work.Elliptic.L12 F z) θ := by
    show deriv (fun θ' : ℝ => Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z θ') θ = _
    rw [Filter.EventuallyEq.deriv_eq hev]
  -- the derivative of the `Ψ`-part
  have hslice2 : HasDerivAt (fun θ' : ℝ => Work.Spaces.pth Ψ z θ')
      (Work.Spaces.pthIter 2 Ψ z θ) θ := by
    have h := hasDerivAt_slice_pthIter_aux hΨ 1 hz hθ0 hθ1
    simpa using h
  -- the derivative of the explicit singular profile
  have hd2 : HasDerivAt (fun θ' : ℝ =>
        ((1 / (4 * α)) * (2 * Real.cos (2 * θ'))) * Work.Elliptic.L12 F z)
      (((1 / (4 * α)) * (-(4 * Real.sin (2 * θ)))) * Work.Elliptic.L12 F z) θ :=
    (hasDerivAt_two_cos_two θ).const_mul (1 / (4 * α))
      |>.mul_const (Work.Elliptic.L12 F z)
  have hdsub := hslice2.sub hd2
  have hdeq : (fun θ' : ℝ => Work.Spaces.pth Ψ z θ'
        - ((1 / (4 * α)) * (2 * Real.cos (2 * θ'))) * Work.Elliptic.L12 F z)
      = ((fun θ' : ℝ => Work.Spaces.pth Ψ z θ')
          - (fun θ' : ℝ => ((1 / (4 * α)) * (2 * Real.cos (2 * θ')))
              * Work.Elliptic.L12 F z)) := by
    funext θ'
    simp only [Pi.sub_apply]
  rw [hmain, hdeq, hdsub.deriv]
  have hkey : ((1 / (4 * α)) * (-(4 * Real.sin (2 * θ)))) * Work.Elliptic.L12 F z
      = -((1 / α) * (Real.sin (2 * θ) * Work.Elliptic.L12 F z)) := by
    have hαne : α ≠ 0 := ne_of_gt hα
    field_simp
    try ring
  rw [hkey]
  ring

/-! ## The requested statement -/

/-- **The two pointwise `θ`-derivative identities for the residual, in the class `SmoothQuad`.**

For `Ψ` of class `C^∞` on the open quadrant `z > -1`, `0 < θ < π/2`, and any `α > 0`, `F`:

* `∂_θ (Ψ - (1/(4α)) sin 2θ · L₁₂(F)) = ∂_θΨ - (1/(4α))·2cos 2θ·L₁₂(F)`;
* `∂_θ² (Ψ - (1/(4α)) sin 2θ · L₁₂(F)) = ∂_θ²Ψ + (1/α)·(sin 2θ·L₁₂(F))`. -/
theorem pth_EllResid_pointwise_smoothQuad (α : ℝ) (hα : 0 < α) (F Ψ : ℝ → ℝ → ℝ)
    (hΨ : Work.FTS.LocData.SmoothQuad Ψ) :
    (∀ z θ, -1 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (Work.Elliptic.EllResid α F Ψ) z θ
        = Work.Spaces.pth Ψ z θ
          - (1 / (4 * α)) * (2 * Real.cos (2 * θ)) * Work.Elliptic.L12 F z) ∧
    (∀ z θ, -1 < z → 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pthIter 2 (Work.Elliptic.EllResid α F Ψ) z θ
        = Work.Spaces.pthIter 2 Ψ z θ
          + (1 / α) * (Real.sin (2 * θ) * Work.Elliptic.L12 F z)) :=
  ⟨pth_EllResid_aux α F Ψ hΨ, pthIter2_EllResid_aux α hα F Ψ hΨ⟩

end

end Work.FTS.EllipticEst.RegQ
