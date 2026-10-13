import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Submission.Work.FTS.EllipticEst.TT.WeakDefs
import Submission.Work.FTS.EllipticEst.StraightDefs
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Spaces.mixed_comm

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
Copyright: work module for the Elgindi finite-time singularity project.

# `TT.ang_a_weak` — the angular (mixed) part of the level-`2` estimate for `A = z²∂_z²Ψ`

Target (`Work.FTS.EllipticEst.TT.ang_a_weak`): there is a universal `C > 0` with

```
∀ α F Ψ, 0 < α → α ≤ 1/4 → EllWeakPos α 2 F Ψ →
  α⁴ · ( |D_θ A · Wt α|²_{L²} + |D_z D_θ A · Wt α|²_{L²} + |D_θ² A · Wt α|²_{L²} ) ≤ C · |F|²_{ℋ²}
```

where `A := z²∂_z²Ψ = D_z²Ψ - D_zΨ` and `Wt α = w · sin(2θ)^{-γ/2}`.  The left-hand side is
exactly the *mixed* (`i ≥ 1`) part of `HkSq α 2 A`; the pure (`D_z`-only) part of that norm is
handled elsewhere (`est_two_weak`'s `pure_two_weak`).

## The identities provided here

Writing the equation `bslOp α Ψ = F` in the `D_z`-form
`-α²D_z²Ψ - 5αD_zΨ + LzeroΨ = F` (valid because `-(α²z²)∂_z²Ψ = -α²(D_z²Ψ - D_zΨ)`):

* `DzIter_two_split` : `D_z²Ψ = D_zΨ + z²∂_z²Ψ` on the open quadrant;
* `Lzero_eq_of_bsl` : `Lzero1 Ψ = F + α² D_z²Ψ + 5α D_zΨ` on the open quadrant.

The `θ`-derivative of the second identity,
`∂_θ(Lzero1 Ψ) = ∂_θF + α² D_z²(∂_θΨ) + 5α D_z(∂_θΨ)`
(equivalently `D_θ(Lzero1 Ψ) = D_θF + α² D_z²(D_θΨ) + 5α D_z(D_θΨ)`), together with
`α²A = Lzero1 Ψ - F - α(5+α)D_zΨ`, is what reduces every term of the target to

* a component of `|F|_{ℋ²}` (`D_θF`, `D_θ²F`, `D_zD_θF`), or
* a *slice* quantity controlled by the level-`0` (`η`-weighted) estimate for the data
  `(D_z^jΨ, D_z^jF)`, `j ≤ 2`, and for the datum `A`,
* or a term carrying an extra factor `α`.

Those level-`0` estimates are the content of `H2W/level0Ae` (the paper's Steps 1–3 of
`prop:H2`; its three inputs are delegated to `AngAWeak/step1Ae`, `AngAWeak/step2Ae`,
`AngAWeak/step3Ae`), and are *not* part of this file.
-/

noncomputable section

namespace Work.FTS.EllipticEst.TT

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- The angular operator of a `z`-slice is the corresponding slice of `Work.Elliptic.Lzero`. -/
theorem Lzero1_slice_eq (Ψ : ℝ → ℝ → ℝ) (z θ : ℝ) :
    Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ = Work.Elliptic.Lzero Ψ z θ := rfl

/-- The elementary split `D_z²Ψ = D_zΨ + z²∂_z²Ψ` on the open quadrant (product rule for
`z ↦ z ∂_zΨ`). -/
theorem DzIter_two_split {Ψ : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.DzIter 2 Ψ z θ
      = Work.Spaces.Dz Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ := by
  have hderiv : deriv (fun z' : ℝ => z' * Work.Spaces.pz Ψ z' θ) z
      = Work.Spaces.pz Ψ z θ + z * Work.Spaces.pzIter 2 Ψ z θ := by
    have h := ((hasDerivAt_id z).mul (hsm.hasDerivAt_slice_pzIter 1 hθ hz)).deriv
    have hfun : (fun z' : ℝ => z' * Work.Spaces.pz Ψ z' θ)
        = (id * fun z' : ℝ => Work.Spaces.pzIter 1 Ψ z' θ) := by
      funext z'
      simp only [Pi.mul_apply, id_eq]
      rfl
    rw [hfun, h]
    simp only [id_eq, one_mul]
    rfl
  have hfun : (fun z' : ℝ => Work.Spaces.Dz Ψ z' θ)
      = fun z' : ℝ => z' * Work.Spaces.pz Ψ z' θ := rfl
  show z * deriv (fun z' : ℝ => Work.Spaces.Dz Ψ z' θ) z
      = z * Work.Spaces.pz Ψ z θ + z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ
  rw [hfun, hderiv]
  ring

/-- **The equation in the `D_z`-form.**  On the open quadrant the `θ`-slice equation
`bslOp α Ψ = F` reads `Lzero1 Ψ = F + α² D_z²Ψ + 5α D_zΨ`. -/
theorem Lzero_eq_of_bsl {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ)
    (hEq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ
        = F z θ + α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ + 5 * α * Work.Spaces.Dz Ψ z θ := by
  intro z hz θ hθ0 hθ1
  have hsplit := DzIter_two_split hsm hz ⟨hθ0, hθ1⟩
  have heq := hEq z hz θ hθ0 hθ1
  rw [Work.Elliptic.bslOp_apply] at heq
  have hDz1 : Work.Spaces.Dz Ψ z θ = z * Work.Spaces.pz Ψ z θ := rfl
  have hL : Work.Elliptic.Lzero Ψ z θ
      = F z θ + α ^ 2 * (z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ)
        + α * (5 + α) * (z * Work.Spaces.pz Ψ z θ) := by linarith [heq]
  rw [Lzero1_slice_eq, hL, hsplit, hDz1]
  ring

/-- `∂_θ` commutes with `∂_z^n` on the open quadrant. -/
theorem pth_pzIter_eq {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f) :
    ∀ n : ℕ, ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (Work.Spaces.pzIter n f) z θ
        = Work.Spaces.pzIter n (Work.Spaces.pth f) z θ := by
  intro n
  induction n with
  | zero => intro z hz θ hθ0 hθ1; rfl
  | succ n ih =>
      intro z hz θ hθ0 hθ1
      have hnz : Set.Ioi (0 : ℝ) ∈ 𝓝 z := isOpen_Ioi.mem_nhds hz
      have hcd : ContDiffAt ℝ 2 (Function.uncurry (Work.Spaces.pzIter n f)) (z, θ) :=
        ((hsm.pzIter n).forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
          (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ0, hθ1⟩))
      have h1 : Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pzIter n f)) z θ
          = Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pzIter n f)) z θ :=
        (Work.Spaces.pz_pth_comm hcd).symm
      show Work.Spaces.pth (Work.Spaces.pz (Work.Spaces.pzIter n f)) z θ
          = Work.Spaces.pzIter (n + 1) (Work.Spaces.pth f) z θ
      rw [h1]
      have hev : (fun z' : ℝ => Work.Spaces.pth (Work.Spaces.pzIter n f) z' θ)
          =ᶠ[𝓝 z] fun z' : ℝ => Work.Spaces.pzIter n (Work.Spaces.pth f) z' θ := by
        filter_upwards [hnz] with z' hz'
        exact ih z' hz' θ hθ0 hθ1
      rw [show Work.Spaces.pz (Work.Spaces.pth (Work.Spaces.pzIter n f)) z θ
            = deriv (fun z' : ℝ => Work.Spaces.pth (Work.Spaces.pzIter n f) z' θ) z from rfl,
          Filter.EventuallyEq.deriv_eq hev]
      rfl

/-- `∂_θ` commutes with `D_z` on the open quadrant. -/
theorem pth_Dz_eq {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    Work.Spaces.pth (Work.Spaces.Dz f) z θ = Work.Spaces.Dz (Work.Spaces.pth f) z θ := by
  have hcd : ContDiffAt ℝ 2 (Function.uncurry f) (z, θ) :=
    ((hsm.forall 2).contDiffAt (Work.FTS.EllipticEst.isOpen_Q0.mem_nhds
      (Work.FTS.EllipticEst.mem_Q0.mpr ⟨hz, hθ.1, hθ.2⟩)))
  show deriv (fun θ' => z * Work.Spaces.pz f z θ') θ
      = z * Work.Spaces.pz (Work.Spaces.pth f) z θ
  rw [deriv_const_mul_field]
  change z * Work.Spaces.pth (Work.Spaces.pz f) z θ
      = z * Work.Spaces.pz (Work.Spaces.pth f) z θ
  rw [(Work.Spaces.pz_pth_comm hcd).symm]

/-- `∂_θ` commutes with `D_z²` on the open quadrant. -/
theorem pth_DzIter2_eq {f : ℝ → ℝ → ℝ} (hsm : Work.FTS.EllipticEst.SmoothOpen f)
    {z θ : ℝ} (hz : 0 < z) (hθ : θ ∈ Set.Ioo 0 (Real.pi / 2)) :
    deriv (fun θ' => Work.Spaces.DzIter 2 f z θ') θ
      = Work.Spaces.DzIter 2 (Work.Spaces.pth f) z θ := by
  have hnb : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hev : (fun θ' : ℝ => Work.Spaces.DzIter 2 f z θ')
      =ᶠ[𝓝 θ] fun θ' : ℝ => z * Work.Spaces.pzIter 1 f z θ'
        + z ^ 2 * Work.Spaces.pzIter 2 f z θ' := by
    filter_upwards [hnb] with θ' hθ'
    have h := DzIter_two_split hsm hz hθ'
    rw [h]
    rfl
  rw [Filter.EventuallyEq.deriv_eq hev]
  have hslice1 : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.pzIter 1 f z θ') θ :=
    (((hsm.pzIter 1).curry_θ hz) θ hθ).differentiableWithinAt (by decide) |>.differentiableAt hnb
  have hslice2 : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.pzIter 2 f z θ') θ :=
    (((hsm.pzIter 2).curry_θ hz) θ hθ).differentiableWithinAt (by decide) |>.differentiableAt hnb
  have hd1 : DifferentiableAt ℝ (fun θ' : ℝ => z * Work.Spaces.pzIter 1 f z θ') θ :=
    DifferentiableAt.const_mul hslice1 z
  have hd2 : DifferentiableAt ℝ (fun θ' : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ') θ :=
    DifferentiableAt.const_mul hslice2 (z ^ 2)
  rw [show (fun θ' : ℝ => z * Work.Spaces.pzIter 1 f z θ'
        + z ^ 2 * Work.Spaces.pzIter 2 f z θ')
      = ((fun θ' : ℝ => z * Work.Spaces.pzIter 1 f z θ')
        + fun θ' : ℝ => z ^ 2 * Work.Spaces.pzIter 2 f z θ') from rfl]
  rw [deriv_add hd1 hd2, deriv_const_mul_field, deriv_const_mul_field]
  rw [show deriv (Work.Spaces.pzIter 1 f z) θ
        = Work.Spaces.pth (Work.Spaces.pzIter 1 f) z θ from rfl,
      show deriv (Work.Spaces.pzIter 2 f z) θ
        = Work.Spaces.pth (Work.Spaces.pzIter 2 f) z θ from rfl,
      pth_pzIter_eq hsm 1 z hz θ hθ.1 hθ.2, pth_pzIter_eq hsm 2 z hz θ hθ.1 hθ.2]
  rw [DzIter_two_split (hsm.pth) hz hθ,
    show Work.Spaces.Dz (Work.Spaces.pth f) z θ
      = z * Work.Spaces.pzIter 1 (Work.Spaces.pth f) z θ from rfl]

/-- **The differentiated equation.**  On the open quadrant,
`∂_θ(Lzero1 Ψ) = ∂_θF + α² D_z²(∂_θΨ) + 5α D_z(∂_θΨ)`.

This is `Lzero_eq_of_bsl` differentiated in `θ`, with `∂_θ` pulled through `D_z`. -/
theorem pth_Lzero_eq_of_bsl {α : ℝ} {F Ψ : ℝ → ℝ → ℝ}
    (hsm : Work.FTS.EllipticEst.SmoothOpen Ψ) (hF : Work.FTS.EllipticEst.SmoothOpen F)
    (hEq : ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Elliptic.bslOp α Ψ z θ = F z θ) :
    ∀ z, 0 < z → ∀ θ, 0 < θ → θ < Real.pi / 2 →
      Work.Spaces.pth (fun z θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ) z θ
        = Work.Spaces.pth F z θ
          + α ^ 2 * Work.Spaces.DzIter 2 (Work.Spaces.pth Ψ) z θ
          + 5 * α * Work.Spaces.Dz (Work.Spaces.pth Ψ) z θ := by
  intro z hz θ hθ0 hθ1
  have hθ : θ ∈ Set.Ioo (0 : ℝ) (Real.pi / 2) := ⟨hθ0, hθ1⟩
  have hnb : Set.Ioo (0 : ℝ) (Real.pi / 2) ∈ 𝓝 θ := isOpen_Ioo.mem_nhds hθ
  have hev : (fun θ' : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ')
      =ᶠ[𝓝 θ] fun θ' : ℝ => F z θ' + α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ'
        + 5 * α * Work.Spaces.Dz Ψ z θ' := by
    filter_upwards [hnb] with θ' hθ'
    exact Lzero_eq_of_bsl hsm hEq z hz θ' hθ'.1 hθ'.2
  rw [show Work.Spaces.pth (fun z θ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ) z θ
        = deriv (fun θ' : ℝ => Work.FTS.EllipticEst.Lzero1 (fun t => Ψ z t) θ') θ from rfl,
      Filter.EventuallyEq.deriv_eq hev]
  have hsliceF : DifferentiableAt ℝ (fun θ' : ℝ => F z θ') θ :=
    (((hF.curry_θ hz) θ hθ).differentiableWithinAt (by decide)) |>.differentiableAt hnb
  have hslice2 : DifferentiableAt ℝ
      (fun θ' : ℝ => Work.Spaces.DzIter 2 Ψ z θ') θ :=
    (((hsm.DzIter 2).curry_θ hz) θ hθ).differentiableWithinAt (by decide) |>.differentiableAt hnb
  have hslice3 : DifferentiableAt ℝ (fun θ' : ℝ => Work.Spaces.Dz Ψ z θ') θ :=
    (((hsm.Dz).curry_θ hz) θ hθ).differentiableWithinAt (by decide) |>.differentiableAt hnb
  have hd1 : DifferentiableAt ℝ (fun θ' : ℝ => F z θ') θ := hsliceF
  have hd2 : DifferentiableAt ℝ (fun θ' : ℝ => α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ') θ :=
    DifferentiableAt.const_mul hslice2 (α ^ 2)
  have hd3 : DifferentiableAt ℝ (fun θ' : ℝ => 5 * α * Work.Spaces.Dz Ψ z θ') θ :=
    DifferentiableAt.const_mul hslice3 (5 * α)
  have hAB : DifferentiableAt ℝ (fun θ' : ℝ => F z θ'
      + α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ') θ := hd1.add hd2
  rw [show (fun θ' : ℝ => F z θ' + α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ'
        + 5 * α * Work.Spaces.Dz Ψ z θ')
      = ((fun θ' : ℝ => F z θ' + α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ')
        + fun θ' : ℝ => 5 * α * Work.Spaces.Dz Ψ z θ') from rfl]
  rw [deriv_add hAB hd3]
  rw [show (fun θ' : ℝ => F z θ' + α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ')
      = ((fun θ' : ℝ => F z θ')
        + fun θ' : ℝ => α ^ 2 * Work.Spaces.DzIter 2 Ψ z θ') from rfl]
  rw [deriv_add hd1 hd2, deriv_const_mul_field, deriv_const_mul_field]
  rw [show deriv (fun θ' : ℝ => Work.Spaces.DzIter 2 Ψ z θ') θ
        = Work.Spaces.DzIter 2 (Work.Spaces.pth Ψ) z θ from pth_DzIter2_eq hsm hz hθ,
      show deriv (fun θ' : ℝ => Work.Spaces.Dz Ψ z θ') θ
        = Work.Spaces.Dz (Work.Spaces.pth Ψ) z θ from pth_Dz_eq hsm hz hθ]
  rfl

theorem ang_a_weak : ∃ C : ℝ, 0 < C ∧
    ∀ (α : ℝ) (F Ψ : ℝ → ℝ → ℝ), 0 < α → α ≤ 1 / 4 →
      Work.FTS.EllipticEst.TT.EllWeakPos α 2 F Ψ →
      α ^ 4 * (Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * Work.Spaces.Wt α z θ)
        + Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 1 1
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * Work.Spaces.Wt α z θ)
        + Work.Spaces.L2Sq (fun z θ => Work.Spaces.mixed 0 2
            (fun z θ => z ^ 2 * Work.Spaces.pzIter 2 Ψ z θ) z θ * Work.Spaces.Wt α z θ))
      ≤ C * Work.Spaces.HkSq α 2 F := by sorry

end Work.FTS.EllipticEst.TT
