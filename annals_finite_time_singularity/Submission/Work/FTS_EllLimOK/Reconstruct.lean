/-
Copyright: work module for the Elgindi finite-time singularity project.

# `FTS_EllLimOK.Reconstruct` — the algebraic identities and the `Vop`-reconstruction

The elliptic packages bound the three *coefficient* operators of the self-similar vorticity
equation

```
Uop α Ψ = -3Ψ - α z ∂_zΨ ,      Vop Ψ = ∂_θΨ - tan θ · Ψ ,
Rop α Ψ = (2 sin θ · Ψ + α sin θ · z ∂_zΨ + cos θ · ∂_θΨ) / cos θ
```

applied to `Φ̃ = PhiTil α g (E g)`, and nothing else.  To get back from the coefficients to the
*function* `Φ̃` one uses the two first-order systems

* `cos θ · Vop Ψ = ∂_θ (cos θ · Ψ)` — an ODE in `θ`, solved by
  `Ψ(z,θ) = -(1/cos θ) ∫_θ^{π/2} cos s · (Vop Ψ)(z,s) ds`  (the Dirichlet value `Ψ(z,π/2) = 0`),
* `Uop α Ψ = -3Ψ - α z ∂_zΨ` — an ODE in `z`,

and the two coefficients are not independent:

```
cos θ · Rop α Ψ = cos θ · Vop Ψ - sin θ · Uop α Ψ .
```

This module proves the **algebraic** part of that dictionary (no differentiability hypotheses
needed: the identities are identities between the totalised derivatives `pth`, `pz`) and the
`θ`-reconstruction `Vop_reconstruct` as an instance of the fundamental theorem of calculus.

The reconstruction is stated for the *boundary limit* `cos s · Ψ(z,s) → 0` as `s → π/2⁻` as a
hypothesis, not derived: `SmoothOpen` constrains `Ψ` on the **open** quadrant only, and the
packages give the *value* `Ψ(z,π/2) = 0` but not the continuity of the slice there.  In the
repaired interface (see `REPLY_LEAD2.md` §3) the solution carries a closed-quadrant regularity
clause, which is what discharges this hypothesis; for the genuine elliptic solution the limit
does hold (`cos s · Φ̃(z,s) = O((π/2-s)²)`).
-/
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Submission.Work.Construction.Defs
import Submission.Work.Spaces.Defs
import Submission.Work.FTS.EllipticEst.OpenQDefs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false
set_option maxHeartbeats 800000

/-- `cos θ` is positive on the open quadrant's angular range. -/
theorem cos_pos_of_mem_Ioo {θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) : 0 < Real.cos θ :=
  Real.cos_pos_of_mem_Ioo ⟨by linarith [hθ.1, Real.pi_pos], hθ.2⟩

/-! ## The algebraic identities between the three coefficient operators -/

/-- `cos θ · Vop Ψ = ∂_θ (cos θ · Ψ)`, in the totalised-derivative form
`cos θ · Vop Ψ = cos θ · ∂_θΨ - sin θ · Ψ`. -/
theorem cos_mul_Vop_eq (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.cos θ * Work.Construction.Vop Ψ z θ
      = Real.cos θ * Work.Spaces.pth Ψ z θ - Real.sin θ * Ψ z θ := by
  have hc : Real.cos θ ≠ 0 := ne_of_gt (cos_pos_of_mem_Ioo hθ)
  rw [Work.Construction.Vop, Real.tan_eq_sin_div_cos]
  field_simp

/-- The compatibility of the three coefficients: `Rop` carries no information beyond `(Uop,Vop)`.
-/
theorem cos_mul_Rop_eq (α : ℝ) (Ψ : ℝ → ℝ → ℝ) {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2)) :
    Real.cos θ * Work.Construction.Rop α Ψ z θ
      = Real.cos θ * Work.Construction.Vop Ψ z θ
        - Real.sin θ * Work.Construction.Uop α Ψ z θ := by
  have hc : Real.cos θ ≠ 0 := ne_of_gt (cos_pos_of_mem_Ioo hθ)
  rw [Work.Construction.Rop, Work.Construction.Vop, Work.Construction.Uop,
    Real.tan_eq_sin_div_cos]
  field_simp
  all_goals ring

/-- `Vop` is the θ-derivative minus `tan θ · Ψ` (the defining identity, as an equality of
functions — what the reconstruction integrates). -/
theorem Vop_eq_sub (Ψ : ℝ → ℝ → ℝ) :
    Work.Construction.Vop Ψ
      = fun z θ => Work.Spaces.pth Ψ z θ - Real.tan θ * Ψ z θ := rfl

/-! ## The `θ`-reconstruction -/

/-- **The reconstruction of `Ψ` from `Vop Ψ`.**  If the slice `s ↦ Ψ z s` has derivative
`∂_θΨ(z,s)` on the open interval `(θ,π/2)`, if `cos s · Vop Ψ(z,s)` is interval-integrable, if
the slice is continuous at `θ` and if the boundary limit `cos s · Ψ(z,s) → 0` holds as
`s → π/2⁻`, then

```
Ψ(z,θ) = -(1/cos θ) · ∫_θ^{π/2} cos s · (Vop Ψ)(z,s) ds .
```

This is the fundamental theorem of calculus applied to `s ↦ cos s · Ψ(z,s)`, whose derivative is
`cos s · Vop Ψ(z,s)` by `cos_mul_Vop_eq`. -/
theorem Vop_reconstruct {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hderiv : ∀ s ∈ Set.Ioo θ (π / 2),
      HasDerivAt (fun s' => Ψ z s') (Work.Spaces.pth Ψ z s) s)
    (hint : IntervalIntegrable (fun s => Real.cos s * Work.Construction.Vop Ψ z s)
      MeasureTheory.volume θ (π / 2))
    (ha : Filter.Tendsto (fun s => Real.cos s * Ψ z s) (𝓝[>] θ) (𝓝 (Real.cos θ * Ψ z θ)))
    (hb : Filter.Tendsto (fun s => Real.cos s * Ψ z s) (𝓝[<] (π / 2)) (𝓝 0)) :
    Ψ z θ = -(1 / Real.cos θ)
      * ∫ s in θ..(π / 2), Real.cos s * Work.Construction.Vop Ψ z s := by
  have hθlt : θ < π / 2 := hθ.2
  have hcos : Real.cos θ ≠ 0 := ne_of_gt (cos_pos_of_mem_Ioo hθ)
  -- the derivative identity on the open interval
  have hderiv' : ∀ s ∈ Set.Ioo θ (π / 2),
      HasDerivAt (fun s' => Real.cos s' * Ψ z s')
        (Real.cos s * Work.Construction.Vop Ψ z s) s := by
    intro s hs
    have hsIoo : s ∈ Set.Ioo 0 (π / 2) := ⟨lt_trans hθ.1 hs.1, hs.2⟩
    have h3 : HasDerivAt (fun s' => Real.cos s' * Ψ z s')
        (-Real.sin s * Ψ z s + Real.cos s * Work.Spaces.pth Ψ z s) s :=
      (Real.hasDerivAt_cos s).mul (hderiv s hs)
    refine h3.congr_deriv ?_
    rw [cos_mul_Vop_eq Ψ hsIoo]
    ring
  have hFTC := intervalIntegral.integral_eq_sub_of_hasDerivAt_of_tendsto hθlt hderiv' hint ha hb
  -- `∫ = 0 - cos θ * Ψ z θ`
  have h1 : Ψ z θ * Real.cos θ
      = -∫ s in θ..(π / 2), Real.cos s * Work.Construction.Vop Ψ z s := by
    rw [show (∫ s in θ..(π / 2), Real.cos s * Work.Construction.Vop Ψ z s)
        = 0 - Real.cos θ * Ψ z θ from hFTC]
    ring
  have h2 : Ψ z θ
      = (-∫ s in θ..(π / 2), Real.cos s * Work.Construction.Vop Ψ z s) / Real.cos θ := by
    rw [eq_div_iff hcos]
    exact h1
  rw [h2]
  ring

/-- The same reconstruction from the *value* `Ψ(z,π/2) = 0` plus continuity of the slice at
`π/2⁻` (which is how the Dirichlet condition of `IsBslSolPos` is used). -/
theorem Vop_reconstruct_of_tendsto {Ψ : ℝ → ℝ → ℝ} {z θ : ℝ} (hθ : θ ∈ Set.Ioo 0 (π / 2))
    (hderiv : ∀ s ∈ Set.Ioo θ (π / 2),
      HasDerivAt (fun s' => Ψ z s') (Work.Spaces.pth Ψ z s) s)
    (hint : IntervalIntegrable (fun s => Real.cos s * Work.Construction.Vop Ψ z s)
      MeasureTheory.volume θ (π / 2))
    (ha : Filter.Tendsto (fun s => Real.cos s * Ψ z s) (𝓝[>] θ) (𝓝 (Real.cos θ * Ψ z θ)))
    (hcont : Filter.Tendsto (fun s => Ψ z s) (𝓝[<] (π / 2)) (𝓝 0)) :
    Ψ z θ = -(1 / Real.cos θ)
      * ∫ s in θ..(π / 2), Real.cos s * Work.Construction.Vop Ψ z s := by
  refine Vop_reconstruct hθ hderiv hint ha ?_
  have : Filter.Tendsto (fun s => Real.cos s * Ψ z s) (𝓝[<] (π / 2))
      (𝓝 (Real.cos (π / 2) * (0 : ℝ))) :=
    (Real.continuous_cos.continuousWithinAt.tendsto.mul hcont)
  simpa using this

end Work.FTS_EllLimOK
