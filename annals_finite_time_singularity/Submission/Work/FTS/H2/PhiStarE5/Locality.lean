/-
# `PhiStarE5` — locality of `bslOp`

`bslOp α Ψ z θ` is a combination of the derivatives of the slices of `Ψ` at `(z,θ)`, so it only
depends on the germ of `Ψ` at `(z,θ)`:

  `Ψ₁ =ᶠ[𝓝 (z,θ)] Ψ₂  ⟹  bslOp α Ψ₁ z θ = bslOp α Ψ₂ z θ`.

This is what lets one redefine a solution off the open quadrant (e.g. to force the Dirichlet data
on the two boundary lines) without changing the equation inside the quadrant.
-/
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.EllipticEst.OpenQDefs
import Submission.Work.Elliptic.Defs
import Submission.Work.Spaces.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.FTS.H2.PhiStarE5

open scoped Real Topology
open MeasureTheory Set Filter

set_option autoImplicit false
noncomputable section

/-- **Locality of `bslOp`**: two functions agreeing on a neighbourhood of `(z,θ)` have the same
`bslOp`-value at `(z,θ)`. -/
theorem bslOp_congr_of_eventuallyEq (α : ℝ) {Ψ₁ Ψ₂ : ℝ → ℝ → ℝ} {z θ : ℝ}
    (h : ∀ᶠ q in 𝓝 (z, θ), Ψ₁ q.1 q.2 = Ψ₂ q.1 q.2) :
    Work.Elliptic.bslOp α Ψ₁ z θ = Work.Elliptic.bslOp α Ψ₂ z θ := by
  obtain ⟨V, hVsub, hVopen, hzθV⟩ := mem_nhds_iff.mp h
  have hVz : ∀ᶠ z' in 𝓝 z, (z', θ) ∈ V :=
    (hVopen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hzθV
  have hVt : ∀ᶠ θ' in 𝓝 θ, (z, θ') ∈ V :=
    (hVopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hzθV
  have hevZ : (fun z' => Ψ₁ z' θ) =ᶠ[𝓝 z] (fun z' => Ψ₂ z' θ) :=
    hVz.mono (fun z' hz' => hVsub hz')
  have hevT : (fun θ' => Ψ₁ z θ') =ᶠ[𝓝 θ] (fun θ' => Ψ₂ z θ') :=
    hVt.mono (fun θ' hθ' => hVsub hθ')
  -- first `z`-derivative
  have hevZ1 : (fun z' => Work.Spaces.pz Ψ₁ z' θ) =ᶠ[𝓝 z]
      (fun z' => Work.Spaces.pz Ψ₂ z' θ) := by
    filter_upwards [hVz] with z' hz'
    have hmem : ∀ᶠ z'' in 𝓝 z', (z'', θ) ∈ V :=
      (hVopen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hz'
    have hev : (fun z'' => Ψ₁ z'' θ) =ᶠ[𝓝 z'] (fun z'' => Ψ₂ z'' θ) :=
      hmem.mono (fun z'' hz'' => hVsub hz'')
    rw [show Work.Spaces.pz Ψ₁ z' θ = deriv (fun z'' => Ψ₁ z'' θ) z' from rfl,
      show Work.Spaces.pz Ψ₂ z' θ = deriv (fun z'' => Ψ₂ z'' θ) z' from rfl]
    exact Filter.EventuallyEq.deriv_eq hev
  -- second `z`-derivative
  have hevZ2 : (fun z' => Work.Spaces.pzIter 2 Ψ₁ z' θ) =ᶠ[𝓝 z]
      (fun z' => Work.Spaces.pzIter 2 Ψ₂ z' θ) := by
    filter_upwards [hVz] with z' hz'
    have hmem : ∀ᶠ z'' in 𝓝 z', (z'', θ) ∈ V :=
      (hVopen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hz'
    have hev : (fun z'' => Work.Spaces.pz Ψ₁ z'' θ) =ᶠ[𝓝 z']
        (fun z'' => Work.Spaces.pz Ψ₂ z'' θ) := by
      filter_upwards [hmem] with z'' hz''
      have hmem2 : ∀ᶠ z₃ in 𝓝 z'', (z₃, θ) ∈ V :=
        (hVopen.preimage (continuous_id.prodMk continuous_const)).mem_nhds hz''
      have hev2 : (fun z₃ => Ψ₁ z₃ θ) =ᶠ[𝓝 z''] (fun z₃ => Ψ₂ z₃ θ) :=
        hmem2.mono (fun z₃ hz₃ => hVsub hz₃)
      rw [show Work.Spaces.pz Ψ₁ z'' θ = deriv (fun z₃ => Ψ₁ z₃ θ) z'' from rfl,
        show Work.Spaces.pz Ψ₂ z'' θ = deriv (fun z₃ => Ψ₂ z₃ θ) z'' from rfl]
      exact Filter.EventuallyEq.deriv_eq hev2
    rw [show Work.Spaces.pzIter 2 Ψ₁ z' θ = deriv (fun z'' => Work.Spaces.pz Ψ₁ z'' θ) z'
        from rfl,
      show Work.Spaces.pzIter 2 Ψ₂ z' θ = deriv (fun z'' => Work.Spaces.pz Ψ₂ z'' θ) z'
        from rfl]
    exact Filter.EventuallyEq.deriv_eq hev
  -- first `θ`-derivative
  have hevT1 : (fun θ' => Work.Spaces.pth Ψ₁ z θ') =ᶠ[𝓝 θ]
      (fun θ' => Work.Spaces.pth Ψ₂ z θ') := by
    filter_upwards [hVt] with θ' hθ'
    have hmem : ∀ᶠ θ'' in 𝓝 θ', (z, θ'') ∈ V :=
      (hVopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hθ'
    have hev : (fun θ'' => Ψ₁ z θ'') =ᶠ[𝓝 θ'] (fun θ'' => Ψ₂ z θ'') :=
      hmem.mono (fun θ'' hθ'' => hVsub hθ'')
    rw [show Work.Spaces.pth Ψ₁ z θ' = deriv (fun θ'' => Ψ₁ z θ'') θ' from rfl,
      show Work.Spaces.pth Ψ₂ z θ' = deriv (fun θ'' => Ψ₂ z θ'') θ' from rfl]
    exact Filter.EventuallyEq.deriv_eq hev
  -- second `θ`-derivative
  have hevT2 : (fun θ' => Work.Spaces.pthIter 2 Ψ₁ z θ') =ᶠ[𝓝 θ]
      (fun θ' => Work.Spaces.pthIter 2 Ψ₂ z θ') := by
    filter_upwards [hVt] with θ' hθ'
    have hmem : ∀ᶠ θ'' in 𝓝 θ', (z, θ'') ∈ V :=
      (hVopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hθ'
    have hev : (fun θ'' => Work.Spaces.pth Ψ₁ z θ'') =ᶠ[𝓝 θ']
        (fun θ'' => Work.Spaces.pth Ψ₂ z θ'') := by
      filter_upwards [hmem] with θ'' hθ''
      have hmem2 : ∀ᶠ θ₃ in 𝓝 θ'', (z, θ₃) ∈ V :=
        (hVopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hθ''
      have hev2 : (fun θ₃ => Ψ₁ z θ₃) =ᶠ[𝓝 θ''] (fun θ₃ => Ψ₂ z θ₃) :=
        hmem2.mono (fun θ₃ hθ₃ => hVsub hθ₃)
      rw [show Work.Spaces.pth Ψ₁ z θ'' = deriv (fun θ₃ => Ψ₁ z θ₃) θ'' from rfl,
        show Work.Spaces.pth Ψ₂ z θ'' = deriv (fun θ₃ => Ψ₂ z θ₃) θ'' from rfl]
      exact Filter.EventuallyEq.deriv_eq hev2
    rw [show Work.Spaces.pthIter 2 Ψ₁ z θ' = deriv (fun θ'' => Work.Spaces.pth Ψ₁ z θ'') θ'
        from rfl,
      show Work.Spaces.pthIter 2 Ψ₂ z θ' = deriv (fun θ'' => Work.Spaces.pth Ψ₂ z θ'') θ'
        from rfl]
    exact Filter.EventuallyEq.deriv_eq hev
  -- the `∂_θ(tan θ · Ψ)` term
  have hevTtan : (fun θ' => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ₁ z θ) z θ')
      =ᶠ[𝓝 θ] (fun θ' => Work.Spaces.pth (fun z θ => Real.tan θ * Ψ₂ z θ) z θ') := by
    filter_upwards [hVt] with θ' hθ'
    have hmem : ∀ᶠ θ'' in 𝓝 θ', (z, θ'') ∈ V :=
      (hVopen.preimage (continuous_const.prodMk continuous_id)).mem_nhds hθ'
    have hev : (fun θ'' => Real.tan θ'' * Ψ₁ z θ'') =ᶠ[𝓝 θ']
        (fun θ'' => Real.tan θ'' * Ψ₂ z θ'') :=
      hmem.mono (fun θ'' hθ'' => by
        have h1 : Ψ₁ z θ'' = Ψ₂ z θ'' := hVsub hθ''
        show Real.tan θ'' * Ψ₁ z θ'' = Real.tan θ'' * Ψ₂ z θ''
        rw [h1])
    rw [show Work.Spaces.pth (fun z θ => Real.tan θ * Ψ₁ z θ) z θ'
          = deriv (fun θ'' => Real.tan θ'' * Ψ₁ z θ'') θ' from rfl,
      show Work.Spaces.pth (fun z θ => Real.tan θ * Ψ₂ z θ) z θ'
          = deriv (fun θ'' => Real.tan θ'' * Ψ₂ z θ'') θ' from rfl]
    exact Filter.EventuallyEq.deriv_eq hev
  have hpsi : Ψ₁ z θ = Ψ₂ z θ :=
    Filter.EventuallyEq.eq_of_nhds (f := fun q : ℝ × ℝ => Ψ₁ q.1 q.2)
      (g := fun q : ℝ × ℝ => Ψ₂ q.1 q.2) (x := (z, θ)) h
  have hpz1 : Work.Spaces.pz Ψ₁ z θ = Work.Spaces.pz Ψ₂ z θ := hevZ1.eq_of_nhds
  have hpz2 : Work.Spaces.pzIter 2 Ψ₁ z θ = Work.Spaces.pzIter 2 Ψ₂ z θ := hevZ2.eq_of_nhds
  have hpth1 : Work.Spaces.pth Ψ₁ z θ = Work.Spaces.pth Ψ₂ z θ := hevT1.eq_of_nhds
  have hpth2 : Work.Spaces.pthIter 2 Ψ₁ z θ = Work.Spaces.pthIter 2 Ψ₂ z θ := hevT2.eq_of_nhds
  have hpthtan : Work.Spaces.pth (fun z θ => Real.tan θ * Ψ₁ z θ) z θ
      = Work.Spaces.pth (fun z θ => Real.tan θ * Ψ₂ z θ) z θ := hevTtan.eq_of_nhds
  rw [Work.Elliptic.bslOp_apply, Work.Elliptic.bslOp_apply]
  simp only [Work.Elliptic.Lzero, hpth2, hpthtan, hpz2, hpz1, hpsi]

end

end Work.FTS.H2.PhiStarE5
