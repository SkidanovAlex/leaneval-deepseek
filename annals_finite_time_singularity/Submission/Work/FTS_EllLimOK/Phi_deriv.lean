/-
Copyright: work module for the Elgindi finite-time singularity project.

# Differentiation under the angular integral sign for box-regular data

The two `z`-derivatives of the elementary energy functionals

* `Φ δ z = ∫_θ (δ z θ)² dθ`,
* `Ψ δ z = 2 ∫_θ δ z θ · ∂_z δ z θ dθ`

are the integrals of their formal `z`-derivatives.  The data class is
`Work.FTS_EllLimOK.BoxReg δ`: `δ` is jointly `C²` on every closed box
`[a,b] × [0,π/2]` with `0 < a ≤ b` (the finite-order substitute for
closed-quadrant smoothness of the area).

Because the angular interval `[0,π/2]` is compact *and closed*, the parametric
integral lemma `Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt` needs
continuity of the integrand on `V ×ˢ Iθ` up to the two boundary angles `θ = 0`,
`π/2`; `BoxReg` only gives `C²` *within* the box there.  The bridge is
`boxReg_facts` below: for a function which is `C²` within a box, the `z`-slices
are (genuinely) differentiable at every interior radial point, the partial
`∂_z` and its `z`-derivative `∂_z²` are continuous on the (radial interior of
the) box, and the two derivatives are the `fderivWithin` of the box applied to
the direction `(1,0)` — resp. the `fderivWithin` of the first partial itself.
The identification goes through `HasFDerivWithinAt.comp_hasDerivAt` with the
curve `s ↦ (s, θ)`, which stays inside the box near an interior radial point.

Everything here is `sorry`-free.
-/
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.TangentCone.Prod
import Mathlib.Analysis.LocallyConvex.AbsConvexOpen
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Measure.Haar.OfBasis
import Mathlib.Order.CompletePartialOrder
import Submission.Work.FTS_EllLimOK.BoxReg
import Submission.Work.Spaces.Defs
import Submission.Work.Coercivity.contDiffOn_infty_integral_Itheta

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

open scoped Real Topology MeasureTheory
open Set Filter

namespace Work.FTS_EllLimOK

set_option autoImplicit false

/-! ## The box analysis: slices, and continuity of the two `z`-derivatives -/

/-- **`C²` within a box gives the `z`-calculus up to the boundary angles.**

For `F` jointly `C²` on the closed box `[a,b] × [0,π/2]` (`a < b`) and every
radial point `z ∈ (a,b)` interior to the box:

* the `z`-slice `s ↦ F s θ` is differentiable at `z` with derivative the plain
  partial `∂_z F z θ`, for **every** angle `θ ∈ [0,π/2]` (including the two
  boundary angles, where only the one-sided information of `BoxReg` is
  available — the derivative still exists because the curve `s ↦ (s,θ)` stays
  inside the box for `s` near `z`);
* the same for the slice of `∂_z F`, with derivative `∂_z² F z θ`;
* `∂_z F` and `∂_z² F` are jointly continuous on `(a,b) × [0,π/2]`. -/
theorem boxReg_facts {F : ℝ → ℝ → ℝ} {a b : ℝ} (hab : a < b)
    (h : ContDiffOn ℝ 2 (Function.uncurry F) (Set.Icc a b ×ˢ Set.Icc 0 (π / 2))) :
    (∀ z ∈ Set.Ioo a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivAt (fun s => F s θ) (Work.Spaces.pz F z θ) z) ∧
    (∀ z ∈ Set.Ioo a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivAt (fun s => Work.Spaces.pz F s θ) (Work.Spaces.pzIter 2 F z θ) z) ∧
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz F p.1 p.2)
      (Set.Ioo a b ×ˢ Set.Icc 0 (π / 2)) ∧
    ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 F p.1 p.2)
      (Set.Ioo a b ×ˢ Set.Icc 0 (π / 2)) := by
  set S : Set (ℝ × ℝ) := Set.Icc a b ×ˢ Set.Icc 0 (π / 2) with hS
  have hSbox : UniqueDiffOn ℝ S := by
    rw [hS]
    exact (uniqueDiffOn_Icc hab).prod (uniqueDiffOn_Icc (by linarith [Real.pi_pos]))
  -- `G` is the partial `∂_z F`, as read off from the Fréchet derivative within the box
  set G : ℝ × ℝ → ℝ := fun p => (fderivWithin ℝ (Function.uncurry F) S p) (1, 0) with hG
  have hfd : ContDiffOn ℝ 1 (fderivWithin ℝ (Function.uncurry F) S) S :=
    h.fderivWithin hSbox (by norm_num)
  have hGC1 : ContDiffOn ℝ 1 G S := hfd.clm_apply contDiffOn_const
  have hcontG : ContinuousOn G S := hGC1.continuousOn
  have hsub : Set.Ioo a b ×ˢ Set.Icc 0 (π / 2) ⊆ S := by
    intro p hp
    rw [hS]
    exact ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, hp.2⟩
  have hmem_of : ∀ {z θ : ℝ}, z ∈ Set.Ioo a b → θ ∈ Set.Icc 0 (π / 2) →
      ∀ᶠ s in 𝓝 z, (s, θ) ∈ S := by
    intro z θ hz hθ
    exact Filter.eventually_of_mem (isOpen_Ioo.mem_nhds hz) (fun s hs => hsub ⟨hs, hθ⟩)
  -- `∂_z² F` as the derivative of the first partial within the box
  have hcomp : ContinuousOn (fun p : ℝ × ℝ => (fderivWithin ℝ G S p) (1, 0)) S :=
    (hGC1.continuousOn_fderivWithin hSbox le_rfl).clm_apply continuousOn_const
  -- the pointwise identity `∂_z F = G` at every point of the box with interior radial coordinate
  have hpt : ∀ p ∈ Set.Ioo a b ×ˢ Set.Icc 0 (π / 2), Work.Spaces.pz F p.1 p.2 = G p := by
    intro p hp
    have hpS : p ∈ S := hsub hp
    have hd : HasFDerivWithinAt (Function.uncurry F)
        (fderivWithin ℝ (Function.uncurry F) S p) S p :=
      ((h p hpS).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
    have h2 := hd.comp_hasDerivAt p.1
      ((hasDerivAt_id p.1).prodMk (hasDerivAt_const p.1 p.2)) (hmem_of hp.1 hp.2)
    have h3 : HasDerivAt (fun s => F s p.2)
        ((fderivWithin ℝ (Function.uncurry F) S p) (1, 0)) p.1 := by
      simpa [Function.comp_def, Function.uncurry] using h2
    rw [Work.Spaces.pz, hG]
    exact h3.deriv
  have hslice : ∀ z ∈ Set.Ioo a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivAt (fun s => F s θ) (Work.Spaces.pz F z θ) z := by
    intro z hz θ hθ
    rw [hpt (z, θ) ⟨hz, hθ⟩]
    have hzS : (z, θ) ∈ S := hsub ⟨hz, hθ⟩
    have hd : HasFDerivWithinAt (Function.uncurry F)
        (fderivWithin ℝ (Function.uncurry F) S (z, θ)) S (z, θ) :=
      ((h (z, θ) hzS).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
    have h2 := hd.comp_hasDerivAt z
      ((hasDerivAt_id z).prodMk (hasDerivAt_const z θ)) (hmem_of hz hθ)
    simpa [Function.comp_def, Function.uncurry, hG] using h2
  have hslicepz : ∀ z ∈ Set.Ioo a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivAt (fun s => Work.Spaces.pz F s θ) ((fderivWithin ℝ G S (z, θ)) (1, 0)) z := by
    intro z hz θ hθ
    have hzS : (z, θ) ∈ S := hsub ⟨hz, hθ⟩
    have hd : HasFDerivWithinAt G (fderivWithin ℝ G S (z, θ)) S (z, θ) :=
      ((hGC1 (z, θ) hzS).differentiableWithinAt (by norm_num)).hasFDerivWithinAt
    have h2 := hd.comp_hasDerivAt z
      ((hasDerivAt_id z).prodMk (hasDerivAt_const z θ)) (hmem_of hz hθ)
    have heq : (fun s => Work.Spaces.pz F s θ) =ᶠ[𝓝 z] (fun s => G (s, θ)) := by
      filter_upwards [isOpen_Ioo.mem_nhds hz] with s hs
      exact hpt (s, θ) ⟨hs, hθ⟩
    simpa [Function.comp_def] using h2.congr_of_eventuallyEq heq
  have hslicepz' : ∀ z ∈ Set.Ioo a b, ∀ θ ∈ Set.Icc 0 (π / 2),
      HasDerivAt (fun s => Work.Spaces.pz F s θ) (Work.Spaces.pzIter 2 F z θ) z := by
    intro z hz θ hθ
    have hC : (fderivWithin ℝ G S (z, θ)) (1, 0) = Work.Spaces.pzIter 2 F z θ := by
      rw [← (hslicepz z hz θ hθ).deriv]; rfl
    exact hC ▸ hslicepz z hz θ hθ
  refine ⟨hslice, hslicepz', ?_, ?_⟩
  · exact (hcontG.mono hsub).congr (fun p hp => hpt p hp)
  · refine (hcomp.mono hsub).congr (fun p hp => ?_)
    exact (hslicepz p.1 hp.1 p.2 hp.2).deriv

/-! ## The two derivatives of `Φ` and `Ψ` -/

/-- **Differentiation of the energy functionals.**  For `δ` jointly `C²` on the closed box
`[a,b] × [0,π/2]` (`0 < a < b`) and every `z ∈ (a,b)`:

* `s ↦ ∫_θ (δ s θ)²` has derivative `2 ∫_θ δ z θ ∂_z δ z θ` at `z`;
* `s ↦ 2 ∫_θ δ s θ ∂_z δ s θ` has derivative
  `2 ∫_θ ((∂_z δ z θ)² + δ z θ ∂_z² δ z θ)` at `z`. -/
theorem hasDerivAt_PhiPsi_box {δ : ℝ → ℝ → ℝ} {a b z : ℝ} (hab : a < b)
    (hδ : ContDiffOn ℝ 2 (Function.uncurry δ) (Set.Icc a b ×ˢ Set.Icc 0 (π / 2)))
    (hz : z ∈ Set.Ioo a b) :
    HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, (δ s θ) ^ 2)
        (2 * ∫ θ in Work.Spaces.Iθ, δ z θ * Work.Spaces.pz δ z θ) z ∧
      HasDerivAt (fun s => 2 * ∫ θ in Work.Spaces.Iθ, δ s θ * Work.Spaces.pz δ s θ)
        (2 * ∫ θ in Work.Spaces.Iθ,
          (Work.Spaces.pz δ z θ) ^ 2 + δ z θ * Work.Spaces.pzIter 2 δ z θ) z := by
  obtain ⟨hsl, hslpz, hpc, hp2c⟩ := boxReg_facts hab hδ
  have hV : IsOpen (Set.Ioo a b) := isOpen_Ioo
  have hsub : Set.Ioo a b ×ˢ Work.Spaces.Iθ ⊆ Set.Icc a b ×ˢ Set.Icc 0 (π / 2) := by
    intro p hp
    exact ⟨⟨le_of_lt hp.1.1, le_of_lt hp.1.2⟩, hp.2⟩
  have hcδ : ContinuousOn (fun p : ℝ × ℝ => δ p.1 p.2) (Set.Ioo a b ×ˢ Work.Spaces.Iθ) :=
    hδ.continuousOn.mono hsub
  have hcpz : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pz δ p.1 p.2)
      (Set.Ioo a b ×ˢ Work.Spaces.Iθ) := hpc
  have hcp2 : ContinuousOn (fun p : ℝ × ℝ => Work.Spaces.pzIter 2 δ p.1 p.2)
      (Set.Ioo a b ×ˢ Work.Spaces.Iθ) := hp2c
  -- the two `z`-derivative identities
  have hval1 : (∫ θ in Work.Spaces.Iθ, 2 * δ z θ * Work.Spaces.pz δ z θ)
      = 2 * ∫ θ in Work.Spaces.Iθ, δ z θ * Work.Spaces.pz δ z θ := by
    rw [show (fun θ => 2 * δ z θ * Work.Spaces.pz δ z θ)
        = (fun θ => 2 * (δ z θ * Work.Spaces.pz δ z θ)) from by funext θ; ring]
    exact MeasureTheory.integral_const_mul 2 _
  have hfun2 : (fun s => ∫ θ in Work.Spaces.Iθ, 2 * δ s θ * Work.Spaces.pz δ s θ)
      = fun s => 2 * ∫ θ in Work.Spaces.Iθ, δ s θ * Work.Spaces.pz δ s θ := by
    funext s
    rw [show (fun θ => 2 * δ s θ * Work.Spaces.pz δ s θ)
        = (fun θ => 2 * (δ s θ * Work.Spaces.pz δ s θ)) from by funext θ; ring]
    exact MeasureTheory.integral_const_mul 2 _
  have hval2 : (∫ θ in Work.Spaces.Iθ, 2 * (Work.Spaces.pz δ z θ ^ 2
      + δ z θ * Work.Spaces.pzIter 2 δ z θ))
      = 2 * ∫ θ in Work.Spaces.Iθ, (Work.Spaces.pz δ z θ ^ 2
          + δ z θ * Work.Spaces.pzIter 2 δ z θ) := MeasureTheory.integral_const_mul 2 _
  constructor
  · have h1 : ContinuousOn (Function.uncurry (fun s θ => (δ s θ) ^ 2))
        (Set.Ioo a b ×ˢ Work.Spaces.Iθ) := hcδ.pow 2
    have h2 : ContinuousOn (Function.uncurry (fun s θ => 2 * δ s θ * Work.Spaces.pz δ s θ))
        (Set.Ioo a b ×ˢ Work.Spaces.Iθ) :=
      (continuousOn_const.mul hcδ).mul hcpz
    have h3 : ∀ θ ∈ Work.Spaces.Iθ, ∀ s ∈ Set.Ioo a b,
        HasDerivAt (fun s => (δ s θ) ^ 2) (2 * δ s θ * Work.Spaces.pz δ s θ) s := by
      intro θ hθ s hs
      convert (hsl s hs θ hθ).pow 2 using 1
      ring
    have hkey := Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt
      (g := fun s θ => (δ s θ) ^ 2)
      (g' := fun s θ => 2 * δ s θ * Work.Spaces.pz δ s θ)
      (V := Set.Ioo a b) hV hz h1 h2 h3
    rw [hval1] at hkey
    exact hkey
  · have h1 : ContinuousOn (Function.uncurry (fun s θ => 2 * δ s θ * Work.Spaces.pz δ s θ))
        (Set.Ioo a b ×ˢ Work.Spaces.Iθ) :=
      (continuousOn_const.mul hcδ).mul hcpz
    have h2 : ContinuousOn (Function.uncurry (fun s θ => 2 * (Work.Spaces.pz δ s θ ^ 2
        + δ s θ * Work.Spaces.pzIter 2 δ s θ)))
        (Set.Ioo a b ×ˢ Work.Spaces.Iθ) :=
      continuousOn_const.mul ((hcpz.pow 2).add (hcδ.mul hcp2))
    have h3 : ∀ θ ∈ Work.Spaces.Iθ, ∀ s ∈ Set.Ioo a b,
        HasDerivAt (fun s => 2 * δ s θ * Work.Spaces.pz δ s θ)
          (2 * (Work.Spaces.pz δ s θ ^ 2 + δ s θ * Work.Spaces.pzIter 2 δ s θ)) s := by
      intro θ hθ s hs
      have h1' : HasDerivAt (fun s' => δ s' θ) (Work.Spaces.pz δ s θ) s := hsl s hs θ hθ
      have h2' : HasDerivAt (fun s' => Work.Spaces.pz δ s' θ) (Work.Spaces.pzIter 2 δ s θ) s :=
        hslpz s hs θ hθ
      have hmul := (h1'.const_mul 2).mul h2'
      convert hmul using 1
      ring
    have hkey := Work.Coercivity.hasDerivAt_integral_Itheta_of_hasDerivAt
      (g := fun s θ => 2 * δ s θ * Work.Spaces.pz δ s θ)
      (g' := fun s θ => 2 * (Work.Spaces.pz δ s θ ^ 2 + δ s θ * Work.Spaces.pzIter 2 δ s θ))
      (V := Set.Ioo a b) hV hz h1 h2 h3
    rw [hfun2, hval2] at hkey
    exact hkey

/-- The derivative of the energy `Φ δ = ∫_θ δ²` and of the pairing `2 ∫_θ δ ∂_z δ`, for
box-regular data and radial points `z > 0`. -/
theorem Phi_deriv {δ : ℝ → ℝ → ℝ} (hbox : Work.FTS_EllLimOK.BoxReg δ) :
    (∀ z ∈ Set.Ioi (0 : ℝ), HasDerivAt (fun s => ∫ θ in Work.Spaces.Iθ, (δ s θ) ^ 2)
      (2 * ∫ θ in Work.Spaces.Iθ, δ z θ * Work.Spaces.pz δ z θ) z) ∧
    (∀ z ∈ Set.Ioi (0 : ℝ),
      HasDerivAt (fun s => 2 * ∫ θ in Work.Spaces.Iθ, δ s θ * Work.Spaces.pz δ s θ)
      (2 * ∫ θ in Work.Spaces.Iθ,
        (Work.Spaces.pz δ z θ) ^ 2 + δ z θ * Work.Spaces.pzIter 2 δ z θ) z) := by
  constructor
  · intro z hz
    have hzpos : 0 < z := hz
    have hab : z / 2 < 2 * z := by linarith
    have hz' : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
    exact (hasDerivAt_PhiPsi_box hab (hbox (z / 2) (2 * z) (by linarith) (le_of_lt hab)) hz').1
  · intro z hz
    have hzpos : 0 < z := hz
    have hab : z / 2 < 2 * z := by linarith
    have hz' : z ∈ Set.Ioo (z / 2) (2 * z) := ⟨by linarith, by linarith⟩
    exact (hasDerivAt_PhiPsi_box hab (hbox (z / 2) (2 * z) (by linarith) (le_of_lt hab)) hz').2

end Work.FTS_EllLimOK
