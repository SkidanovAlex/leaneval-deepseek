import Mathlib
import Submission.Work.ELRig.SideFlipChart
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.CylSides

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

variable {c : ℂ} {d : Work.EL.RootParabolic c}
variable {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁}
variable {L : Work.ELRig.RayCylLift d fl}
variable {s₀ : ℝ}

/-! ## Two ingredients of the openness of the chart

The straightening chart `w ↦ dynPhi (Ψ w) / rayPoint α₁ (τ s₀)` is the composite of the repelling
coordinate `Ψ` (open on the far-left half plane, being holomorphic and injective there) with the
Böttcher coordinate `dynPhi = e ∘ ⋯` of the dynamical plane (open off the filled Julia set `K c`,
being a homeomorphism onto the exterior of the unit disc).  We isolate the two open-map statements
so that the chart is visibly a composite of open maps.
-/

/-- The dynamical Böttcher coordinate is an open map on the complement of the filled Julia set: off
`K c` it is the homeomorphism `d.hN.e` onto the (open) exterior of the unit disc, followed by the
(open) inclusion of the exterior into `ℂ`. -/
theorem isOpen_image_dynPhi (d : Work.EL.RootParabolic c) {W : Set ℂ}
    (hW : IsOpen W) (hWK : W ⊆ (Work.EL.K c)ᶜ) :
    IsOpen (Work.EL.dynPhi c d.φ '' W) := by
  have hExt : IsOpen Work.Top.exteriorDisc := by
    rw [Work.Top.exteriorDisc]
    exact isOpen_Ioi.preimage continuous_norm
  have hset : Work.EL.dynPhi c d.φ '' W
      = (Subtype.val : ↥Work.Top.exteriorDisc → ℂ) ''
        (d.hN.e '' ((Subtype.val : ↥(Work.EL.K c)ᶜ → ℂ) ⁻¹' W)) := by
    ext y
    constructor
    · rintro ⟨z, hzW, rfl⟩
      have hz : z ∉ Work.EL.K c := hWK hzW
      exact ⟨d.hN.e ⟨z, hz⟩, ⟨⟨z, hz⟩, hzW, rfl⟩, (d.hN.he ⟨z, hz⟩).symm⟩
    · rintro ⟨z', ⟨w', hw', rfl⟩, rfl⟩
      exact ⟨(w' : ℂ), hw', d.hN.he w'⟩
  rw [hset]
  exact hExt.isOpenMap_subtype_val _
    (d.hN.e.isOpenMap _ (hW.preimage continuous_subtype_val))

/-- The repelling coordinate `Ψ` is an open map on the ball `ball (γ₁ s₀) ρ`, whenever that ball
lies in the far-left half plane `{Re < -R}` where `Ψ` is injective: `Ψ` is entire, hence analytic,
and a non-constant analytic function on the (preconnected) ball is open. -/
theorem isOpen_image_psi {ρ : ℝ} (hρ : 0 < ρ)
    (hsub : ∀ w : ℂ, ‖w - L.γ₁ s₀‖ ≤ ρ → w.re < -L.R) :
    ∀ s : Set ℂ, IsOpen s → s ⊆ Metric.ball (L.γ₁ s₀) ρ → IsOpen (fl.Ψ '' s) := by
  intro s hs hsball
  have hinj : Set.InjOn fl.Ψ (Metric.ball (L.γ₁ s₀) ρ) :=
    L.hinj.mono (fun w hw => hsub w (le_of_lt (by simpa [dist_eq_norm] using Metric.mem_ball.mp hw)))
  have han : AnalyticOnNhd ℂ fl.Ψ (Metric.ball (L.γ₁ s₀) ρ) :=
    fl.Ψ_diff.differentiableOn.analyticOnNhd Metric.isOpen_ball
  by_cases hconst : ∃ w, ∀ z ∈ Metric.ball (L.γ₁ s₀) ρ, fl.Ψ z = w
  · exfalso
    obtain ⟨w₀, hw₀⟩ := hconst
    have hmem1 : L.γ₁ s₀ ∈ Metric.ball (L.γ₁ s₀) ρ := Metric.mem_ball_self hρ
    have hmem2 : L.γ₁ s₀ + ((ρ / 2 : ℝ) : ℂ) ∈ Metric.ball (L.γ₁ s₀) ρ := by
      rw [Metric.mem_ball, dist_eq_norm, add_sub_cancel_left]
      rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith : (0 : ℝ) < ρ / 2)]
      linarith
    have heq : L.γ₁ s₀ = L.γ₁ s₀ + ((ρ / 2 : ℝ) : ℂ) :=
      hinj hmem1 hmem2 (by rw [hw₀ _ hmem1, hw₀ _ hmem2])
    have h' : ((ρ / 2 : ℝ) : ℂ) = 0 := by
      have h2 := congrArg (fun z : ℂ => z - L.γ₁ s₀) heq
      simpa using h2.symm
    have h'' : (ρ / 2 : ℝ) = 0 := Complex.ofReal_eq_zero.mp h'
    linarith
  · exact (han.is_constant_or_isOpen Metric.isPreconnected_ball).resolve_left hconst s hsball hs

/-- The straightening chart of the lift is an open map on any ball around the base point that lies
in the far-left half plane and whose `Ψ`-image misses the filled Julia set. -/
theorem sideFlipChart_open_on_ball {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {s₀ : ℝ} {ρ : ℝ}
    (hre : (L.γ₁ s₀).re < -L.R) (hρ : 0 < ρ)
    (hsub : ∀ w : ℂ, ‖w - L.γ₁ s₀‖ ≤ ρ → w.re < -L.R)
    (hΨK : ∀ w : ℂ, ‖w - L.γ₁ s₀‖ ≤ ρ → fl.Ψ w ∉ Work.EL.K c) :
    ∀ s : Set ℂ, IsOpen s → s ⊆ Metric.ball (L.γ₁ s₀) ρ →
      IsOpen ((Work.ELRig.sideFlipChart c d fl L s₀) '' s) := by
  intro s hs hsball
  -- `Ψ` maps the open `s` to the open set `Ψ '' s`, which avoids the filled Julia set
  have hpsi : IsOpen (fl.Ψ '' s) :=
    isOpen_image_psi (L := L) (fl := fl) hρ hsub s hs hsball
  have hpsiK : fl.Ψ '' s ⊆ (Work.EL.K c)ᶜ := by
    rintro y ⟨w, hw, rfl⟩
    exact hΨK w (le_of_lt (by simpa [dist_eq_norm] using Metric.mem_ball.mp (hsball hw)))
  -- hence its Böttcher image is open
  have hdyn : IsOpen (Work.EL.dynPhi c d.φ '' (fl.Ψ '' s)) :=
    isOpen_image_dynPhi d hpsi hpsiK
  -- the chart is the Böttcher image, rescaled by the (nonzero) normalisation constant
  have hq : Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀) ≠ 0 :=
    rayPoint_alpha1_ne_zero (c := c) (d := d) (fl := fl) (L := L) (s₀ := s₀)
  have hset : (sideFlipChart c d fl L s₀) '' s
      = (fun u : ℂ => u * (Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀))⁻¹) ''
          (Work.EL.dynPhi c d.φ '' (fl.Ψ '' s)) := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      exact ⟨Work.EL.dynPhi c d.φ (fl.Ψ w), ⟨fl.Ψ w, ⟨w, hw, rfl⟩, rfl⟩,
        by rw [sideFlipChart_apply, div_eq_mul_inv]⟩
    · rintro ⟨u, ⟨z, ⟨w, hw, rfl⟩, rfl⟩, rfl⟩
      exact ⟨w, hw, by rw [sideFlipChart_apply, div_eq_mul_inv]⟩
  rw [hset]
  exact (Homeomorph.mulRight₀ _ (inv_ne_zero hq)).isOpenMap _ hdyn

end Work.ELRig
