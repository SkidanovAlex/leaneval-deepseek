import Mathlib
import Submission.Work.ELRig.SideFlipChart
import Submission.Work.ELRig.CylSides
import Submission.Work.ELRig.sideFlipChart_open_on_ball

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set
open scoped Topology

variable {c : ℂ}

/-! ## The straightening chart of a lift is an open map

`sideFlipChart c d fl L s₀ = (dynPhi c d.φ ∘ fl.Ψ) / rayPoint α₁ (L.τ s₀)` is the composite of
the entire repelling coordinate `fl.Ψ`, which is holomorphic and non-constant, hence open, with
the Böttcher coordinate `dynPhi c d.φ`, which is a homeomorphism onto the exterior of the unit
disc off the filled Julia set and hence open.  Neither ingredient needs the far-left half plane
in which `Ψ` is injective: a non-constant holomorphic function is already open. -/

/-- **`Ψ` is not constant on any ball around a point of the lift.**  If it were constant on the
ball `ball (γ₁ s₀) ε`, it would be constant on all of `ℂ` (identity principle, `Ψ` is entire), and
then the two points `γ₁ s₀` and `γ₁ (s₀ + 1)` -- both sent to the point of the ray `R(α₁)` of
level `τ` -- would carry the same level, contradicting the strict monotonicity of `τ`. -/
theorem psi_not_constant_on_ball {d : Work.EL.RootParabolic c}
    {fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁}
    (L : RayCylLift d fl) {s₀ : ℝ} {ε : ℝ} (hε : 0 < ε) :
    ¬ ∃ a, ∀ w ∈ Metric.ball (L.γ₁ s₀) ε, fl.Ψ w = a := by
  rintro ⟨a, ha⟩
  -- `Ψ` is entire, so constant on a ball forces it constant everywhere
  have han : AnalyticOnNhd ℂ fl.Ψ Set.univ :=
    fl.Ψ_diff.differentiableOn.analyticOnNhd isOpen_univ
  have hev : fl.Ψ =ᶠ[𝓝 (L.γ₁ s₀)] (fun _ : ℂ => a) :=
    Filter.eventually_of_mem (Metric.ball_mem_nhds (L.γ₁ s₀) hε) ha
  have hEq : Set.EqOn fl.Ψ (fun _ : ℂ => a) Set.univ :=
    han.eqOn_of_preconnected_of_eventuallyEq analyticOnNhd_const isPreconnected_univ
      (Set.mem_univ _) hev
  have hs₀ : fl.Ψ (L.γ₁ s₀) = a := hEq (Set.mem_univ _)
  have hs₁ : fl.Ψ (L.γ₁ (s₀ + 1)) = a := hEq (Set.mem_univ _)
  -- `L.hΨ₁` read with the unfolded ray point, so that `rw` can match it below
  have hΨ₁ : ∀ s : ℝ, fl.Ψ (L.γ₁ s) = Work.Top.NakaneData.rayPt d.hN Work.EL.alpha1 (L.τ s) :=
    fun s => L.hΨ₁ s
  -- the levels of the two points therefore coincide
  have hlev : Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ s₀)
      = Work.Top.NakaneData.rayPoint Work.EL.alpha1 (L.τ (s₀ + 1)) := by
    rw [← Work.Top.NakaneData.Phi_rayPt d.hN (L.hτ1 s₀),
      ← Work.Top.NakaneData.Phi_rayPt d.hN (L.hτ1 (s₀ + 1)),
      ← hΨ₁ s₀, ← hΨ₁ (s₀ + 1), hs₀, hs₁]
  have hτ : L.τ s₀ = L.τ (s₀ + 1) := by
    have h := congrArg norm hlev
    rw [Work.Top.NakaneData.norm_rayPoint, Work.Top.NakaneData.norm_rayPoint,
      abs_of_pos (by linarith [L.hτ1 s₀]), abs_of_pos (by linarith [L.hτ1 (s₀ + 1)])] at h
    exact h
  exact (ne_of_lt (L.hτmono (lt_add_one s₀))) hτ

theorem sideFlipChart_isOpenMap {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) (s₀ : ℝ) {p : ℂ} {ε : ℝ} (hε : 0 < ε)
    (hp : p = L.γ₁ s₀)
    (hK : ∀ w ∈ Metric.ball p ε, fl.Ψ w ∉ Work.EL.K c) :
    ∀ s : Set ℂ, IsOpen s → s ⊆ Metric.ball p ε → IsOpen (Work.ELRig.sideFlipChart c d fl L s₀ '' s) := by
  subst hp
  intro s hs hsball
  -- `Ψ` is open on the ball, being a non-constant holomorphic function there
  have hnonconst : ¬ ∃ a, ∀ w ∈ Metric.ball (L.γ₁ s₀) ε, fl.Ψ w = a :=
    psi_not_constant_on_ball (c := c) L hε
  have han : AnalyticOnNhd ℂ fl.Ψ (Metric.ball (L.γ₁ s₀) ε) :=
    fl.Ψ_diff.differentiableOn.analyticOnNhd Metric.isOpen_ball
  have hpsi : IsOpen (fl.Ψ '' s) := by
    rcases han.is_constant_or_isOpen Metric.isPreconnected_ball with h | h
    · exact absurd h hnonconst
    · exact h s hsball hs
  -- and its image misses the filled Julia set
  have hpsiK : fl.Ψ '' s ⊆ (Work.EL.K c)ᶜ := by
    rintro y ⟨w, hw, rfl⟩
    exact hK w (hsball hw)
  have hdyn : IsOpen (Work.EL.dynPhi c d.φ '' (fl.Ψ '' s)) :=
    isOpen_image_dynPhi d hpsi hpsiK
  -- the chart is that Böttcher image, rescaled by the non-zero normalisation constant
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
