import Mathlib
import Submission.Work.ELRig.chart_local_structure

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set
open scoped Topology

/-- **Small circle, two crossings.**  For the straightening chart of the lift `γ₁` at the far-left
point `p = γ₁ s₀` and for any `δ > 0` satisfying the "horizontal line meets the lifts only at `p`"
condition, there is a radius `r < δ` (also so small that the closed ball of radius `r` around `p`
lies in the half plane `{Re < -L.R}` and its `Ψ`-image misses `K c`) such that the circle of radius
`r` around `p` meets the zero set of the chart's imaginary part exactly in the two "first exit"
points `γ₁ sL`, `γ₁ sR` of the lift from that circle. -/
theorem chart_sphere_crossings_small {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl) {s₀ : ℝ} (hre : (L.γ₁ s₀).re < -L.R) {δ : ℝ} (hδ : 0 < δ)
    (hsimple : ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      L.γ₁ s₀ + t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
      L.γ₁ s₀ - t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) :
    ∃ r > 0, r < δ ∧ r < -((L.γ₁ s₀).re) - L.R ∧
      (∀ w : ℂ, ‖w - L.γ₁ s₀‖ ≤ r → fl.Ψ w ∉ Work.EL.K c) ∧
      ∃ sL sR : ℝ, sL < s₀ ∧ s₀ < sR ∧
        (∀ s ∈ Set.Ioo sL sR, ‖L.γ₁ s - L.γ₁ s₀‖ < r) ∧
        ‖L.γ₁ sL - L.γ₁ s₀‖ = r ∧ ‖L.γ₁ sR - L.γ₁ s₀‖ = r ∧
        (∀ w : ℂ, ‖w - L.γ₁ s₀‖ = r →
          ((Work.ELRig.sideFlipChart c d fl L s₀ w).im = 0 ↔ w = L.γ₁ sL ∨ w = L.γ₁ sR)) := by
  -- The local structure theorem gives the radius, the two first-exit parameters and the
  -- identification of the zero set of the chart with the piece of the lift inside the ball.
  obtain ⟨r, hrpos, hrδ, hrR, hball, sL, sR, hsL, hsR, hinside, hdL, hdR, _him, hzero⟩ :=
    chart_local_structure d fl L hre hδ hsimple
  refine ⟨r, hrpos, hrδ, hrR, hball, sL, sR, hsL, hsR, hinside, hdL, hdR, ?_⟩
  intro w hw
  constructor
  · -- a zero of the chart on the sphere is the image of a parameter in `[sL, sR]`; that
    -- parameter has to be one of the two endpoints
    intro him
    obtain ⟨s, hsIcc, hs_eq⟩ := (hzero w (le_of_eq hw)).mp him
    have hdist : ‖L.γ₁ s - L.γ₁ s₀‖ = r := by rw [hs_eq, hw]
    by_cases h1 : s = sL
    · exact Or.inl (by rw [← hs_eq, h1])
    by_cases h2 : s = sR
    · exact Or.inr (by rw [← hs_eq, h2])
    · exfalso
      have hmem : s ∈ Set.Ioo sL sR :=
        ⟨lt_of_le_of_ne hsIcc.1 (Ne.symm h1), lt_of_le_of_ne hsIcc.2 h2⟩
      have := hinside s hmem
      rw [hdist] at this
      exact lt_irrefl r this
  · -- the two exit points are zeros of the chart
    rintro (h | h)
    · rw [h, sideFlipChart_eq_ofReal]
      exact Complex.ofReal_im _
    · rw [h, sideFlipChart_eq_ofReal]
      exact Complex.ofReal_im _

end Work.ELRig
