import Mathlib
import Submission.Work.ELRig.SideFlipChart
import Submission.Work.ELRig.CylLift
import Submission.Work.ELRig.chart_local_structure
import Submission.Work.ELRig.sideFlipChart_open_on_ball
import Submission.Work.ELRig.crossing_of_local_structure

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

open Classical Filter Set
open scoped Topology

/-- **The straightening chart turns the crossing of the horizontal line with the lift into a sign
change of its imaginary part.**  With `p = L.γ₁ s₀` in the far-left half plane, the two branches
of the lift at `s₀` lie on strictly opposite sides of the horizontal line through `p` **iff** the
imaginary part of the chart `sideFlipChart c d fl L s₀` at `p + t` and at `p - t` has opposite
signs for all small `t > 0`. -/
theorem sideFlipChart_crossing {c : ℂ} (d : Work.EL.RootParabolic c)
    (fl : Work.EL.ParabolicFlower (Work.EL.F c) ((LeanEval.ComplexAnalysis.Tantibar c)^[5]) d.z₁)
    (L : Work.ELRig.RayCylLift d fl)
    {s₀ : ℝ} (hre : (L.γ₁ s₀).re < -L.R)
    (hsimple : ∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      L.γ₁ s₀ + t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂ ∧
      L.γ₁ s₀ - t ∉ Set.range L.γ₁ ∪ Set.range L.γ₂) :
    ((∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, (L.γ₁ s).im < (L.γ₁ s₀).im) ∧
        (∀ s ∈ Set.Ioo s₀ (s₀ + ε), (L.γ₁ s₀).im < (L.γ₁ s).im)) ∨
      (∃ ε > 0, (∀ s ∈ Set.Ioo (s₀ - ε) s₀, (L.γ₁ s₀).im < (L.γ₁ s).im) ∧
        (∀ s ∈ Set.Ioo s₀ (s₀ + ε), (L.γ₁ s).im < (L.γ₁ s₀).im))) ↔
    (∃ δ > 0, ∀ t ∈ Set.Ioo (0 : ℝ) δ,
      ((0 < (sideFlipChart c d fl L s₀ (L.γ₁ s₀ + t)).im ∧
          (sideFlipChart c d fl L s₀ (L.γ₁ s₀ - t)).im < 0) ∨
        ((sideFlipChart c d fl L s₀ (L.γ₁ s₀ + t)).im < 0 ∧
          0 < (sideFlipChart c d fl L s₀ (L.γ₁ s₀ - t)).im))) := by
  classical
  obtain ⟨δ, hδpos, hδ⟩ := hsimple
  -- the local structure of the chart around `p = γ₁ s₀`
  obtain ⟨r, hrpos, hrδ, hrR, hΨK, sL, sR, hsL, hsR, hintI, hzL, hzR, hline, hzero⟩ :=
    Work.ELRig.chart_local_structure d fl L hre hδpos hδ
  -- the closed ball lies in the far-left half plane
  have hsub : ∀ w : ℂ, ‖w - L.γ₁ s₀‖ ≤ r → w.re < -L.R := by
    intro w hw
    have h1 : (w - L.γ₁ s₀).re ≤ ‖w - L.γ₁ s₀‖ := Complex.re_le_norm _
    have h2 : (w - L.γ₁ s₀).re = w.re - (L.γ₁ s₀).re := Complex.sub_re w _
    rw [h2] at h1
    linarith
  -- openness of the chart on the ball
  have hopen := Work.ELRig.sideFlipChart_open_on_ball d fl L hre hrpos hsub hΨK
  -- continuity of the chart on the open ball
  have hcont : ContinuousOn (sideFlipChart c d fl L s₀) (Metric.ball (L.γ₁ s₀) r) := by
    have h1 : ContinuousOn (fun w : ℂ => Work.EL.dynPhi c d.φ (fl.Ψ w))
        (Metric.ball (L.γ₁ s₀) r) :=
      (Work.ELRig.continuousOn_dynPhi (c := c) (d := d)).comp
        fl.Ψ_diff.continuous.continuousOn
        (fun w hw => hΨK w (le_of_lt (by
          rw [Metric.mem_ball, dist_eq_norm] at hw
          exact hw)))
    exact h1.div_const _
  -- the lift is injective
  have hγinj : Function.Injective L.γ₁ := by
    intro a b hab
    have h := congrArg (sideFlipChart c d fl L s₀) hab
    rw [sideFlipChart_eq_ofReal, sideFlipChart_eq_ofReal] at h
    have h1 : L.τ a / L.τ s₀ = L.τ b / L.τ s₀ := Complex.ofReal_injective h
    have hne : L.τ s₀ ≠ 0 := ne_of_gt (lt_trans zero_lt_one (L.hτ1 s₀))
    exact L.hτmono.injective (mul_right_cancel₀ hne ((div_eq_div_iff hne hne).mp h1))
  -- the two endpoints of the arc lie on the sphere
  have hsphL : L.γ₁ sL ∈ Metric.sphere (L.γ₁ s₀) r := by
    rw [Metric.mem_sphere, dist_eq_norm, hzL]
  have hsphR : L.γ₁ sR ∈ Metric.sphere (L.γ₁ s₀) r := by
    rw [Metric.mem_sphere, dist_eq_norm, hzR]
  -- the arc lies inside the ball
  have hint : ∀ s ∈ Set.Ioo sL sR, L.γ₁ s ∈ Metric.ball (L.γ₁ s₀) r := by
    intro s hs
    rw [Metric.mem_ball, dist_eq_norm]
    exact hintI s hs
  -- the horizontal line meets the lift only at `p` along the arc
  -- the horizontal rays avoid the lifts
  have hray : ∀ t : ℝ, 0 < t → t ≤ r →
      L.γ₁ s₀ + t ∉ Set.range L.γ₁ ∧ L.γ₁ s₀ - t ∉ Set.range L.γ₁ := by
    intro t ht htr
    have hlt : t < δ := lt_of_le_of_lt htr hrδ
    obtain ⟨h1, h2⟩ := hδ t ⟨ht, hlt⟩
    exact ⟨fun hc => h1 (Or.inl hc), fun hc => h2 (Or.inl hc)⟩
  exact Work.ELRig.crossing_of_local_structure (p := L.γ₁ s₀) (r := r) (A := L.γ₁)
    (sL := sL) (sR := sR) (s₀ := s₀) hrpos hsL hsR L.cont₁.continuousOn hγinj.injOn
    rfl hsphL hsphR hint hline hcont hopen hzero hray

end Work.ELRig
