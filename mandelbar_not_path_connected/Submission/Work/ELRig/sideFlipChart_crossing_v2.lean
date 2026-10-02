import Mathlib
import Submission.Work.Topology.crosscut_axis_separation_v2
import Submission.Work.ELRig.chart_local_structure
import Submission.Work.ELRig.crossing_of_local_structure
import Submission.Work.ELRig.sideFlipChart_isOpenMap

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
theorem sideFlipChart_crossing_v2 {c : ℂ} (d : Work.EL.RootParabolic c)
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
  obtain ⟨δ, hδ, hsimple'⟩ := hsimple
  -- the local structure of the chart at `p`: radius, two exit parameters, zero set of `Im`
  obtain ⟨r, hr, hrδ, _hrR, hΨK, sL, sR, hsL, hsR, hIoo, hsphL, hsphR, hline, hzero⟩ :=
    chart_local_structure (c := c) d fl L hre hδ hsimple'
  refine crossing_of_local_structure (p := L.γ₁ s₀) (r := r) (A := L.γ₁)
    (sL := sL) (sR := sR) (s₀ := s₀) (h := sideFlipChart c d fl L s₀)
    hr hsL hsR L.cont₁.continuousOn (rayCylLift_injective L).injOn rfl
    (by rw [Metric.mem_sphere, dist_eq_norm]; exact hsphL)
    (by rw [Metric.mem_sphere, dist_eq_norm]; exact hsphR)
    (fun s hs => by rw [Metric.mem_ball, dist_eq_norm]; exact hIoo s hs)
    hline ?_ ?_ hzero ?_
  · -- the chart is continuous on the ball: `dynPhi` is continuous off `K c` and `Ψ` avoids `K c`
    have hdyn : ContinuousOn (Work.EL.dynPhi c d.φ) (Work.EL.K c)ᶜ := continuousOn_dynPhi
    have hcomp : ContinuousOn (fun w : ℂ => Work.EL.dynPhi c d.φ (fl.Ψ w))
        (Metric.ball (L.γ₁ s₀) r) :=
      ContinuousOn.comp hdyn fl.Ψ_diff.continuous.continuousOn
        (fun w hw => hΨK w (le_of_lt (by rwa [Metric.mem_ball, dist_eq_norm] at hw)))
    exact hcomp.div_const _
  · -- the chart is open on the ball
    exact sideFlipChart_isOpenMap (c := c) d fl L s₀ hr rfl
      (fun w hw => hΨK w (le_of_lt (by rwa [Metric.mem_ball, dist_eq_norm] at hw)))
  · -- the punctured horizontal line misses the lift, by `hsimple`
    intro t ht htr
    have htδ : t ∈ Set.Ioo (0 : ℝ) δ := ⟨ht, lt_of_le_of_lt htr hrδ⟩
    obtain ⟨ha, hb⟩ := hsimple' t htδ
    exact ⟨fun h => ha (Or.inl h), fun h => hb (Or.inl h)⟩

end Work.ELRig
