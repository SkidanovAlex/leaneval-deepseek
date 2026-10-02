import Mathlib
import Submission.Work.ELRig.crosscut_separation_ball
import Submission.Work.ELRig.crossing_arc_separation

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.ELRig

/-- A crosscut of the disc `ball 1 ρ` through `1` that crosses the real axis at `1` separates the
two points `1 ± δ` of the real axis.  Route: `ψ z = 1 - i (z - 1)` maps the disc onto itself, fixes
`1`, sends the real axis to the imaginary axis and satisfies `(ψ (v t)).re - 1 = (v t).im`; apply
`crosscut_separation_ball` to `u ↦ ψ (v (a + u (b-a)))` on `Set.Icc 0 1` and transport the
conclusion back along `ψ ⁻¹ w = 1 + i (w - 1)` (using `JoinedIn.map`, `Set.image_diff` and
`ψ '' Metric.ball 1 ρ = Metric.ball 1 ρ`). -/
theorem not_joined_of_arc_crossing {v : ℝ → ℂ} {ρ a b : ℝ} (hρ : 0 < ρ)
    (ha : a < 0) (hb : 0 < b)
    (hvc : ContinuousOn v (Set.Icc a b)) (hvi : Set.InjOn v (Set.Icc a b)) (hv0 : v 0 = 1)
    (hvspha : v a ∈ Metric.sphere (1:ℂ) ρ) (hvsphb : v b ∈ Metric.sphere (1:ℂ) ρ)
    (hvball : ∀ t ∈ Set.Ioo a b, v t ∈ Metric.ball (1:ℂ) ρ)
    (him : ∀ t ∈ Set.Icc a b, t ≠ 0 → (v t).im ≠ 0)
    (hcross : ((∀ t ∈ Set.Ioo a 0, (v t).im < 0) ∧ (∀ t ∈ Set.Ioo 0 b, 0 < (v t).im)) ∨
              ((∀ t ∈ Set.Ioo a 0, 0 < (v t).im) ∧ (∀ t ∈ Set.Ioo 0 b, (v t).im < 0))) :
    ∀ δ : ℝ, 0 < δ → δ < ρ →
      ¬ JoinedIn (Metric.ball (1:ℂ) ρ \ v '' Set.Icc a b) (1 + (δ:ℂ)) (1 - (δ:ℂ)) := by
  -- The arc meets the horizontal line `{im = 1.im}` in the disc only at its midpoint `v 0 = 1`:
  -- off the parameter `0` this is `him`, and at `0` it is `hv0`.
  have hline : ∀ s ∈ Set.Icc a b, v s ≠ 1 → (v s).im ≠ (1:ℂ).im := by
    intro s hs hne
    rw [Complex.one_im]
    by_cases hs0 : s = 0
    · exact absurd (by rw [hs0, hv0]) hne
    · exact him s hs hs0
  -- The crossing hypothesis, read against the centre `p = 1`.
  have hcr : ((∀ s ∈ Set.Ioo a 0, (v s).im < (1:ℂ).im) ∧
        (∀ s ∈ Set.Ioo 0 b, (1:ℂ).im < (v s).im)) ∨
        ((∀ s ∈ Set.Ioo a 0, (1:ℂ).im < (v s).im) ∧
          (∀ s ∈ Set.Ioo 0 b, (v s).im < (1:ℂ).im)) := by
    rw [Complex.one_im]
    exact hcross
  intro δ hδ0 hδρ
  exact crossing_arc_separation (p := 1) (r := ρ) (A := v) (sL := a) (sR := b) (s₀ := 0)
    hρ ha hb hvc hvi hv0 hvspha hvsphb hvball hline hcr δ hδ0 hδρ

end Work.ELRig
