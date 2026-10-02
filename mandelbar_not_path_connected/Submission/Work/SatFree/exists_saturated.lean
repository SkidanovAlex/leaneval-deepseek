/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: SatFree team
-/
import Mathlib
import Submission.Work.SatFree.Defs
import Submission.Work.SatFree.parabolicFlowerFix_wideSat
import Submission.Work.SatFree.flowerFix_of_wideSat

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# AREA `SatFree` — the deliverable: a saturating `c₀`-flower, with no numeric hypothesis

`Work.SatFree.exists_saturated` is the `hSat` input of `Work.GATE2.twoSided_of_saturating` /
`Work.GATE2.saturatedFlower_of_numeric`, with the numeric hypothesis
`Ha1 : Re ((2/3) · F''' / F''²) < 1` (equivalently `a.re < 1` for the Abel parameter `a` of the
germ at `d.z₁`) **removed**.  Only `Work.GATE2`'s `SaturatedFlower` is quoted, so the statement is
the one the wire note §B.2 asks for:

```lean
theorem Work.SatFree.exists_saturated {c₀} (d : Work.EL.RootParabolic c₀) :
    ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁,
    ∃ FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa,
      Work.GATE2.SaturatedFlower fl.toParabolicFlower FF
```

`Work.SatFree.exists_saturated_wide` additionally exposes *which* flower is produced: its petal
contains a **wide chart sector** `{z₁ - lam / W | W ≠ 0, Ms < sgauge W}` (a sector of opening
`3π/2` in the chart `z ↦ -1/((z - z₁)/lam)`, i.e. `SatFree.chartSector d.z₁ lam Ms`), which is what
PARIMPL2 needs for the restricted `hLB` of wire note §A.4 R1.  `exists_saturated_chartSector` is
the same statement in the `z`-form of `SatFree.chartSector`.

The design (see `Submission/Work/SatFree/NOTES.md`): for `κ₀ = 1 - a` of either sign the chart
Fatou coordinate `w - (1-a) log w` saturates a right half-plane only up to the log-slack
threshold of `SatFree.fatouCoordW_saturates_log`; feeding `τ + m` for `m = O(log ‖τ‖)` into it and
pulling back `m` steps inside the wide petal (`SatFree.backward_orbit`,
`SatFree.germ_flowerFix_wideSat`) produces a point of the petal with `φa`-value exactly `τ`; the
`FlowerFix` half-petal `Pg = {z ∈ Pa | g z ∈ Pa ∧ X < Re φa z}` is then invariant for free
(`SatFree.flowerFix_of_wideSat`).
-/

open scoped Topology
open Set Filter Metric Function

namespace Work.SatFree

noncomputable section

open LeanEval.ComplexAnalysis (Tantibar)

/-- **The wide, saturating `c₀`-flower, with the wide chart sector exposed.**  The flower whose
`Work.GATE2.SaturatedFlower` certificate is `exists_saturated`, together with the affine data of
the germ normalization: `fl.Pa` contains `{d.z₁ - lam / W | W ≠ 0, Ms < sgauge W}`, the wide chart
sector of level `Ms` in the chart `z ↦ -1/((z - d.z₁)/lam) = lam * (-1/(z - d.z₁))`. -/
theorem exists_saturated_wide {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) :
    ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁,
      ∃ FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa,
        Work.GATE2.SaturatedFlower fl.toParabolicFlower FF ∧
        ∃ (Ms : ℝ) (lam : ℂ), lam ≠ 0 ∧ ∀ W : ℂ, W ≠ 0 →
          Ms < Work.FatouCoord.Flower.sgauge W → d.z₁ - lam / W ∈ fl.Pa := by
  obtain ⟨fl, -, hwide, hsat⟩ :=
    parabolicFlowerFix_wideSat (Work.Final.differentiable_F c₀)
      (fun z => (Work.Final.differentiable_star_Tantibar_five c₀).differentiableAt)
      (Work.Final.Tantibar_five_comp_self c₀) (Work.Final.Tantibar_five_fix d.per_half)
      d.mult d.simple d.per_half one_pos
  obtain ⟨FF, hFF⟩ := saturatedFlower_of_satHalfPlane' d fl hsat
  exact ⟨fl, FF, hFF, hwide⟩

/-- **THE DELIVERABLE** (wire note §B.2, step S5): the saturating `c₀`-flower, sign-free.

For every root-parabolic parameter `d : Work.EL.RootParabolic c₀` there is a repaired flower `fl`
of `(Ft c₀, gtc c₀)` at `d.z₁` and a `Work.PARIMPL.FlowerFix` `FF` on it whose Fatou coordinate
maps the invariant half-petal `FF.Pg` onto a right half-plane — `Work.GATE2.SaturatedFlower`.

No hypothesis on `Re ((2/3) · F'''/F''²)`, i.e. `κ₀ = 1 - a` may be negative (gaps3 §1). -/
theorem exists_saturated {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) :
    ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁,
      ∃ FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa,
        Work.GATE2.SaturatedFlower fl.toParabolicFlower FF := by
  obtain ⟨fl, FF, hFF, -⟩ := exists_saturated_wide d
  exact ⟨fl, FF, hFF⟩

/-- **The deliverable with the petal inside a prescribed ball.**  The same chart as
`exists_saturated`, with the flower's `Pa` contained in `Metric.ball d.z₁ δ` (`δ > 0` arbitrary).
This is the form to use when a downstream consumer needs the petal to avoid a fixed neighbourhood
of the parabolic point. -/
theorem exists_saturated_at {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) {δ : ℝ} (hδ : 0 < δ) :
    ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁,
      fl.Pa ⊆ Metric.ball d.z₁ δ ∧
      ∃ FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa,
        Work.GATE2.SaturatedFlower fl.toParabolicFlower FF := by
  obtain ⟨fl, hball, -, hsat⟩ :=
    parabolicFlowerFix_wideSat (Work.Final.differentiable_F c₀)
      (fun z => (Work.Final.differentiable_star_Tantibar_five c₀).differentiableAt)
      (Work.Final.Tantibar_five_comp_self c₀) (Work.Final.Tantibar_five_fix d.per_half)
      d.mult d.simple d.per_half hδ
  exact ⟨fl, hball, saturatedFlower_of_satHalfPlane' d fl hsat⟩

/-- **The deliverable with the wide chart sector in the `z`-form.**  Same flower as
`exists_saturated_wide`, with the containment read through `SatFree.chartSector`: the flower's
petal contains the wide sector of level `Ms` in the chart `z ↦ lam * (-1/(z - d.z₁))`. -/
theorem exists_saturated_chartSector {c₀ : ℂ} (d : Work.EL.RootParabolic c₀) :
    ∃ fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁,
      ∃ FF : Work.PARIMPL.FlowerFix d (Work.EL.F c₀) ((Tantibar c₀)^[5]) d.z₁ fl.Pa fl.φa,
        Work.GATE2.SaturatedFlower fl.toParabolicFlower FF ∧
        ∃ (Ms : ℝ) (lam : ℂ), lam ≠ 0 ∧ chartSector d.z₁ lam Ms ⊆ fl.Pa := by
  obtain ⟨fl, FF, hFF, Ms, lam, hlam, hwide⟩ := exists_saturated_wide d
  refine ⟨fl, FF, hFF, Ms, lam, hlam, ?_⟩
  rw [chartSector_eq_image hlam Ms]
  rintro z ⟨W, ⟨hW, hMs⟩, rfl⟩
  exact hwide W hW hMs

end

end Work.SatFree
