/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FatouCoord team
-/
import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Flower.GermDefs
import Submission.Work.FatouCoord.Repelling.near_translation_mod

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# Growth of the wide sector under the chart dynamics

Past a large level `M`, the wide sector `{M < sgauge W}` is mapped into itself by the chart
dynamics `wMap f`, and the real part grows by at least `1/2` per step.
-/

open scoped Topology
open Set Filter Metric Function

namespace Work.FatouCoord.Flower

open Work.FatouCoord

noncomputable section

theorem sgauge_le_two_norm (W : ℂ) : sgauge W ≤ 2 * ‖W‖ := by
  rw [sgauge]
  have h1 := Complex.abs_re_le_norm W
  have h2 := Complex.abs_im_le_norm W
  have h3 : W.re ≤ |W.re| := le_abs_self _
  linarith

theorem widePetal_growth {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') :
    ∃ M : ℝ, 1 ≤ M ∧ 1 / r < M ∧
      ∀ W : ℂ, M < sgauge W →
        M < sgauge (wMap f W) ∧ (wMap f W).re ≥ W.re + 1 / 2 := by
  have hKnn : 0 ≤ Estimate.Ksub A a := Estimate.Ksub_nonneg hb.hA a
  set K := Estimate.Ksub A a with hKdef
  set L : ℝ := max (1 / r) (max 4 (4 * K)) with hLdef
  refine ⟨2 * max 1 L + 1, by linarith [le_max_left (1 : ℝ) L], ?_, ?_⟩
  · have hr1 : 1 / r ≤ L := le_max_left _ _
    have hLmax : L ≤ max 1 L := le_max_right _ _
    have hmax1 : (1 : ℝ) ≤ max 1 L := le_max_left _ _
    linarith
  · intro W hW
    have hL4 : (4 : ℝ) ≤ L := le_trans (le_max_left (4 : ℝ) (4 * K)) (le_max_right _ _)
    have hL4K : 4 * K ≤ L := le_trans (le_max_right (4 : ℝ) (4 * K)) (le_max_right _ _)
    have hrle : 1 / r ≤ L := le_max_left _ _
    have hbig : L < ‖W‖ := by
      have h1 : sgauge W / 2 ≤ ‖W‖ := by linarith [sgauge_le_two_norm W]
      have h2 : max 1 L + 1 / 2 < sgauge W / 2 := by linarith
      have hmax1 : (1 : ℝ) ≤ max 1 L := le_max_left _ _
      have hLmax : L ≤ max 1 L := le_max_right _ _
      linarith
    have hx : 1 / r < ‖W‖ := lt_of_le_of_lt hrle hbig
    have hx4 : 4 ≤ ‖W‖ := le_of_lt (lt_of_le_of_lt hL4 hbig)
    have hΔ := Repelling.near_translation_mod hb hx hx4
    have hWpos : (0 : ℝ) < ‖W‖ := by linarith
    have hKle : K / ‖W‖ < 1 / 4 := by
      rw [div_lt_iff₀ hWpos]
      linarith
    have hre : (wMap f W).re ≥ W.re + 1 / 2 := by
      have h1 : |(wMap f W - W - 1).re| ≤ ‖wMap f W - W - 1‖ := Complex.abs_re_le_norm _
      have h2 : |(wMap f W - W - 1).re| ≤ 1 / 4 := le_trans h1 (le_trans hΔ hKle.le)
      have h3 : -(1 / 4) ≤ (wMap f W - W - 1).re := (abs_le.mp h2).1
      simp only [Complex.sub_re, Complex.one_re] at h3
      linarith
    refine ⟨?_, hre⟩
    have him : |(wMap f W).im - W.im| ≤ 1 / 4 := by
      have h1 : |(wMap f W - W - 1).im| ≤ ‖wMap f W - W - 1‖ := Complex.abs_im_le_norm _
      have h2 : |(wMap f W - W - 1).im| ≤ 1 / 4 := le_trans h1 (le_trans hΔ hKle.le)
      simpa using h2
    have h5 : |W.im| - 1 / 4 ≤ |(wMap f W).im| := by
      have h6 : |W.im| - |(wMap f W).im| ≤ |W.im - (wMap f W).im| :=
        abs_sub_abs_le_abs_sub _ _
      rw [abs_sub_comm] at h6
      linarith
    have h7 : sgauge W + 1 / 4 ≤ sgauge (wMap f W) := by
      rw [sgauge, sgauge]
      linarith
    linarith

end

end Work.FatouCoord.Flower
