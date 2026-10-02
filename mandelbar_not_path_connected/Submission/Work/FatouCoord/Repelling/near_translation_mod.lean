import Mathlib
import Submission.Work.FatouCoord.Setup
import Submission.Work.FatouCoord.Estimate.wMap_iterate_deriv_bound

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


namespace Work.FatouCoord.Repelling

open Work.FatouCoord
open scoped Topology
open Set Filter Metric Function

set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
set_option linter.unreachableTactic false
set_option linter.unusedTactic false

noncomputable section

variable {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ} {x w : ℂ}

/-! ## `wMap` in closed form without a half-plane hypothesis

The lemmas `wMap_eq` and `wMap_sub_eq` in `Setup` assume `0 < w.re`; the only place that
hypothesis is used is to conclude `w ≠ 0`.  Since `1 / r < ‖w‖` with `r > 0` already forces
`w ≠ 0`, we restate them with that single, weaker hypothesis. -/

/-- The chart-conjugate dynamics written in terms of the germ: if `f z = z + z ^ 2 * h z`
then `wMap f w = w / (1 + (-1/w) * h (-1/w))`.  Only `w ≠ 0` (and `1/r < ‖w‖`) is needed. -/
theorem wMap_eq_ne {f h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ∀ z ∈ ball 0 r, f z = z + z ^ 2 * h z) {w : ℂ} (hw0 : w ≠ 0)
    (hN : 1 / r < ‖w‖) : wMap f w = w / (1 + (-1 / w) * h (-1 / w)) := by
  have hz : -1 / w ∈ ball 0 r := by
    simpa [mem_ball_zero_iff] using norm_neg_one_div_lt hr hw0 hN
  have hzw : -1 / (-1 / w) = w := by field_simp
  have h1 : f (-1 / w) = (-1 / w) * (1 + (-1 / w) * h (-1 / w)) := by
    rw [hf (-1 / w) hz]; ring
  simp only [wMap, chart]
  rw [h1, div_mul_eq_div_div, hzw]

/-- The "defect" `wMap f w - w` of the pull-back from being a translation, with `w ≠ 0`
in place of `0 < w.re`. -/
theorem wMap_sub_eq_ne {f h : ℂ → ℂ} {r : ℝ} (hr : 0 < r)
    (hf : ∀ z ∈ ball 0 r, f z = z + z ^ 2 * h z) {w : ℂ} (hw0 : w ≠ 0)
    (hN : 1 / r < ‖w‖) (hne : 1 + (-1 / w) * h (-1 / w) ≠ 0) :
    wMap f w - w = h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) := by
  have key : w * ((-1 / w) * h (-1 / w)) = -h (-1 / w) := by field_simp
  have hsub : (wMap f w - w) * (1 + (-1 / w) * h (-1 / w)) = h (-1 / w) := by
    rw [wMap_eq_ne hr hf hw0 hN, sub_mul, div_mul_cancel₀ _ hne]
    rw [show w - w * (1 + (-1 / w) * h (-1 / w))
        = -(w * ((-1 / w) * h (-1 / w))) by ring, key, neg_neg]
  calc wMap f w - w
      = ((wMap f w - w) * (1 + (-1 / w) * h (-1 / w))) / (1 + (-1 / w) * h (-1 / w)) :=
        (mul_div_cancel_right₀ _ hne).symm
    _ = h (-1 / w) / (1 + (-1 / w) * h (-1 / w)) := by rw [hsub]

/-- **Near-translation of the pull-back, without a half-plane hypothesis.**  For any `x`
with `1/r < ‖x‖` and `4 ≤ ‖x‖` (in particular `x ≠ 0`), the chart-conjugate dynamics
`wMap f` is translation by `1` up to `O(1/‖x‖)`:
`‖wMap f x - x - 1‖ ≤ Ksub A a / ‖x‖`. -/
theorem near_translation_mod {f h : ℂ → ℂ} {a : ℂ} {r A A' : ℝ}
    (hb : ParabolicBounds f h a r A A') {x : ℂ} (hx : 1 / r < ‖x‖) (hx4 : 4 ≤ ‖x‖) :
    ‖wMap f x - x - 1‖ ≤ Work.FatouCoord.Estimate.Ksub A a / ‖x‖ := by
  have hnw : 0 < ‖x‖ := lt_of_lt_of_le (by norm_num : (0 : ℝ) < 4) hx4
  have hx0 : x ≠ 0 := norm_ne_zero_iff.mp (ne_of_gt hnw)
  obtain ⟨_, hz, hz1, hzn, hzh, h1zh, _⟩ := Estimate.wMap_aux_facts hb hx hx4
  have hsub := wMap_sub_eq_ne hb.hr hb.f_eq hx0 hx h1zh
  have hstep : (h (-1 / x) / (1 + (-1 / x) * h (-1 / x)) - 1) * (1 + (-1 / x) * h (-1 / x))
      = h (-1 / x) - (1 + (-1 / x) * h (-1 / x)) := by
    rw [sub_mul, div_mul_cancel₀ _ h1zh, one_mul]
  have hident : (wMap f x - x - 1) * (1 + (-1 / x) * h (-1 / x))
      = (h (-1 / x) - 1 - a * (-1 / x)) * (1 - (-1 / x)) + (a - 1) * (-1 / x)
          - a * (-1 / x) ^ 2 := by
    rw [show wMap f x - x - 1 = h (-1 / x) / (1 + (-1 / x) * h (-1 / x)) - 1 by
      rw [hsub], hstep]
    ring
  have hden : 1 / 2 ≤ ‖1 + (-1 / x) * h (-1 / x)‖ := by
    have h1 : ‖(1 : ℂ)‖ ≤ ‖1 + (-1 / x) * h (-1 / x)‖ + ‖(-1 / x) * h (-1 / x)‖ := by
      have hh := norm_sub_le (1 + (-1 / x) * h (-1 / x)) ((-1 / x) * h (-1 / x))
      simpa using hh
    rw [norm_one] at h1
    linarith
  have hnum := Estimate.norm_sub_identity_bound hb hz hzn
  have hEB2 : ‖wMap f x - x - 1‖ * ‖1 + (-1 / x) * h (-1 / x)‖
      ≤ (Estimate.Ksub A a / 2) * ‖(-1 / x : ℂ)‖ := by
    rw [← norm_mul, hident]
    exact hnum
  have hcell : ‖wMap f x - x - 1‖
      ≤ 2 * (‖wMap f x - x - 1‖ * ‖1 + (-1 / x) * h (-1 / x)‖) := by
    have h1 : 1 ≤ 2 * ‖1 + (-1 / x) * h (-1 / x)‖ := by linarith
    calc ‖wMap f x - x - 1‖ = ‖wMap f x - x - 1‖ * 1 := by ring
      _ ≤ ‖wMap f x - x - 1‖ * (2 * ‖1 + (-1 / x) * h (-1 / x)‖) :=
          mul_le_mul_of_nonneg_left h1 (norm_nonneg _)
      _ = 2 * (‖wMap f x - x - 1‖ * ‖1 + (-1 / x) * h (-1 / x)‖) := by ring
  calc ‖wMap f x - x - 1‖
      ≤ 2 * (‖wMap f x - x - 1‖ * ‖1 + (-1 / x) * h (-1 / x)‖) := hcell
    _ ≤ 2 * ((Estimate.Ksub A a / 2) * ‖(-1 / x : ℂ)‖) := by linarith [hEB2]
    _ = Estimate.Ksub A a / ‖x‖ := by rw [hz1]; ring

end

end Work.FatouCoord.Repelling
