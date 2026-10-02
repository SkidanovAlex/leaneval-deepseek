import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.PARIMPL2.Lavaurs.exists_normalForm_preimage
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.box_lands_step
import Submission.Work.FlowerGlue2.incr_defs
import Submission.Work.FlowerGlue2.incr_expansion_aux
import Submission.Work.FlowerGlue2.L0
import Submission.Work.PARIMPL.Basic

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.PARIMPL2.Lavaurs.deep_tail_preimage_shift` — the deep tail is in the image of the return
map, with a deep preimage and a uniform backward shift

In the `c₀`-chart `w₀ = -P.s c₀/(z - z₁)` (so `w₀ = -1/ζ` in the chart `z = m c₀ + s c₀·ζ`, and
`w₀ z → ∞` exactly when `z → d.z₁`), the second return map `Ft c₀` is conjugate to the parabolic
germ `φ ζ = ζ + ζ² h_{c₀} ζ` (`Work.FlowerGlue2.Ft_chart`).  Because `φ` is tangent to the
identity at the origin, it is locally invertible there
(`Work.PARIMPL2.Lavaurs.exists_normalForm_preimage`), so that every point `t` of the deep tail
is the image under `Ft c₀` of a point `y` which is *itself* in the deep tail.

Quantitatively: if `ζ` is the chart preimage of `ξ = -1/w₀ t`, then
`w₀ y = -1/ζ = w₀ t - h_{c₀}ζ/(1 + ζ h_{c₀}ζ)`, and the increment is bounded by `3/2` in modulus
on the smallness ball `rsmall P` (`Work.FlowerGlue2.incr_expansion_aux`).  Hence for a threshold
`M₀` with `‖w₀ t‖ ≥ 1/ε + 4` — which follows from `M₀ + 2 < Re (w₀ t)` — the preimage already
satisfies `Re (w₀ y) ≥ Re (w₀ t) - 3/2 > M₀`, and the *loss* along the backward step is at most
`C = 2`: `Re (w₀ t) ≤ Re (w₀ y) + C`.

This is the shifted form `Re (w₀ t) ≤ Re (w₀ y) + C` of the "deep tail is in the image, with a
deep preimage" statement, used to iterate the landing argument backwards along the tail.
-/

set_option autoImplicit false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open Classical Filter Set Metric
open scoped Topology

noncomputable section

namespace Work.PARIMPL2.Lavaurs

open Work.PARIMPL (ParNormal Ft)

theorem deep_tail_preimage_shift {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d) :
    ∃ M₀ C : ℝ, 0 ≤ C ∧ ∀ t : ℂ, M₀ + C < (Work.PARIMPL2.w0 P t).re →
      ∃ y : ℂ, M₀ < (Work.PARIMPL2.w0 P y).re ∧
        (Work.PARIMPL2.w0 P t).re ≤ (Work.PARIMPL2.w0 P y).re + C ∧
        Work.PARIMPL.Ft c₀ y = t := by
  obtain ⟨ε, hεpos, hε⟩ := exists_normalForm_preimage P
  refine ⟨1 / ε + 2, 2, by norm_num, ?_⟩
  intro t ht
  -- the chart coordinate of the target
  set W : ℂ := Work.PARIMPL2.w0 P t with hWdef
  have hWbig : 1 / ε + 4 < W.re := by linarith
  have hWpos : 0 < W.re := by
    have h1 : (0 : ℝ) < 1 / ε := one_div_pos.mpr hεpos
    linarith
  have hWne : W ≠ 0 := by
    intro h0
    rw [h0] at hWpos
    simp at hWpos
  -- the chart coordinate of the preimage
  set ξ : ℂ := -1 / W with hξdef
  have hξne : ξ ≠ 0 := div_ne_zero (by norm_num) hWne
  have hξnorm : ‖ξ‖ ≤ ε := by
    have hnormW : 1 / ε + 4 < ‖W‖ := lt_of_lt_of_le hWbig (Complex.re_le_norm W)
    have hpos : (0 : ℝ) < 1 / ε + 4 := by
      have h1 : (0 : ℝ) < 1 / ε := one_div_pos.mpr hεpos
      linarith
    have h1 : ‖ξ‖ = 1 / ‖W‖ := by rw [hξdef, norm_div, norm_neg, norm_one]
    rw [h1]
    have h2 : 1 / ‖W‖ ≤ 1 / (1 / ε + 4) := one_div_le_one_div_of_le hpos hnormW.le
    have h3 : 1 / (1 / ε + 4) ≤ ε := by
      rw [div_le_iff₀ hpos]
      have h4 : ε * (1 / ε) = 1 := by field_simp
      nlinarith
    linarith
  obtain ⟨ζ, hζeq, hζsmall⟩ := hε ξ hξnorm
  have hs : P.s c₀ ≠ 0 := P.s_ne c₀ (Metric.mem_ball_self P.hρ₀)
  have hζr : ‖ζ‖ < P.r := lt_of_le_of_lt hζsmall (Work.FlowerGlue2.rsmall_le_r P)
  have hζne : ζ ≠ 0 := by
    intro h0
    have : ξ = 0 := by rw [← hζeq, h0]; simp
    exact hξne this
  have hfac : ζ + ζ ^ 2 * P.h c₀ ζ = ζ * (1 + ζ * P.h c₀ ζ) := by ring
  have h1hζne : 1 + ζ * P.h c₀ ζ ≠ 0 := by
    intro h0
    have : ξ = 0 := by rw [← hζeq, hfac, h0, mul_zero]
    exact hξne this
  have ht_ne : t ≠ d.z₁ := by
    intro h0
    apply hWne
    rw [hWdef, h0]
    simp [Work.PARIMPL2.w0]
  -- the preimage point of the `z`-plane
  set y : ℂ := P.m c₀ + P.s c₀ * ζ with hydef
  have hsub' : y - d.z₁ = P.s c₀ * ζ := by
    rw [hydef, P.m₀]; ring
  have hw0y : Work.PARIMPL2.w0 P y = -1 / ζ := by
    rw [Work.PARIMPL2.w0, hsub']
    field_simp
  have hsξ : P.s c₀ * ξ = t - d.z₁ := by
    rw [hξdef, hWdef, Work.PARIMPL2.w0]
    field_simp
  have hFt : Ft c₀ y = d.z₁ + P.s c₀ * ξ := by
    have h := Work.FlowerGlue2.Ft_chart P hζr
    rw [hζeq] at h
    show Ft c₀ (P.m c₀ + P.s c₀ * ζ) = d.z₁ + P.s c₀ * ξ
    linear_combination h
  -- the two conclusions
  have hWval : W = -1 / ξ := by
    rw [hξdef]; field_simp
  have hmain : -1 / ζ = W - P.h c₀ ζ / (1 + ζ * P.h c₀ ζ) := by
    have hξval : ξ = ζ * (1 + ζ * P.h c₀ ζ) := by rw [← hζeq, hfac]
    rw [hWval, hξval]
    field_simp
    ring
  have hg : ‖P.h c₀ ζ / (1 + ζ * P.h c₀ ζ)‖ ≤ 3 / 2 :=
    (Work.FlowerGlue2.incr_expansion_aux P hζsmall).2.2
  have hre_le : (P.h c₀ ζ / (1 + ζ * P.h c₀ ζ)).re ≤ 3 / 2 :=
    le_trans (Complex.re_le_norm _) hg
  refine ⟨y, ?_, ?_, hFt.trans ?_⟩
  · rw [hw0y, hmain]
    simp only [Complex.sub_re]
    linarith
  · rw [hw0y, hmain]
    simp only [Complex.sub_re]
    linarith
  · rw [hsξ]; ring

end Work.PARIMPL2.Lavaurs

end
