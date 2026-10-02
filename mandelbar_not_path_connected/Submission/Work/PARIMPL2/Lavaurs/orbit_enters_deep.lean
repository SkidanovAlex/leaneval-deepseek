import Mathlib
import Submission.Work.PARIMPL2.Lavaurs.Defs
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.box_lands_step
import Submission.Work.FlowerGlue2.w0_step
import Submission.Work.PARIMPL.Basic
import Submission.Work.FatouCoordFix.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.PARIMPL2.Lavaurs.orbit_enters_deep`

Every orbit in the (wide) attracting petal of the parabolic point `d.z₁` of `Ft c₀` enters the
**deep** region `{Re (w0 P ·) > M}` of the `c₀`-chart, for every `M`.

The mechanism is the exact one-step identity of the chart at the parabolic parameter
(`Work.FlowerGlue2.w0_step`, with `P.h c₀ 0 = 1` supplied by `Work.FlowerGlue2.tau_c₀`):

`w0 P (Ft c₀ z) − w0 P z = h(ζ)/(1 + ζ h ζ)` with `ζ = (z − d.z₁)/P.s c₀`,

whose right-hand side tends to `h(0) = 1` as `ζ → 0`.  Hence there is `r > 0` such that

`Re (w0 P (Ft c₀ z)) ≥ Re (w0 P z) + 1/4` whenever `z ≠ d.z₁` and `‖z − d.z₁‖ < r`

(`w0_re_step_aux`).  An orbit in the petal converges to `d.z₁` (`ParabolicFlower.tendsto_Pa`) and
never hits it (`ParabolicFlower.z₀_not_mem` together with `MapsTo`), so from some time `N` on all
its points lie in that ball; the real part of the chart coordinate then grows by `≥ 1/4` at every
step, and therefore crosses every bound `M`.
-/

namespace Work.PARIMPL2.Lavaurs

open Filter Set Metric
open scoped Topology

/-- A point of a forward invariant set which avoids `z₁` never hits `z₁` along its orbit. -/
private lemma iterate_ne_of_notMem {G : ℂ → ℂ} {Pa : Set ℂ} {z₁ z : ℂ} (hmaps : MapsTo G Pa Pa)
    (hz₁ : z₁ ∉ Pa) (hz : z ∈ Pa) (n : ℕ) : G^[n] z ≠ z₁ := by
  intro hcon
  have hmem : G^[n] z ∈ Pa := Work.FatouCoord.mapsTo_iterate_of_mapsTo hmaps n hz
  rw [hcon] at hmem
  exact hz₁ hmem

/-- **The chart coordinate grows by at least `1/4` per step near the parabolic point.**  Since
`w0 P (Ft c₀ z) − w0 P z = h(ζ)/(1 + ζ h ζ) → 1` as `ζ = (z − d.z₁)/P.s c₀ → 0`, the increment
has real part `≥ 1/4` uniformly in the direction, as soon as `‖z − d.z₁‖` is below a positive
threshold.  (This is the direction-free form of the one-step estimate: no lower bound on
`Re (w0 P z)` is needed.) -/
private theorem w0_re_step_aux {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d) :
    ∃ r : ℝ, 0 < r ∧ ∀ z : ℂ, z ≠ d.z₁ → ‖z - d.z₁‖ < r →
      (Work.PARIMPL2.w0 P z).re + 1 / 4 ≤
        (Work.PARIMPL2.w0 P (Work.PARIMPL.Ft c₀ z)).re := by
  obtain ⟨r, hr, C, hC, H⟩ := Work.FlowerGlue2.w0_step P (Work.FlowerGlue2.tau_c₀ P)
  refine ⟨min r (1 / (4 * (C + 1))), lt_min hr (div_pos one_pos (by linarith)), ?_⟩
  intro z hz hzd
  have hr' : ‖z - d.z₁‖ < r := lt_of_lt_of_le hzd (min_le_left _ _)
  have hδ : ‖z - d.z₁‖ < 1 / (4 * (C + 1)) := lt_of_lt_of_le hzd (min_le_right _ _)
  obtain ⟨-, hbound⟩ := H z hz hr'
  -- the increment is within `1/4` of `1`
  have hb : ‖Work.FlowerGlue2.w0 P (Work.PARIMPL.Ft c₀ z) - Work.FlowerGlue2.w0 P z - 1‖
      ≤ 1 / 4 := by
    refine le_trans hbound ?_
    have h2 : C * (1 / (4 * (C + 1))) ≤ 1 / 4 := by
      have h3 : C ≤ C + 1 := by linarith
      have h4 : C * (1 / (4 * (C + 1))) = C / (4 * (C + 1)) := by ring
      rw [h4]
      calc C / (4 * (C + 1)) ≤ (C + 1) / (4 * (C + 1)) :=
            div_le_div_of_nonneg_right h3 (by linarith)
        _ = 1 / 4 := by field_simp
    exact le_trans (mul_le_mul_of_nonneg_left hδ.le hC) h2
  -- hence the real part of the increment is `≥ 3/4`
  have hkey : 3 / 4 ≤
      (Work.FlowerGlue2.w0 P (Work.PARIMPL.Ft c₀ z) - Work.FlowerGlue2.w0 P z).re := by
    have h5 : -(‖Work.FlowerGlue2.w0 P (Work.PARIMPL.Ft c₀ z) - Work.FlowerGlue2.w0 P z - 1‖)
        ≤ (Work.FlowerGlue2.w0 P (Work.PARIMPL.Ft c₀ z) - Work.FlowerGlue2.w0 P z - 1).re := by
      linarith [neg_abs_le (Work.FlowerGlue2.w0 P (Work.PARIMPL.Ft c₀ z)
          - Work.FlowerGlue2.w0 P z - 1).re,
        Complex.abs_re_le_norm (Work.FlowerGlue2.w0 P (Work.PARIMPL.Ft c₀ z)
          - Work.FlowerGlue2.w0 P z - 1)]
    have h6 : (Work.FlowerGlue2.w0 P (Work.PARIMPL.Ft c₀ z) - Work.FlowerGlue2.w0 P z - 1).re
        = (Work.FlowerGlue2.w0 P (Work.PARIMPL.Ft c₀ z) - Work.FlowerGlue2.w0 P z).re - 1 := by
      rw [Complex.sub_re, Complex.one_re]
    linarith
  have hfinal : (Work.FlowerGlue2.w0 P z).re + 1 / 4
      ≤ (Work.FlowerGlue2.w0 P (Work.PARIMPL.Ft c₀ z)).re := by
    have h7 : (Work.FlowerGlue2.w0 P (Work.PARIMPL.Ft c₀ z) - Work.FlowerGlue2.w0 P z).re
        = (Work.FlowerGlue2.w0 P (Work.PARIMPL.Ft c₀ z)).re - (Work.FlowerGlue2.w0 P z).re :=
      Complex.sub_re _ _
    linarith
  simpa only [Work.FlowerGlue2.w0, Work.PARIMPL2.w0] using hfinal

theorem orbit_enters_deep {c₀ : ℂ} {d : Work.EL.RootParabolic c₀} (P : Work.PARIMPL.ParNormal d)
    (fl : Work.FatouCoordFix.ParabolicFlowerFix (Work.PARIMPL.Ft c₀) (Work.PARIMPL.gtc c₀) d.z₁)
    (z : ℂ) (hz : z ∈ fl.Pa) (M : ℝ) :
    ∃ n : ℕ, M < (Work.PARIMPL2.w0 P ((Work.PARIMPL.Ft c₀)^[n] z)).re := by
  obtain ⟨r, hr, hstep⟩ := w0_re_step_aux P
  -- the orbit lies in the petal, hence converges to `d.z₁` and never hits it
  have hconv : Tendsto (fun n : ℕ => (Work.PARIMPL.Ft c₀)^[n] z) atTop (nhds d.z₁) :=
    fl.tendsto_Pa z hz
  have hne : ∀ n : ℕ, (Work.PARIMPL.Ft c₀)^[n] z ≠ d.z₁ :=
    fun n => iterate_ne_of_notMem fl.mapsTo_Pa fl.z₀_not_mem hz n
  -- from some time on, the orbit is in the small ball of `w0_re_step_aux`
  have hev : ∀ᶠ n : ℕ in atTop, ‖(Work.PARIMPL.Ft c₀)^[n] z - d.z₁‖ < r := by
    filter_upwards [hconv.eventually (Metric.ball_mem_nhds d.z₁ hr)] with n hn
    simpa [Metric.mem_ball, dist_eq_norm] using hn
  obtain ⟨N, hN⟩ := eventually_atTop.mp hev
  -- the real part of the chart coordinate grows by `1/4` per step from time `N` on
  have hmain : ∀ k : ℕ,
      (Work.PARIMPL2.w0 P ((Work.PARIMPL.Ft c₀)^[N] z)).re + k / 4 ≤
        (Work.PARIMPL2.w0 P ((Work.PARIMPL.Ft c₀)^[N + k] z)).re := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      have hclose : ‖(Work.PARIMPL.Ft c₀)^[N + k] z - d.z₁‖ < r :=
        hN (N + k) (Nat.le_add_right N k)
      have hst := hstep ((Work.PARIMPL.Ft c₀)^[N + k] z) (hne (N + k)) hclose
      rw [show N + (k + 1) = (N + k) + 1 by ring, Function.iterate_succ_apply']
      push_cast
      linarith
  obtain ⟨k, hk⟩ := exists_nat_gt
    (4 * (M - (Work.PARIMPL2.w0 P ((Work.PARIMPL.Ft c₀)^[N] z)).re))
  refine ⟨N + k, ?_⟩
  have h1 := hmain k
  have h2 : M < (Work.PARIMPL2.w0 P ((Work.PARIMPL.Ft c₀)^[N] z)).re + k / 4 := by linarith
  linarith

end Work.PARIMPL2.Lavaurs
