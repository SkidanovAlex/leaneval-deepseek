/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue2 team
-/
import Mathlib
import Submission.Work.FlowerGlue2.Defs
import Submission.Work.FlowerGlue2.chart_scale_eq
import Submission.Work.FlowerGlue.exists_refCoord
import Submission.Work.FlowerGlue.Model

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.exists_refCoord_P_normalForm` — L0.6 (chart consistency)

The reference attracting Fatou coordinate of a root-parabolic parameter, expressed in the
**chart of the parameter normal form** `P : ParNormal d` at the parabolic parameter `c₀`
(`w0 P z = -P.s c₀ / (z - d.z₁)`, the coordinate `-1/ζ_{c₀}` of `z = m c₀ + s c₀·ζ`).

The datum `D : RefData d` supplies a reference coordinate `D.toRef` together with its asymptotic
in the germ chart `u ↦ d.z₁ + D.lam·u` of `Work.FatouCoord.Flower.germ_bounds`:

  `‖D.toRef.φ z - approxCoord (1 - D.ap) (-D.lam/(z - d.z₁))‖ ≤ D.K / Re (-D.lam/(z - d.z₁))`.

The content of the present statement is the **chart comparison** (L0.6 of
`Submission/Work/NOTES_LEAD_mandelbar_implosion.md` §3.2): the two affine charts at `z₁` in which
`F c₀` reads `ζ ↦ ζ + ζ²·(germ)` are the same chart, so

  `D.lam = P.s c₀`   and   `D.ap = P.h1 c₀`,

which (with `P.h c₀ 0 = 1`) turns `1 - D.ap` into `P.κ c₀`.  Hence the asymptotic of `D` is
literally the asymptotic in the chart of `P`, and the half-plane petal of `D` is the one cut out
by `Re (w0 P ·) > N`.  The comparison itself is the (verified, general) lemma
`Work.FlowerGlue2.chart_scale_eq` of `Submission/Work/FlowerGlue2/chart_scale_eq.lean`, applied to
the chart germ of `ParNormal` at `c₀` and to the germ datum of `RefData`.
-/

open scoped Topology
open Set Filter Metric

namespace Work.FlowerGlue2

/-- The continuity at `0` of the germ of the parameter normal form `P.h c₀`. -/
private theorem continuousAt_h_c₀ {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d) : ContinuousAt (fun ζ : ℂ => P.h c₀ ζ) 0 := by
  have hs : (Metric.ball c₀ P.ρ₀ ×ˢ Metric.ball (0:ℂ) P.r) ∈ 𝓝 (c₀, (0:ℂ)) :=
    (Metric.isOpen_ball.prod Metric.isOpen_ball).mem_nhds
      ⟨mem_ball_self P.hρ₀, mem_ball_self P.hr⟩
  have hct : ContinuousAt (fun p : ℂ × ℂ => P.h p.1 p.2) (c₀, (0:ℂ)) :=
    P.cont_h.continuousAt hs
  have hcomp : ContinuousAt (fun ζ : ℂ => (c₀, ζ)) (0:ℂ) :=
    continuousAt_const.prodMk continuousAt_id
  exact hct.comp hcomp

/-- **The two charts at `z₁` coincide** (L0.6, chart uniqueness).  The reference germ chart
`u ↦ d.z₁ + D.lam·u` of the datum `D` and the chart `ζ ↦ d.z₁ + P.s c₀·ζ` of the parameter
normal form `P` are charts in which `F c₀` reads `ζ + ζ²·(germ)` with `germ 0 = 1`; hence they
agree on the scale (`D.lam = P.s c₀`) and on the linear coefficient of the germ
(`D.ap = P.h1 c₀`). -/
private theorem refData_chart_eq {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d) (hτ : P.h c₀ 0 = 1) (D : RefData d) :
    D.lam = P.s c₀ ∧ D.ap = P.h1 c₀ := by
  have hρ : c₀ ∈ Metric.ball c₀ P.ρ₀ := mem_ball_self P.hρ₀
  -- at the root parameter the two split fixed points collide: `a c₀ = 0`, so that the normal
  -- form of `P` at `c₀` is `ζ ↦ ζ + ζ²·(P.h c₀ ζ)`
  have ha0 : P.a c₀ = 0 := by
    have h := P.a_sq c₀ hρ
    rw [P.a2₀] at h
    simpa using sq_eq_zero_iff.mp h
  exact chart_scale_eq (F := Work.EL.F c₀) (z₁ := d.z₁) (γ := D.lam) (s := P.s c₀)
    (f₁ := D.f) (h₁ := D.h) (a₁ := D.ap) (r₁ := D.r) (A₁ := D.A)
    (f₂ := fun ζ => ζ + ζ ^ 2 * P.h c₀ ζ) (h₂ := P.h c₀) (a₂ := P.h1 c₀) (r₂ := P.r) (A₂ := P.A)
    D.lam_ne (P.s_ne c₀ hρ) D.hb.hr P.hr
    (fun z hz => D.hb.f_eq z (by simpa [Metric.mem_ball, dist_zero_right] using hz))
    (fun z hz => D.hb.h_close z (by simpa [Metric.mem_ball, dist_zero_right] using hz))
    (D.hb.h_diff.differentiableAt
      (Metric.isOpen_ball.mem_nhds (Metric.mem_ball_self D.hb.hr))).continuousAt
    (fun ζ _ => rfl)
    (fun z hz => by
      have h := (P.bounds c₀ hρ).2.2.1 z hz
      rwa [hτ] at h)
    (continuousAt_h_c₀ P)
    (fun u hu => D.conj u (by simpa [Metric.mem_ball, dist_zero_right] using hu))
    (fun u hu => by
      have hu' : u ∈ Metric.ball (0 : ℂ) P.r := by
        simpa [Metric.mem_ball, dist_zero_right] using hu
      have h1 := P.conj c₀ hρ u hu'
      rw [P.m₀, ha0] at h1
      simpa [Work.Implosion.normalForm] using h1)

theorem exists_refCoord_P_normalForm {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d) (hτ : P.h c₀ 0 = 1) (D : Work.FlowerGlue2.RefData d) :
    ∃ Rf : Work.FlowerGlue.RefCoord d, ∃ N K : ℝ, 0 < N ∧ 0 ≤ K ∧
      (∀ z : ℂ, z ≠ d.z₁ → N < (Work.FlowerGlue2.w0 P z).re → z ∈ Rf.P) ∧
      ∀ z : ℂ, z ≠ d.z₁ → N < (Work.FlowerGlue2.w0 P z).re →
        ‖Rf.φ z - Work.FatouCoord.approxCoord (P.κ c₀) (Work.FlowerGlue2.w0 P z)‖
          ≤ K / (Work.FlowerGlue2.w0 P z).re := by
  obtain ⟨hlam, hap⟩ := refData_chart_eq P hτ D
  have hρ : c₀ ∈ Metric.ball c₀ P.ρ₀ := mem_ball_self P.hρ₀
  -- `1 - D.ap = P.κ c₀` at the root parameter, where `P.h c₀ 0 = 1`
  have hκ : (1 : ℂ) - D.ap = P.κ c₀ := by
    obtain ⟨-, hκeq⟩ := P.κ_eq c₀ hρ
    rw [← hap, hτ] at hκeq
    rw [hκeq]
    simp
  -- the half-plane `Re (w0 P ·) > N` is exactly the half-plane of the `D.lam`-chart
  have hhalf : ∀ z : ℂ, z ≠ d.z₁ → D.N < (w0 P z).re →
      D.N < (-D.lam / (z - d.z₁)).re := by
    intro z _ hN
    rw [w0_apply, ← hlam] at hN
    exact hN
  refine ⟨D.toRef, D.N, D.K, D.N_pos, D.K_nonneg, ?_, ?_⟩
  · intro z hz hN
    exact D.mem_P z hz (hhalf z hz hN)
  · intro z hz hN
    have h := D.asymp z hz (hhalf z hz hN)
    rw [hκ, hlam] at h
    simpa only [w0_apply] using h

end Work.FlowerGlue2
