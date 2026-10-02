/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue2 team
-/
import Mathlib
import Submission.Work.FlowerGlue2.Defs

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.h_c0_differentiableOn` — the germ `P.h c₀` is holomorphic

`Work.PARIMPL.ParNormal` exports only the *continuity* of the two-variable germ `h` on
`ball c₀ ρ₀ ×ˢ ball 0 r` (`cont_h`) and the *uniform bounds* `ParBounds`; the repelling
construction of the area (`Work.FlowerGlue2.parabolicBounds_of_normalForm`, the
`ParabolicBounds` of `Work.FatouCoord`) however needs `h c₀` to be differentiable — this is the
"one structural gap of the repelling side" flagged in `Submission/Work/FlowerGlue2/NOTES.md` §6.

It is nevertheless a *theorem*, not an extra hypothesis: at the parabolic parameter `c₀` the
conjugacy `conj` of the normal form pins the germ down.  Since `a c₀ = 0` (because `a₂ c₀ = 0`
and `a c₀² = a₂ c₀`) and `m c₀ = d.z₁`, the identity reads

  `F c₀ (d.z₁ + s c₀·ζ) = d.z₁ + s c₀·(ζ + ζ²·h c₀ ζ)`,

so on the chart ball minus the critical point `0`

  `h c₀ ζ = (F c₀ (d.z₁ + s c₀·ζ) − d.z₁ − s c₀·ζ) / (s c₀·ζ²)`,

a function which is holomorphic there because `F c₀ = (Tsq c₀)^[5]` is a polynomial in `ζ`.
Together with the continuity of `h c₀` at `0` (the slice `c = c₀` of `cont_h`) Riemann's
removable-singularity theorem (`Complex.differentiableOn_compl_singleton_and_continuousAt_iff`)
fills in the point `0`.
-/

set_option linter.unusedVariables false

open scoped Topology
open Metric Set

noncomputable section

namespace Work.FlowerGlue2

theorem h_c0_differentiableOn {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}
    (P : Work.PARIMPL.ParNormal d) :
    DifferentiableOn ℂ (P.h c₀) (Metric.ball (0 : ℂ) P.r) := by
  have hmem : c₀ ∈ Metric.ball c₀ P.ρ₀ := Metric.mem_ball_self P.hρ₀
  have hs : P.s c₀ ≠ 0 := P.s_ne c₀ hmem
  -- the chosen root vanishes at the parabolic parameter, where `a₂ c₀ = 0`
  have ha : P.a c₀ = 0 := by
    have h := P.a_sq c₀ hmem
    rw [P.a2₀] at h
    have h2 : P.a c₀ ^ 2 = 0 := by simpa using h
    exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp h2
  -- `F c₀ = (Tsq c₀)^[5]` is a polynomial, hence entire
  have hF : Differentiable ℂ (Work.EL.F c₀) := by
    have hTsq : Differentiable ℂ (Work.Landing.Tsq c₀) := by
      unfold Work.Landing.Tsq; fun_prop
    exact hTsq.iterate 5
  -- `h c₀` is continuous at the critical point, being the slice `c = c₀` of `cont_h`
  have hcont : ContinuousAt (fun ζ : ℂ => P.h c₀ ζ) 0 := by
    have hsec : ContinuousOn (fun ζ : ℂ => P.h c₀ ζ) (Metric.ball (0 : ℂ) P.r) := by
      have hcomp := P.cont_h.comp (f := fun ζ : ℂ => (c₀, ζ))
        (continuous_const.prodMk continuous_id).continuousOn (fun ζ hζ => ⟨hmem, hζ⟩)
      refine hcomp.congr ?_
      intro ζ hζ
      rfl
    exact hsec.continuousAt (Metric.ball_mem_nhds 0 P.hr)
  -- the conjugacy of the normal form, solved for `h c₀`
  have key : ∀ ζ ∈ Metric.ball (0 : ℂ) P.r,
      P.h c₀ ζ * (P.s c₀ * ζ ^ 2)
        = Work.EL.F c₀ (d.z₁ + P.s c₀ * ζ) - d.z₁ - P.s c₀ * ζ := by
    intro ζ hζ
    have h := P.conj c₀ hmem ζ hζ
    have h' := h
    rw [P.m₀, Work.Implosion.normalForm, ha] at h'
    have h'' : Work.EL.F c₀ (d.z₁ + P.s c₀ * ζ)
        = d.z₁ + P.s c₀ * (ζ + (ζ ^ 2 - (0 : ℂ) ^ 2) * P.h c₀ ζ) := h'
    rw [h'']; ring
  -- off the critical point `h c₀` is the holomorphic quotient above
  have hpunct : DifferentiableOn ℂ (P.h c₀) (Metric.ball (0 : ℂ) P.r \ {0}) := by
    refine DifferentiableOn.congr
      (f := fun ζ : ℂ =>
        (Work.EL.F c₀ (d.z₁ + P.s c₀ * ζ) - d.z₁ - P.s c₀ * ζ) / (P.s c₀ * ζ ^ 2)) ?_ ?_
    · have hnum : DifferentiableOn ℂ (fun ζ : ℂ =>
          Work.EL.F c₀ (d.z₁ + P.s c₀ * ζ) - d.z₁ - P.s c₀ * ζ)
          (Metric.ball (0 : ℂ) P.r \ {0}) := by
        fun_prop
      have hden : DifferentiableOn ℂ (fun ζ : ℂ => P.s c₀ * ζ ^ 2)
          (Metric.ball (0 : ℂ) P.r \ {0}) := by
        fun_prop
      exact hnum.div hden (fun ζ hζ => mul_ne_zero hs (pow_ne_zero 2 hζ.2))
    · intro ζ hζ
      rw [eq_div_iff (mul_ne_zero hs (pow_ne_zero 2 hζ.2))]
      exact key ζ hζ.1
  -- Riemann's removable singularity at `0`
  exact (Complex.differentiableOn_compl_singleton_and_continuousAt_iff (s := Metric.ball (0 : ℂ) P.r)
    (c := 0) (Metric.ball_mem_nhds 0 P.hr)).1 ⟨hpunct, hcont⟩

end Work.FlowerGlue2
