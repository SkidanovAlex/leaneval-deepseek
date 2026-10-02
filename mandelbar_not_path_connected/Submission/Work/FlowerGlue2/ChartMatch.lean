/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: FlowerGlue2 team
-/
import Submission.Work.FlowerGlue2.L0
import Submission.Work.FlowerGlue2.exists_refData_rootParabolic
import Submission.Work.FlowerGlue2.exists_refCoord_P_normalForm

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


/-!
# `Work.FlowerGlue2.ChartMatch` — L0.6: the reference coordinate in the `w0` chart

`Submission/Work/NOTES_LEAD_mandelbar_implosion.md` §3.2 (L0.6).  The reference attracting Fatou
coordinate of `Work.FlowerGlue2.exists_refData_rootParabolic` lives in the germ chart
`u ↦ d.z₁ + λ_f·u`; the parameter normal form `P` lives in the chart `ζ ↦ P.m c + P.s c·ζ`
(`P.m c₀ = d.z₁`).  By `Work.FlowerGlue2.tau_c₀` the germ constant at `c₀` is `1`, which pins
the two charts together (`λ_f = P.s c₀`, `a_f = P.h1 c₀`, hence `1 - a_f = P.κ c₀`), and the
asymptotic of the reference coordinate becomes

  `‖Rf.φ z - approxCoord (P.κ c₀) (w0 P z)‖ ≤ K / Re (w0 P z)`

on the half-plane `Re (w0 P ·) > N`.
-/

open scoped Topology
open Filter Set Metric

namespace Work.FlowerGlue2

open Work.PARIMPL (ParNormal Ft gtc)

noncomputable section

variable {c₀ : ℂ} {d : Work.EL.RootParabolic c₀}

/-- **L0.6.**  There is a reference coordinate whose petal contains the whole half-plane
`Re (w0 P ·) > N`, and whose coordinate differs from `approxCoord (P.κ c₀) (w0 P ·)` by
`O(1/Re (w0 P ·))` there.  This is the chart-matching input of the attracting comparison N1
(`Work.FlowerGlue2.attr_norm`) and of `Work.FlowerGlue2.box_deep`. -/
theorem exists_refCoord_P (P : ParNormal d) (hτ : P.h c₀ 0 = 1) :
    ∃ Rf : Work.FlowerGlue.RefCoord d, ∃ N K : ℝ, 0 < N ∧ 0 ≤ K ∧
      (∀ z : ℂ, z ≠ d.z₁ → N < (w0 P z).re → z ∈ Rf.P) ∧
      ∀ z : ℂ, z ≠ d.z₁ → N < (w0 P z).re →
        ‖Rf.φ z - Work.FatouCoord.approxCoord (P.κ c₀) (w0 P z)‖ ≤ K / (w0 P z).re := by
  obtain ⟨D⟩ := exists_refData_rootParabolic d
  exact exists_refCoord_P_normalForm P hτ D

/-- The same, with the chart constant `hτ` supplied by `Work.FlowerGlue2.tau_c₀`. -/
theorem exists_refCoord_P' (P : ParNormal d) :
    ∃ Rf : Work.FlowerGlue.RefCoord d, ∃ N K : ℝ, 0 < N ∧ 0 ≤ K ∧
      (∀ z : ℂ, z ≠ d.z₁ → N < (w0 P z).re → z ∈ Rf.P) ∧
      ∀ z : ℂ, z ≠ d.z₁ → N < (w0 P z).re →
        ‖Rf.φ z - Work.FatouCoord.approxCoord (P.κ c₀) (w0 P z)‖ ≤ K / (w0 P z).re :=
  exists_refCoord_P P (tau_c₀ P)

end

end Work.FlowerGlue2
