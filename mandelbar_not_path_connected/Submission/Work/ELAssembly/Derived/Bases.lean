/-
# `ELAssembly.Derived.Bases` — the landing-point bases and shifts of the two nests

This file collects, for the *pair data* `Work.ELAssembly.NestPairs d` of the assembly (rather
than for the `Work.ELNest.NestData` interface), the landing-point facts that the derivations of
`NOTES.md` §7.8 need:

* `Work.ELAssembly.cycle_lands` — the two-ray portrait at every point of the parabolic cycle
  (`Work.ELAssembly.PbAvoid_portrait`, restated);
* `Work.ELAssembly.Qp_y_shift` — `F c ((Qp (n+1)).y) = (Qp n).y` (`Work.ELNest.Qp_shift` for
  `NestPairs`);
* `Work.ELAssembly.Za_y_base`, `Zb_y_base`, `Zc_y_base` — the level-`0` arm landing points are
  the cycle points `z₁`, `T² z₁`, `T⁴ z₁` (the arm angles at level `0` are `α₁, α₂`,
  `T²α₁, T²α₂`, `T⁴α₁, T⁴α₂`).
-/
import Mathlib
import Submission.Work.ELAssembly.PbAvoid_portrait
import Submission.Work.ELAssembly.PbAvoid_cycle
import Submission.Work.ELAssembly.armChainInputs_of
import Submission.Work.ELAssembly.pullQ_pair
import Submission.Work.ELAssembly.base_shift_of
import Submission.Work.ELAssembly.landsN_add_int
import Submission.Work.ELNest.Qp_shift
import Submission.Work.ELTop.landsN_iff_landsAt

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


open Classical Filter Set
open scoped Topology

set_option linter.unusedVariables false

noncomputable section

namespace Work.ELAssembly

open LeanEval.ComplexAnalysis (Tantibar Mandelbar)

variable {c : ℂ}

/-- The two canonical `F`'s of the workspace agree. -/
theorem EL_F_eq_ELNest_F (c : ℂ) : Work.EL.F c = Work.ELNest.F c := rfl

/-- **The two-ray portrait at every point of the parabolic cycle** (wrapper of
`Work.ELAssembly.PbAvoid_portrait`). -/
theorem cycle_lands (d : Work.EL.RootParabolic c)
    (hzero : ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ d.z₁ ↔ θ = Work.EL.alpha1 ∨ θ = Work.EL.alpha2))
    (hcount : Work.ELPull.PortraitCount (hNcanOf d)) (j : ℕ) (hj : j < 5) :
    ∀ θ : ℝ, θ ∈ Set.Ico 0 1 →
      (Work.EL.LandsN d.hN θ (((Tantibar c)^[j]) d.z₁) ↔
        θ = (Work.EL.T^[j]) Work.EL.alpha1 ∨ θ = (Work.EL.T^[j]) Work.EL.alpha2) :=
  PbAvoid_portrait d hzero hcount (PbAvoid_cycle d).1 j hj

/-- **The `F`-shift of the landing points of the `z₁`-nest** (certificate N1 for the pair data
`NestPairs`), the `NestPairs` form of `Work.ELNest.Qp_shift`. -/
theorem Qp_y_shift (d : Work.EL.RootParabolic c) (N : NestPairs d) (n : ℕ) :
    Work.EL.F c ((N.Qp (n + 1)).y) = (N.Qp n).y := by
  have hlan : Work.EL.LandsN d.hN
      ((Work.EL.T^[10]) (Work.ELNest.bAng' (n + 1))) (Work.ELNest.F c ((N.Qp (n + 1)).y)) :=
    Work.ELNest.landsN_iterate_F d.hN d.bottcher (N.Qpa (n + 1) ▸ (N.Qp (n + 1)).lands_a)
  rw [(pullQ_pair n).1] at hlan
  have h2 : Work.EL.LandsN d.hN (Work.ELNest.bAng' n) (N.Qp n).y :=
    N.Qpa n ▸ (N.Qp n).lands_a
  rw [EL_F_eq_ELNest_F]
  exact (Work.ELNest.landsN_unique h2 hlan).symm

/-- **The level-`0` arm-`A` landing point is `z₁`.** -/
theorem Za_y_base (d : Work.EL.RootParabolic c) (N : NestPairs d) :
    (N.Za 0).y = d.z₁ := by
  have h1 : Work.EL.LandsN d.hN (Work.ELNest.armA1 0) (N.Za 0).y :=
    N.Zaa 0 ▸ (N.Za 0).lands_a
  rw [armA1_zero_angle] at h1
  have h0 : Work.EL.LandsN d.hN Work.EL.alpha1 d.z₁ :=
    (Work.ELTop.landsN_iff_landsAt d.hN d.bottcher Work.EL.alpha1 d.z₁).mpr d.rays.1
  exact Work.ELNest.landsN_unique h1 h0

/-- **The level-`0` arm-`B` landing point is `T² z₁`.** -/
theorem Zb_y_base (d : Work.EL.RootParabolic c) (N : NestPairs d) :
    (N.Zb 0).y = ((Tantibar c)^[2]) d.z₁ := by
  have h1 : Work.EL.LandsN d.hN (Work.ELNest.armB1 0) (N.Zb 0).y :=
    N.Zba 0 ▸ (N.Zb 0).lands_a
  rw [armB1_zero_angle, ← alpha_T2_first] at h1
  have h0 : Work.EL.LandsN d.hN ((Work.EL.T^[2]) Work.EL.alpha1)
      (((Tantibar c)^[2]) d.z₁) :=
    (PbAvoid_cycle d).1 2 |>.1
  exact Work.ELNest.landsN_unique h1 h0

/-- **The level-`0` arm-`C` landing point is `T⁴ z₁`.** -/
theorem Zc_y_base (d : Work.EL.RootParabolic c) (N : NestPairs d) :
    (N.Zc 0).y = ((Tantibar c)^[4]) d.z₁ := by
  have h1 : Work.EL.LandsN d.hN (Work.ELNest.armC1 0) (N.Zc 0).y :=
    N.Zca 0 ▸ (N.Zc 0).lands_a
  rw [armC1_zero_angle, ← alpha_T4_first] at h1
  have h0 : Work.EL.LandsN d.hN ((Work.EL.T^[4]) Work.EL.alpha1)
      (((Tantibar c)^[4]) d.z₁) :=
    (PbAvoid_cycle d).1 4 |>.1
  exact Work.ELNest.landsN_unique h1 h0

end Work.ELAssembly
