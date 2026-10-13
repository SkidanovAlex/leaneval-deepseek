/-
# `C⁴`-smoothness of the 27 pieces of the §8 assembly

The summands `N0fix, N03g, …, N5ss` of `Submission/Work/FTS/Nonlinear/Defs.lean` are products,
sums and constant multiples of the factors collected in `Work.FTS.OpenPkg.FourFactors`; hence
each of them is `C^4` on the open quadrant `Q0 = (0,∞) × (0,π/2)` once its factors are.

This is what makes `Work.Spaces.HkMem α 4` of a *sum* of pieces derivable from the honesty of
its summands (`Work.FTS.OpenPkg.HkMem_add_of_contDiffOn_four`), which is exactly what the
primed `add` clause of `Work.FTS.OpenPkg.N4Extra'` consumes.

All the proofs are the definitional unfolding of the piece followed by the closure of
`ContDiffOn ℝ 4` under constant multiples and products.
-/
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.InnerProductSpace.Basic
import Submission.Work.FTS.OpenPkg.FourFactors

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.OpenPkg

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## The `N₀`-block (rows 1--7) -/

theorem contDiffOn_four_N0fix {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N0fix α)) Q0 := by
  have h1 : ContDiffOn ℝ 4 (Function.uncurry (fun z θ =>
      (3 / (2 * α)) * Real.sin (2 * θ) * Work.Construction.L12 (Work.Construction.Fstar α) z
        * Work.Spaces.pth (Work.Construction.Fstar α) z θ)) Q0 :=
    (((contDiffOn_const.mul (contDiffOn_s2_Q0 4)).mul h.hL12F).mul h.hpthF)
  have h2 : ContDiffOn ℝ 4 (Function.uncurry (fun z θ =>
      (-(Real.cos (2 * θ) - Real.sin θ ^ 2))
        * Work.Construction.L12 (Work.Construction.Fstar α) z
        * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)) Q0 :=
    (((contDiffOn_c2m_Q0 4).neg).mul h.hL12F).mul h.hDzF
  exact h1.add h2

theorem contDiffOn_four_N03g {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N03g α g)) Q0 :=
  (contDiffOn_const.mul h.hL12g).mul h.hg

theorem contDiffOn_four_N04aF {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N04aF α g)) Q0 :=
  (((contDiffOn_const.mul (contDiffOn_s2_Q0 4)).mul h.hL12g).mul h.hpthF)

theorem contDiffOn_four_N04bF {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N04bF α g)) Q0 :=
  (((contDiffOn_const.mul (contDiffOn_s2_Q0 4)).mul h.hL12g).mul h.hpthg)

theorem contDiffOn_four_N05aF {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N05aF α g)) Q0 :=
  (((contDiffOn_c2m_Q0 4).neg).mul h.hL12g).mul h.hDzF

theorem contDiffOn_four_N05bF {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N05bF α g)) Q0 :=
  (((contDiffOn_c2m_Q0 4).neg).mul h.hL12g).mul h.hDzg

theorem contDiffOn_four_N06F {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N06F α g)) Q0 :=
  (((contDiffOn_c2m_Q0 4).neg).mul h.hL12F).mul h.hDzg

/-! ## The `N₁`-block (rows 8--11) -/

theorem contDiffOn_four_N1gg {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N1gg α g Φg)) Q0 :=
  (contDiffOn_const.mul h.hRopTg).mul h.hg

theorem contDiffOn_four_N1gs {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N1gs α g Φg)) Q0 :=
  (contDiffOn_const.mul h.hRopTg).mul h.hF

theorem contDiffOn_four_N1sg {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N1sg α Φs g)) Q0 :=
  (contDiffOn_const.mul h.hRopTs).mul h.hg

theorem contDiffOn_four_N1ss {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N1ss α Φs)) Q0 :=
  (contDiffOn_const.mul h.hRopTs).mul h.hF

/-! ## The `N₂`-block (rows 12--15) -/

theorem contDiffOn_four_N2gg {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N2gg α g Φg)) Q0 :=
  (contDiffOn_const.mul h.hUopTg).mul h.hpthg

theorem contDiffOn_four_N2gs {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N2gs α g Φg)) Q0 :=
  (contDiffOn_const.mul h.hUopTg).mul h.hpthF

theorem contDiffOn_four_N2sg {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N2sg α Φs g)) Q0 :=
  (contDiffOn_const.mul h.hUopTs).mul h.hpthg

theorem contDiffOn_four_N2ss {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N2ss α Φs)) Q0 :=
  (contDiffOn_const.mul h.hUopTs).mul h.hpthF

/-! ## The `N₃`-block (rows 16--19) -/

theorem contDiffOn_four_N3gg {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N3gg α g Φg)) Q0 := by
  have h1 : ContDiffOn ℝ 4 (Function.uncurry (fun z θ =>
      -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
        * Work.Spaces.Dz g z θ)) Q0 :=
    ((contDiffOn_const (c := (-2) * α)).mul h.hVopTg).mul h.hDzg
  exact h1

theorem contDiffOn_four_N3gs {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N3gs α g Φg)) Q0 := by
  have h1 : ContDiffOn ℝ 4 (Function.uncurry (fun z θ =>
      -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTg α g Φg) z θ
        * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)) Q0 :=
    ((contDiffOn_const (c := (-2) * α)).mul h.hVopTg).mul h.hDzF
  exact h1

theorem contDiffOn_four_N3sg {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N3sg α Φs g)) Q0 := by
  have h1 : ContDiffOn ℝ 4 (Function.uncurry (fun z θ =>
      -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Spaces.Dz g z θ)) Q0 :=
    ((contDiffOn_const (c := (-2) * α)).mul h.hVopTs).mul h.hDzg
  exact h1

theorem contDiffOn_four_N3ss {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N3ss α Φs)) Q0 := by
  have h1 : ContDiffOn ℝ 4 (Function.uncurry (fun z θ =>
      -2 * α * Work.Construction.Vop (Work.FTS.Nonlin.PhiTs α Φs) z θ
        * Work.Spaces.Dz (Work.Construction.Fstar α) z θ)) Q0 :=
    ((contDiffOn_const (c := (-2) * α)).mul h.hVopTs).mul h.hDzF
  exact h1

/-! ## The `N₄`-block (rows 20--23) -/

theorem contDiffOn_four_N4gg {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N4gg α g)) Q0 :=
  (contDiffOn_const.mul h.hFKg).mul h.hDthg

theorem contDiffOn_four_N4gs {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N4gs α g)) Q0 :=
  ((contDiffOn_const.mul (contDiffOn_s2_Q0 4)).mul h.hFKg).mul h.hpthF

theorem contDiffOn_four_N4sg {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N4sg α g)) Q0 :=
  (contDiffOn_const.mul h.hFKF).mul h.hDthg

theorem contDiffOn_four_N4ss {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N4ss α)) Q0 :=
  ((contDiffOn_const.mul (contDiffOn_s2_Q0 4)).mul h.hFKF).mul h.hpthF

/-! ## The `N₅`-block (rows 24--26) -/

theorem contDiffOn_four_N5gg {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N5gg g)) Q0 :=
  (((contDiffOn_sin_sq_Q0 4).neg).mul h.hFKg).mul h.hg

theorem contDiffOn_four_N5gs {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N5gs α g)) Q0 :=
  (((contDiffOn_sin_sq_Q0 4).neg).mul h.hFKg).mul h.hF

theorem contDiffOn_four_N5sg {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N5sg α g)) Q0 :=
  (((contDiffOn_sin_sq_Q0 4).neg).mul h.hFKF).mul h.hg

theorem contDiffOn_four_N5ss {α : ℝ} {g Φs Φg : Fn} (h : FourFactors α g Φs Φg) :
    ContDiffOn ℝ 4 (Function.uncurry (Work.FTS.Nonlin.N5ss α)) Q0 :=
  (((contDiffOn_sin_sq_Q0 4).neg).mul h.hFKF).mul h.hF

end Work.FTS.OpenPkg
