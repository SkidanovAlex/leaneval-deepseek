/-
# The filling atlas of `M̂`: the definitions of the two chart families

This file fixes the *vocabulary* of the filling atlas of `M̂` used by
`Work.RTOwed.fillCross_of_rigid`, so that the transition lemmas can be stated and proved in
separate files.

## The atlas

The filling charts of `M̂` are of two kinds, indexed by the pinning data produced by the three
cover lemmas `Work.RTOwed.jCollar_cover_fin`, `Work.RTOwed.jPolar_cover_fin` (junction pinning
data `Work.RTOwed.JPin`) and `Work.RTOwed.core_cover_fin` (the `w`-section boxes `W`):

* **junction charts** (`Work.RTOwed.jChartOf`): for a cusp `v` and a pin `P : JPin a v`, the chart
  whose source is the image of the box `P.box` under the coordinate inclusion
  `Work.RTOwed.jCoordM` and whose value is the *polar coordinate* `Θ_v` of the point
  (`Work.RTOwed.jChart_exists`).  Its metric layer is `ChartLayer.warped (fillProf v)`: the warped
  filling metric of the profile of `v`.  These charts cover the inner polar layer
  (`‖p‖∞ < 1/2`, `Work.Cusp.polarLayer`), the junction `‖p‖∞ = 1/2` and the collar layer
  (`‖p‖∞ ≥ 1/2`) of every filling piece;
* **core charts** (`Work.RTOwed.coreChartOf`): for a cusp `v` and an open `w`-section box `W`, the
  chart whose source is the image of the core box section `Work.Cusp.coreBoxSect W` under the core
  coordinate inclusion `Work.Cusp.coreCoordM` (`Work.Cusp.exists_coreChartM`).  Its metric layer is
  `ChartLayer.flat (fillProf v).h₀` (the Cartesian flat core metric).  These charts cover the core
  layer `‖p‖∞ < 1/12`.

## The filling profiles

The metric of the filling piece of the `v`-th cusp is the warped metric
`dr² + f(r)²dθ² + h(r)²|dw|²`, where the profile `f` is the identity `f r = r` on the core
`r ≤ 1/2` (matched with the flat Cartesian core charts by the polar-to-Cartesian change of
variables) and the hyperbolic rate `f r = C e^r` in the collar `r ≥ 3` (matched with the upper half
space metric of the collar by `Work.Cusp.polarToUHS`).  The constants are forced by the *coordinate*
identification `Work.Cusp.polarToUHS v` of the collar:

  `C_v = ‖σ_v‖ e^{-R₀} / (2π)`,   `D = e^{-R₀}`

(with `R₀ = 7/2` the lead's constant): with these constants `polarToUHS v` carries the warped
metric of the profile to the upper half space metric
(`Work.HypModel.polarToUHS_isometry`).  The numerical input `1 ≤ C_v` is constraint (ii) of the
blueprint (`Work.Space.Data.slope_norm_ge`).

## The cover data

`Work.RTOwed.jData` (resp. `Work.RTOwed.kData`) is the finite family of junction pins (resp. core
sections) obtained from the two (resp. one) cover lemmas, together with the resulting cover of the
three layers on `M̂` (`Work.RTOwed.jData_collar`, `Work.RTOwed.jData_polar`,
`Work.RTOwed.kData_core`).
-/
import Mathlib
import Submission.Work.RTOwed.FillCharts
import Submission.Work.RTOwed.CuspRigid
import Submission.Work.RTOwed.jChart_exists
import Submission.Work.RTOwed.CuspBridge
import Submission.Work.Cusp.ChartTop
import Submission.Work.Cusp.cover_univ_charts
import Submission.Work.Cusp.polarToUHS_ThetaPolar
import Submission.Work.Profiles.Main
import Submission.Work.Space.Data.slope_norm_ge
import Submission.Work.RTOwed.Instance

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped RealInnerProductSpace Real Topology Manifold

namespace Work.RTOwed

open Work.RTInstance

/-! ## The filling profiles of the five cusps -/

/-- **The cusp constant `C_v` of the filling profile of the `v`-th cusp**:
`C_v = ‖σ_v‖ e^{-R₀}/(2π)`.  It is the constant that makes the polar-to-upper-half-space map
`Work.Cusp.polarToUHS v` an isometry from the warped metric `dr² + (C eʳ)²dθ² + (D eʳ)²|dw|²` to the
upper half space metric, and it is `≥ 1` by constraint (ii) of the blueprint. -/
def fillC (v : Work.Space.Cusp) : ℝ :=
  ‖Work.Cusp.slope v‖ * Real.exp (-(Work.Cusp.R0)) / (2 * π)

/-- **The cusp constant `D` of the filling profile**: `D = e^{-R₀}`. -/
def fillD : ℝ := Real.exp (-(Work.Cusp.R0))

theorem fillD_pos : 0 < fillD := Real.exp_pos _

/-- **The norm of the slope is the square root of the data constant**:
`‖σ_v‖² = slopeNormSq v` (`Work.Space.Data.slopeNormSq`). -/
theorem cusp_slope_norm_sq (v : Work.Space.Cusp) :
    ‖Work.Cusp.slope v‖ ^ 2 = (Work.Space.slopeNormSq v : ℝ) := by
  rw [EuclideanSpace.norm_sq_eq]
  fin_cases v <;> norm_num [Work.Cusp.slope, Work.Cusp.kv, Work.Cusp.kappa, Work.Cusp.slopeB,
    Work.Cusp.slopeC, Work.Space.slopeNormSq, Fin.sum_univ_three, Real.norm_eq_abs, sq_abs]

/-- **Constraint (ii)**: `1 ≤ C_v`.  Indeed `‖σ_v‖² = slopeNormSq v ≥ (2π e^{R₀})²`
(`Work.Space.Data.slope_norm_ge`), so `‖σ_v‖ e^{-R₀} ≥ 2π`. -/
theorem one_le_fillC (v : Work.Space.Cusp) : 1 ≤ fillC v := by
  have hge := Work.Space.Data.slope_norm_ge v
  have hR0 : Work.Cusp.R0 = (7:ℝ)/2 := rfl
  have hsq : (2 * Real.pi * Real.exp (Work.Cusp.R0)) ^ 2 ≤ ‖Work.Cusp.slope v‖ ^ 2 := by
    rw [cusp_slope_norm_sq v, hR0]
    exact_mod_cast hge
  have hnorm : 2 * Real.pi * Real.exp (Work.Cusp.R0) ≤ ‖Work.Cusp.slope v‖ := by
    have h := Real.sqrt_le_sqrt hsq
    rwa [Real.sqrt_sq (by positivity), Real.sqrt_sq (norm_nonneg _)] at h
  rw [fillC, le_div_iff₀ (by positivity : (0:ℝ) < 2 * Real.pi), one_mul]
  have hexp : Real.exp (-(Work.Cusp.R0)) = (Real.exp (Work.Cusp.R0))⁻¹ := Real.exp_neg _
  rw [hexp, ← div_eq_mul_inv, le_div_iff₀ (Real.exp_pos _)]
  linarith

/-- **The filling profile of the `v`-th cusp**: the profile with the forced constants `C_v`, `D`
(`Work.Profiles.exists_fillProfile`). -/
noncomputable def fillProf (v : Work.Space.Cusp) : Work.Profiles.FillProfile :=
  Classical.choose (Work.Profiles.exists_fillProfile (fillC v) fillD (one_le_fillC v) fillD_pos)

theorem fillProf_C (v : Work.Space.Cusp) : (fillProf v).C = fillC v :=
  (Classical.choose_spec (Work.Profiles.exists_fillProfile (fillC v) fillD
    (one_le_fillC v) fillD_pos)).1

theorem fillProf_D (v : Work.Space.Cusp) : (fillProf v).D = fillD :=
  (Classical.choose_spec (Work.Profiles.exists_fillProfile (fillC v) fillD
    (one_le_fillC v) fillD_pos)).2

/-- **The profile of the `v`-th cusp has the hyperbolic rate in the collar**: `f r = C_v e^r` for
`r ≥ 3`. -/
theorem fillProf_f_cusp (v : Work.Space.Cusp) {r : ℝ} (hr : 3 ≤ r) :
    (fillProf v).f r = fillC v * Real.exp r := by
  rw [(fillProf v).f_cusp r hr, fillProf_C v]

/-- **The profile of the `v`-th cusp has the hyperbolic rate in the collar**: `h r = D e^r` for
`r ≥ 3`. -/
theorem fillProf_h_cusp (v : Work.Space.Cusp) {r : ℝ} (hr : 3 ≤ r) :
    (fillProf v).h r = fillD * Real.exp r := by
  rw [(fillProf v).h_cusp r hr, fillProf_D v]

/-- **The profile is flat in the core**: `f r = r` for `r ≤ 1/2`. -/
theorem fillProf_f_core (v : Work.Space.Cusp) {r : ℝ} (hr : r ≤ 1/2) :
    (fillProf v).f r = r := (fillProf v).f_core r hr

/-- **The profile is flat in the core**: `h r = h₀` for `r ≤ 1/2`. -/
theorem fillProf_h_core (v : Work.Space.Cusp) {r : ℝ} (hr : r ≤ 1/2) :
    (fillProf v).h r = (fillProf v).h₀ := (fillProf v).h_core r hr

/-- The core constant `h₀` of the profile of the `v`-th cusp is nonzero. -/
theorem fillProf_h₀_ne_zero (v : Work.Space.Cusp) : (fillProf v).h₀ ≠ 0 :=
  ne_of_gt (fillProf v).h₀_pos

/-- The cusp constant `C_v` is positive. -/
theorem fillC_pos (v : Work.Space.Cusp) : 0 < fillC v := lt_of_lt_of_le one_pos (one_le_fillC v)

/-! ## The metric layers of the three chart families -/

/-- **The metric layer of a polar (junction) chart of the `v`-th cusp**: the warped filling metric
of the profile, in the polar coordinates `(r,θ,w₁,w₂)` of the filling piece. -/
def jLayer (v : Work.Space.Cusp) : ChartLayer := ChartLayer.warped (fillProf v)

/-- **The upper half space margin of the collar charts**: `s₁ = 11/10`, the bottom of the height
window of the collar box (every height of a collar chart is `> s₁`). -/
def cδ : ℝ := 11 / 10

theorem cδ_pos : 0 < cδ := by norm_num [cδ]

/-- **The metric layer of a collar chart**: the upper half space metric with the margin `s₁`. -/
def cLayer : ChartLayer := ChartLayer.uhs cδ

/-- **The metric layer of a core chart of the `v`-th cusp**: the flat Cartesian core metric of the
core constant `h₀` of the profile. -/
def kLayer (v : Work.Space.Cusp) : ChartLayer := ChartLayer.flat (fillProf v).h₀

theorem pLayer_okAnywhere (v : Work.Space.Cusp) : (jLayer v).okAnywhere := trivial

theorem cLayer_okAnywhere : cLayer.okAnywhere := cδ_pos

theorem kLayer_okAnywhere (v : Work.Space.Cusp) : (kLayer v).okAnywhere :=
  fillProf_h₀_ne_zero v

/-- The polar layer is non-degenerate at every polar coordinate above the box floor. -/
theorem pLayer_ok (v : Work.Space.Cusp) {q : E4} (hq : 1/4 < q 0) : (jLayer v).ok q := hq

/-- The collar layer is non-degenerate at every height of the collar box. -/
theorem cLayer_ok {q : E4} (hq : cδ < q 3) : cLayer.ok q := ⟨cδ_pos, hq⟩

/-- The core layer is non-degenerate everywhere (`h₀ ≠ 0`). -/
theorem kLayer_ok (v : Work.Space.Cusp) (q : E4) : (kLayer v).ok q := fillProf_h₀_ne_zero v

/-! ## The cut radius `rMid` between the polar and the collar charts -/

/-- **The cut radius of the atlas**: `rMid = R₀ − log sTop`.  The polar charts of the atlas have
their radial coordinate `< rMid` and the collar charts have their filling part in radius `> rMid`
(the filling part of a collar box consists of the points above the ceiling `β x`, whose UHS height
is `< sTop`, and `r = R₀ − log s`): this splits the filling pieces cleanly between the two
families, with no overlap in the filling direction. -/
def rMid : ℝ := Work.Cusp.R0 - Real.log Work.Cusp.sTop

theorem exp_three_gt_two : (2 : ℝ) < Real.exp 3 := by
  have h1 : Real.exp (1:ℝ) < Real.exp 3 := Real.exp_lt_exp.mpr (by norm_num)
  linarith [Real.exp_one_gt_two]

theorem exp_half_ge_one : (1 : ℝ) ≤ Real.exp ((1:ℝ)/2) := Real.one_le_exp (by norm_num)

theorem rMid_lt_rJ : rMid < Work.Cusp.rJ := by
  have h1 : Real.exp ((1:ℝ)/2) < Work.Cusp.sTop := Work.Cusp.sJ_lt_sTop
  have h2 : Real.log (Real.exp ((1:ℝ)/2)) < Real.log Work.Cusp.sTop :=
    Real.log_lt_log (Real.exp_pos _) h1
  rw [Real.log_exp] at h2
  rw [rMid, Work.Cusp.rJ, Work.Cusp.R0]
  linarith

theorem log_sTop_lt_seven_halves : Real.log Work.Cusp.sTop < 7/2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num [Work.Cusp.sTop])]
  have h1 : Real.exp ((7:ℝ)/2) = Real.exp 3 * Real.exp ((1:ℝ)/2) := by
    rw [← Real.exp_add]; norm_num
  have h2 : (33:ℝ)/20 < 2 := by norm_num
  rw [show Work.Cusp.sTop = ((33:ℝ)/20) by rfl, h1]
  nlinarith [exp_three_gt_two, exp_half_ge_one, Real.exp_pos ((1:ℝ)/2)]

theorem log_sTop_lt_five_halves : Real.log Work.Cusp.sTop < 5/2 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num [Work.Cusp.sTop])]
  have h1 : Real.exp ((5:ℝ)/2) = Real.exp 2 * Real.exp ((1:ℝ)/2) := by
    rw [← Real.exp_add]; norm_num
  have h2 : (4:ℝ) < Real.exp 2 := by
    rw [show (2:ℝ) = (2:ℕ)*1 by norm_num, Real.exp_nat_mul]
    nlinarith [Real.exp_one_gt_two, Real.exp_pos (1:ℝ)]
  have h3 : (33:ℝ)/20 < 4 := by norm_num
  rw [show Work.Cusp.sTop = ((33:ℝ)/20) by rfl, h1]
  nlinarith [h2, exp_half_ge_one, Real.exp_pos ((1:ℝ)/2)]

theorem rMid_pos : 0 < rMid := by
  rw [rMid, Work.Cusp.R0]
  linarith [log_sTop_lt_seven_halves]

theorem rMid_gt_one : 1 < rMid := by
  rw [rMid, Work.Cusp.R0]
  linarith [log_sTop_lt_five_halves]

theorem rMid_lt_four : rMid < 4 := by
  have h := rMid_lt_rJ
  rw [Work.Cusp.rJ] at h; linarith

/-! ## The cut radius of the junction charts, the boxes, and the three chart families -/

/-- **The cut radius of the junction charts**: `61/20 = 3.05`.  It lies strictly between the
junction `r_J = 3` (which the junction charts must reach, since the polar coordinates are pinned to
`r < r_J` and the junction has `r = r_J`) and `R₀ − log (3/2) ≈ 3.0945` (above which the UHS
coordinate of a junction box point can fall below the ceiling `β`, i.e. the collar branch
`cuspCoordMTop` could return a point of the *chimney* of `M̄` rather than a point of the filling
piece).  With this cut every value of a junction chart lies in the filling piece of its cusp. -/
def rCut : ℝ := 61 / 20

theorem rCut_gt_rJ : Work.Cusp.rJ < rCut := by norm_num [rCut, Work.Cusp.rJ]

theorem log_three_halves_lt : Real.log (3/2 : ℝ) < 45 / 100 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  have h1 : ∑ i ∈ Finset.range 3, ((45:ℝ)/100) ^ i / (i.factorial : ℝ) ≤ Real.exp (45/100) :=
    Real.sum_le_exp_of_nonneg (by norm_num) 3
  have h3 : (1:ℝ) + 45/100 + (45/100)^2/2 ≤
      ∑ i ∈ Finset.range 3, ((45:ℝ)/100) ^ i / (i.factorial : ℝ) := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_one]
    norm_num
  linarith

theorem rCut_lt_R0_sub_log : rCut < Work.Cusp.R0 - Real.log (3/2) := by
  rw [rCut, Work.Cusp.R0]
  linarith [log_three_halves_lt]

theorem lt_betaMax : (3/2 : ℝ) = Work.Cusp.betaMax := rfl

/-- **The box of a junction chart with the radial cut `rCut`**: the box of the pinning data cut at
the radial coordinate `rCut`. -/
def jBoxR (a : Work.Space.Assembly) (v : Work.Space.Cusp) (P : JPin a v) : Set E4 :=
  jBox v P.cU P.k P.W P.kx P.δ ∩ {q : E4 | q 0 < rCut}

theorem isOpen_jBoxR (a : Work.Space.Assembly) (v : Work.Space.Cusp) (P : JPin a v) :
    IsOpen (jBoxR a v P) := by
  have h1 : IsOpen {q : E4 | q 0 < rCut} :=
    isOpen_lt (by fun_prop : Continuous fun q : E4 => q 0) continuous_const
  exact (isOpen_jBox v P.cU P.k P.W P.kx P.δ P.hW).inter h1

/-- **The junction chart of the `v`-th cusp with the pinning data `P`**: the chart whose value is
the polar coordinate `Θ_v` of the point, with the box `P.box` (`Work.RTOwed.jChart_exists`). -/
noncomputable def jChartOf (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) : OpenPartialHomeomorph a.Mhat E4 :=
  Classical.choose (jChart_exists a v (D v) P.cU P.k P.W P.kx P.δ P.hδ P.hW P.hsec)

theorem jChartOf_source (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) :
    (jChartOf a D v P).source = jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ''
      (Set.univ : Set {q : Work.Cusp.E4 // q ∈ jBox v P.cU P.k P.W P.kx P.δ}) :=
  (Classical.choose_spec (jChart_exists a v (D v) P.cU P.k P.W P.kx P.δ P.hδ P.hW P.hsec)).1

theorem jChartOf_target (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) :
    (jChartOf a D v P).target = P.box :=
  (Classical.choose_spec (jChart_exists a v (D v) P.cU P.k P.W P.kx P.δ P.hδ P.hW P.hsec)).2.1

theorem jChartOf_apply (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (q : Work.Cusp.E4) (hq : q ∈ P.box) :
    jChartOf a D v P (P.coordM (D v) ⟨q, hq⟩) = q :=
  (Classical.choose_spec (jChart_exists a v (D v) P.cU P.k P.W P.kx P.δ P.hδ P.hW P.hsec)).2.2 q hq

/-- **The junction chart of the atlas**: the junction chart cut at the radius `rCut`, so that its
source consists of points of the filling piece of `v` only. -/
noncomputable def jChart (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) : OpenPartialHomeomorph a.Mhat E4 :=
  (jChartOf a D v P).trans
    (OpenPartialHomeomorph.ofSet (jBoxR a v P) (isOpen_jBoxR a v P))

theorem jChart_source (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) :
    (jChart a D v P).source =
      jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ''
        {q : {q : Work.Cusp.E4 // q ∈ jBox v P.cU P.k P.W P.kx P.δ} |
          (q : Work.Cusp.E4) ∈ jBoxR a v P} := by
  obtain ⟨hsrc, -, hcoe⟩ := Classical.choose_spec
    (jChart_exists a v (D v) P.cU P.k P.W P.kx P.δ P.hδ P.hW P.hsec)
  rw [jChart, show jChartOf a D v P
      = Classical.choose (jChart_exists a v (D v) P.cU P.k P.W P.kx P.δ P.hδ P.hW P.hsec)
      from rfl, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.ofSet_source,
    show (Classical.choose (jChart_exists a v (D v) P.cU P.k P.W P.kx P.δ P.hδ P.hW P.hsec)).source
      = jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ''
        (Set.univ : Set {q : Work.Cusp.E4 // q ∈ jBox v P.cU P.k P.W P.kx P.δ})
      from hsrc]
  ext x
  constructor
  · rintro ⟨⟨q, -, rfl⟩, hx⟩
    refine ⟨q, ?_, rfl⟩
    rw [Set.mem_preimage] at hx
    have h1 : (Classical.choose (jChart_exists a v (D v) P.cU P.k P.W P.kx P.δ P.hδ P.hW P.hsec))
        (jCoordM a v (D v) P.cU P.k P.W P.kx P.δ q) = (q : Work.Cusp.E4) :=
      hcoe (q : Work.Cusp.E4) q.2
    rw [h1] at hx
    exact hx
  · rintro ⟨q, hq, rfl⟩
    refine ⟨⟨q, Set.mem_univ q, rfl⟩, ?_⟩
    rw [Set.mem_preimage]
    have h1 : (Classical.choose (jChart_exists a v (D v) P.cU P.k P.W P.kx P.δ P.hδ P.hW P.hsec))
        (jCoordM a v (D v) P.cU P.k P.W P.kx P.δ q) = (q : Work.Cusp.E4) :=
      hcoe (q : Work.Cusp.E4) q.2
    rw [h1]
    exact hq

theorem jChart_apply (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (q : Work.Cusp.E4) (hq : q ∈ jBoxR a v P) :
    jChart a D v P (jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hq.1⟩) = q := by
  obtain ⟨-, -, hcoe⟩ := Classical.choose_spec
    (jChart_exists a v (D v) P.cU P.k P.W P.kx P.δ P.hδ P.hW P.hsec)
  have h1 : (Classical.choose (jChart_exists a v (D v) P.cU P.k P.W P.kx P.δ P.hδ P.hW P.hsec))
      (jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hq.1⟩) = q := hcoe q hq.1
  rw [jChart, show jChartOf a D v P
      = Classical.choose (jChart_exists a v (D v) P.cU P.k P.W P.kx P.δ P.hδ P.hW P.hsec)
      from rfl, OpenPartialHomeomorph.trans_apply]
  show (OpenPartialHomeomorph.ofSet (jBoxR a v P) (isOpen_jBoxR a v P))
    ((Classical.choose (jChart_exists a v (D v) P.cU P.k P.W P.kx P.δ P.hδ P.hW P.hsec))
      (jCoordM a v (D v) P.cU P.k P.W P.kx P.δ ⟨q, hq.1⟩)) = q
  rw [h1]
  exact congrFun (OpenPartialHomeomorph.ofSet_apply _ _) q

/-- **The box of a collar chart of the atlas**: the unslabbed collar box cut at the top by the
junction height `s_J` (so that its filling part lies at radius `> 3`, where the warped metric of
the profile agrees with the upper half space metric). -/
def cBoxR (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) : Set E4 :=
  Work.Cusp.cuspBoxTop v c δ ∩ {q : E4 | q 3 < Work.Cusp.sJ}

theorem isOpen_cBoxR (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) :
    IsOpen (cBoxR v c δ) := by
  have h1 : IsOpen {q : E4 | q 3 < Work.Cusp.sJ} :=
    isOpen_lt (by fun_prop : Continuous fun q : E4 => q 3) continuous_const
  exact (Work.Cusp.isOpen_cuspBoxTop v c δ).inter h1

/-- **The collar chart of the `v`-th cusp** (`Work.Cusp.cuspChart`, the unslabbed family), whose
value is the UHS coordinate `q` of the point. -/
noncomputable def cChartOf (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    OpenPartialHomeomorph a.Mhat E4 :=
  @Work.Cusp.cuspChart a v (D v) c δ hδ hne

theorem cChartOf_source (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    (cChartOf a D v c δ hδ hne).source =
      Work.Cusp.cuspCoordMTop a v (D v) c δ ''
        (Set.univ : Set {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) := by
  show (@Work.Cusp.cuspChart a v (D v) c δ hδ hne).source = _
  rw [@Work.Cusp.cuspChart_source a v (D v) c δ hδ hne, Set.image_univ]

theorem cChartOf_target (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    (cChartOf a D v c δ hδ hne).target = Work.Cusp.cuspBoxTop v c δ :=
  @Work.Cusp.cuspChart_target a v (D v) c δ hδ hne

theorem cChartOf_apply (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    (q : Work.Cusp.E4) (hq : q ∈ Work.Cusp.cuspBoxTop v c δ) :
    cChartOf a D v c δ hδ hne (Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨q, hq⟩) = q :=
  @Work.Cusp.cuspChart_apply a v (D v) c δ hδ hne ⟨q, hq⟩

/-- **The collar chart of the atlas**: the collar chart cut at the top by the junction height `s_J`,
so that its filling part lies in radius `> 3`. -/
noncomputable def cChart (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    OpenPartialHomeomorph a.Mhat E4 :=
  (cChartOf a D v c δ hδ hne).trans
    (OpenPartialHomeomorph.ofSet (cBoxR v c δ) (isOpen_cBoxR v c δ))

theorem cChart_source (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) :
    (cChart a D v c δ hδ hne).source =
      Work.Cusp.cuspCoordMTop a v (D v) c δ ''
        {q : {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ} |
          (q : Work.Cusp.E4) ∈ cBoxR v c δ} := by
  rw [cChart, OpenPartialHomeomorph.trans_source, OpenPartialHomeomorph.ofSet_source,
    show (cChartOf a D v c δ hδ hne).source
      = Work.Cusp.cuspCoordMTop a v (D v) c δ ''
        (Set.univ : Set {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
      from cChartOf_source a D v c δ hδ hne]
  ext x
  constructor
  · rintro ⟨⟨q, -, rfl⟩, hx⟩
    refine ⟨q, ?_, rfl⟩
    rw [Set.mem_preimage] at hx
    have h1 : cChartOf a D v c δ hδ hne (Work.Cusp.cuspCoordMTop a v (D v) c δ q)
        = (q : Work.Cusp.E4) := cChartOf_apply a D v c δ hδ hne (q : Work.Cusp.E4) q.2
    rw [h1] at hx
    exact hx
  · rintro ⟨q, hq, rfl⟩
    refine ⟨⟨q, Set.mem_univ q, rfl⟩, ?_⟩
    rw [Set.mem_preimage]
    have h1 : cChartOf a D v c δ hδ hne (Work.Cusp.cuspCoordMTop a v (D v) c δ q)
        = (q : Work.Cusp.E4) := cChartOf_apply a D v c δ hδ hne (q : Work.Cusp.E4) q.2
    rw [h1]
    exact hq

theorem cChart_apply (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ})
    (q : Work.Cusp.E4) (hq : q ∈ Work.Cusp.cuspBoxTop v c δ) (hq' : q ∈ cBoxR v c δ) :
    cChart a D v c δ hδ hne (Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨q, hq⟩) = q := by
  have h1 : cChartOf a D v c δ hδ hne (Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨q, hq⟩) = q :=
    cChartOf_apply a D v c δ hδ hne q hq
  rw [cChart, OpenPartialHomeomorph.trans_apply]
  show (OpenPartialHomeomorph.ofSet (cBoxR v c δ) (isOpen_cBoxR v c δ))
    (cChartOf a D v c δ hδ hne (Work.Cusp.cuspCoordMTop a v (D v) c δ ⟨q, hq⟩)) = q
  rw [h1]
  exact congrFun (OpenPartialHomeomorph.ofSet_apply _ _) q

/-- **The core chart of the `v`-th cusp with the `w`-section box `W`**
(`Work.Cusp.exists_coreChartM`). -/
noncomputable def kChartOf (a : Work.Space.Assembly)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    OpenPartialHomeomorph a.Mhat E4 :=
  Classical.choose (Work.Cusp.exists_coreChartM a v (tor v) W hW hsec)

theorem kChartOf_source (a : Work.Space.Assembly)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    (kChartOf a tor v W hW hsec).source =
      Work.Cusp.coreCoordM a v (tor v) W ''
        (Set.univ : Set {q : Work.Cusp.E4 // q ∈ Work.Cusp.coreBoxSect W}) :=
  (Classical.choose_spec (Work.Cusp.exists_coreChartM a v (tor v) W hW hsec)).1

theorem kChartOf_target (a : Work.Space.Assembly)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    (kChartOf a tor v W hW hsec).target = Work.Cusp.coreBoxSect W :=
  (Classical.choose_spec (Work.Cusp.exists_coreChartM a v (tor v) W hW hsec)).2.1

theorem kChartOf_apply (a : Work.Space.Assembly)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    (q : Work.Cusp.E4) (hq : q ∈ Work.Cusp.coreBoxSect W) :
    kChartOf a tor v W hW hsec (Work.Cusp.coreCoordM a v (tor v) W ⟨q, hq⟩) = q :=
  (Classical.choose_spec (Work.Cusp.exists_coreChartM a v (tor v) W hW hsec)).2.2 q hq

/-! ## The transition maps of the pairs of the atlas, as functions on the value coordinates -/

/-- The transition of two junction charts of one cusp, as a function on the coordinate space. -/
noncomputable def jjTransMap (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P Q : JPin a v) : E4 → E4 :=
  fun q => jChart a D v Q ((jChart a D v P).symm q)

/-- The source of the transition of two junction charts of one cusp. -/
noncomputable def jjTransSrc (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P Q : JPin a v) : Set E4 :=
  ((jChart a D v P).symm ≫ₕ (jChart a D v Q)).source

/-- The transition from a junction chart to a collar chart of one cusp. -/
noncomputable def jcTransMap (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) : E4 → E4 :=
  fun q => cChart a D v c δ hδ hne ((jChart a D v P).symm q)

/-- The source of the transition from a junction chart to a collar chart. -/
noncomputable def jcTransSrc (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) : Set E4 :=
  ((jChart a D v P).symm ≫ₕ (cChart a D v c δ hδ hne)).source

/-- The transition from a collar chart to a junction chart of one cusp. -/
noncomputable def cjTransMap (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) : E4 → E4 :=
  fun q => jChart a D v P ((cChart a D v c δ hδ hne).symm q)

/-- The source of the transition from a collar chart to a junction chart. -/
noncomputable def cjTransSrc (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (P : JPin a v) (c : Work.Cusp.E3) (δ : ℝ) (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) : Set E4 :=
  ((cChart a D v c δ hδ hne).symm ≫ₕ (jChart a D v P)).source

/-- The transition from a junction chart to a core chart of one cusp. -/
noncomputable def jkTransMap (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (P : JPin a v) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    E4 → E4 :=
  fun q => kChartOf a tor v W hW hsec ((jChart a D v P).symm q)

/-- The source of the transition from a junction chart to a core chart. -/
noncomputable def jkTransSrc (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (P : JPin a v) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    Set E4 :=
  ((jChart a D v P).symm ≫ₕ (kChartOf a tor v W hW hsec)).source

/-- The transition of two core charts of one cusp. -/
noncomputable def kkTransMap (a : Work.Space.Assembly)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (W₁ W₂ : Set Work.Cusp.E2) (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    (hsec₁ : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W₁ → Work.Cusp.wOf v y' ∈ W₁ →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    (hsec₂ : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W₂ → Work.Cusp.wOf v y' ∈ W₂ →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    E4 → E4 :=
  fun q => kChartOf a tor v W₂ hW₂ hsec₂ ((kChartOf a tor v W₁ hW₁ hsec₁).symm q)

/-- The source of the transition of two core charts of one cusp. -/
noncomputable def kkTransSrc (a : Work.Space.Assembly)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (W₁ W₂ : Set Work.Cusp.E2) (hW₁ : IsOpen W₁) (hW₂ : IsOpen W₂)
    (hsec₁ : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W₁ → Work.Cusp.wOf v y' ∈ W₁ →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y')
    (hsec₂ : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W₂ → Work.Cusp.wOf v y' ∈ W₂ →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    Set E4 :=
  ((kChartOf a tor v W₁ hW₁ hsec₁).symm ≫ₕ (kChartOf a tor v W₂ hW₂ hsec₂)).source

/-- The transition of two collar charts, as a function on the coordinate space. -/
noncomputable def ccTransMap (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c₁ : Work.Cusp.E3) (δ₁ : ℝ) (hδ₁ : δ₁ ≤ 1/2)
    (hne₁ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁})
    (v' : Work.Space.Cusp) (c₂ : Work.Cusp.E3) (δ₂ : ℝ) (hδ₂ : δ₂ ≤ 1/2)
    (hne₂ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v' c₂ δ₂}) : E4 → E4 :=
  fun q => cChart a D v' c₂ δ₂ hδ₂ hne₂ ((cChart a D v c₁ δ₁ hδ₁ hne₁).symm q)

/-- The source of the transition of two collar charts. -/
noncomputable def ccTransSrc (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (v : Work.Space.Cusp) (c₁ : Work.Cusp.E3) (δ₁ : ℝ) (hδ₁ : δ₁ ≤ 1/2)
    (hne₁ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c₁ δ₁})
    (v' : Work.Space.Cusp) (c₂ : Work.Cusp.E3) (δ₂ : ℝ) (hδ₂ : δ₂ ≤ 1/2)
    (hne₂ : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v' c₂ δ₂}) : Set E4 :=
  ((cChart a D v c₁ δ₁ hδ₁ hne₁).symm ≫ₕ (cChart a D v' c₂ δ₂ hδ₂ hne₂)).source

/-- The transition from a transported fold chart to a collar chart. -/
noncomputable def foldCTransMap (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (i : Fin (foldDataOf g).nF) (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ)
    (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) : E4 → E4 :=
  fun q => cChart (Work.RTInstance.assemblyOf g) D v c δ hδ hne (((foldDataOf g).foldM i).symm q)

/-- The source of the transition from a transported fold chart to a collar chart. -/
noncomputable def foldCTransSrc (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (i : Fin (foldDataOf g).nF) (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ)
    (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) : Set E4 :=
  (((foldDataOf g).foldM i).symm ≫ₕ
    cChart (Work.RTInstance.assemblyOf g) D v c δ hδ hne).source

/-- The transition from a collar chart to a transported fold chart. -/
noncomputable def cFoldTransMap (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (i : Fin (foldDataOf g).nF) (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ)
    (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) : E4 → E4 :=
  fun q => (foldDataOf g).foldM i
    ((cChart (Work.RTInstance.assemblyOf g) D v c δ hδ hne).symm q)

/-- The source of the transition from a collar chart to a transported fold chart. -/
noncomputable def cFoldTransSrc (g : Work.RTInstance.GlueHomeo)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData (Work.RTInstance.assemblyOf g) v)
    (i : Fin (foldDataOf g).nF) (v : Work.Space.Cusp) (c : Work.Cusp.E3) (δ : ℝ)
    (hδ : δ ≤ 1/2)
    (hne : Nonempty {q : Work.Cusp.E4 // q ∈ Work.Cusp.cuspBoxTop v c δ}) : Set E4 :=
  ((cChart (Work.RTInstance.assemblyOf g) D v c δ hδ hne).symm ≫ₕ (foldDataOf g).foldM i).source

/-- **The transition of two charts of `M̂` is smooth and is an isometry of the two metric models**,
in the *coordinate* form: `mdl₁` is the model of the first chart, `mdl₂` that of the second, `t` the
transition as a function of the coordinate of the first chart and `S` its source.  This is exactly
the pair of conditions `FillData.fill_smooth`/`FillData.fill_iso` (resp. `CrossData.cross_smooth_fg`/
`cross_iso_fg`) for the pair, transported to the coordinate space. -/
def TransIso2 (mdl₁ mdl₂ : Work.RTInstance.E4 → (Work.RTInstance.E4 →L[ℝ] Work.RTInstance.E4
      →L[ℝ] ℝ)) (t : Work.RTInstance.E4 → Work.RTInstance.E4)
    (S : Set Work.RTInstance.E4) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) t S ∧
    ∀ ⦃q : Work.RTInstance.E4⦄, q ∈ S → ∀ u w : Work.RTInstance.E4,
      mdl₂ (t q) (fderiv ℝ t q u) (fderiv ℝ t q w) = mdl₁ q u w

/-- The transition from a core chart to a junction chart of one cusp. -/
noncomputable def kjTransMap (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (P : JPin a v) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    Work.RTInstance.E4 → Work.RTInstance.E4 :=
  fun q => jChart a D v P ((kChartOf a tor v W hW hsec).symm q)

/-- The source of the transition from a core chart to a junction chart. -/
noncomputable def kjTransSrc (a : Work.Space.Assembly)
    (D : ∀ v : Work.Space.Cusp, Work.Cusp.CuspGlueData a v)
    (tor : ∀ v : Work.Space.Cusp, a.Torus v ≃ₜ (Fin 2 → AddCircle (1 : ℝ)))
    (v : Work.Space.Cusp) (P : JPin a v) (W : Set Work.Cusp.E2) (hW : IsOpen W)
    (hsec : ∀ y y' : Work.Cusp.E2, Work.Cusp.wOf v y ∈ W → Work.Cusp.wOf v y' ∈ W →
      (∀ i, ((y i : ℝ) : AddCircle (1 : ℝ)) = ((y' i : ℝ) : AddCircle (1 : ℝ))) → y = y') :
    Set Work.RTInstance.E4 :=
  ((kChartOf a tor v W hW hsec).symm ≫ₕ (jChart a D v P)).source

end Work.RTOwed
