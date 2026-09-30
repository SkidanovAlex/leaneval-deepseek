/-
# The ceiling identity of the cusp chart

The chart `Work.RTOwed.mbarLow v` of the cusp neighbourhood of `M̄` reduces the cube coordinate
`x_cube = x_cusp + h` (`h = (1/2,1/2,1/2)`) to the unit cube of its cube `a` and applies the Möbius
chart `chartKlein a` of that cube.  The truncation facet of the cube `a` is the hemisphere

  `ceilH a x = √(9/4 − ∑_i (x_i − corner_a i − 1/2)²)`,

the cube-coordinate form of the ceiling `β` of the cusp chapter (`Work.Cusp.beta`).  This file proves
the identities that make the cusp chart work:

* **`ceilH_chartRed`** — `ceilH (chartCube v q) (chartRed v q) = β (xOf q)`: the hemisphere of the
  cube of the reduced coordinate *is* the ceiling `β` of the cusp coordinate, so the region
  `q 3 ≤ β (xOf q)` of `CuspGlueData` is exactly the region `q 3 ≤ ceilH (chartCube v q) (chartRed v q)`
  of `mbarLow_eq`, where the junk branch of the chart is never taken;
* **`mbarLow_ceiling_eq_mbarPt`** — `mbarLow v (ceilingPt x) = mbarPt v (x + h)`: the chart at the
  ceiling is the ceiling map of the development (in the *cube* coordinate `x + h`).

Both follow from `Work.RTOwed.ceilH_eq_beta` (`ceilH a (y + h) = β y` for `y + h` in the cube of `a`),
the `ℤ³`-periodicity of `β` (`Work.Cusp.beta_add_int`) and the reduction identity
`redV v (x + h) = (x + h) − intVec L` of the development.

The file also fixes the concrete certificates `Work.RTOwed.cuspCertificates`, the concrete ceiling
data `Work.RTOwed.ceilingData : Work.RTOwed.CuspCeilingData` of the five cusps, the ceiling map
`Work.RTOwed.mbarPtC` in the cusp coordinates of the chart (with its two defining properties) and the
`Tset` membership lemmas that the fill/chart fields consume.
-/
import Mathlib
import Submission.Work.RTOwed.cuspChartRegion
import Submission.Work.RTOwed.ceilH_eq_beta
import Submission.Work.RTOwed.chartKlein_ceiling
import Submission.Work.RTOwed.chartKlein_strict
import Submission.Work.RTOwed.cuspCeilingData_exists
import Submission.Work.Cusp.beta_min_le

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped BigOperators

namespace Work.RTOwed

/-! ## Bridges between the coordinate conventions -/

/-- The horizontal part `xOf4` of this area is the `xOf` of the cusp chapter. -/
theorem xOf4_eq_xOf (q : CuspE4) : xOf4 q = Work.Cusp.xOf q := rfl

/-- The horizontal part of `mkE4 x s` is `x`. -/
@[simp] theorem xOf4_mkE4 (x : CuspE3) (s : ℝ) : xOf4 (mkE4 x s) = x := by
  apply PiLp.ext; intro i
  fin_cases i <;> rfl

/-- The cube coordinate of `mkE4 x s` is `x + h`. -/
@[simp] theorem uhsXj_mkE4 (x : CuspE3) (s : ℝ) : uhsXj (mkE4 x s) = x + cuspH := by
  apply PiLp.ext; intro i
  fin_cases i <;> rfl

/-- The height coordinate of `mkE4 x s` is `s`. -/
@[simp] theorem mkE4_three (x : CuspE3) (s : ℝ) : (mkE4 x s) 3 = s := rfl

/-- The integer vector of the reduction of `x + h` to its cube. -/
def redShift (v : Fin 5) (x : CuspE3) : Fin 3 → ℤ :=
  fun i => floorV (x + cuspH) i - Work.Cusp.cubeCorner (cubeOf v (x + cuspH)) i

/-- **The reduction identity**: the reduced coordinate of the cube coordinate `x + h`, shifted back
by `h`, is the cusp coordinate `x` modulo the lattice vector `redShift v x`. -/
theorem redV_sub_cuspH (v : Fin 5) (x : CuspE3) :
    redV v (x + cuspH) - cuspH = x + Work.Cusp.ofInt3 (fun i => -(redShift v x i)) := by
  rw [cuspCert.redV_eq_sub]
  apply PiLp.ext; intro i
  fin_cases i <;>
    simp only [redShift, uhsXj, xOf4, cuspCert.intVec, Work.Cusp.ofInt3, cuspH, PiLp.sub_apply,
      PiLp.add_apply, PiLp.toLp_apply, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
      Matrix.head_cons] <;>
    push_cast <;> ring

/-! ## The ceiling identity -/

/-- **The ceiling of the chart cube at the reduced coordinate is `β`.**  This is the identity which
turns the region condition `q 3 ≤ β (xOf q)` of `CuspGlueData` into the region condition
`q 3 ≤ ceilH (chartCube v q) (chartRed v q)` of `mbarLow_eq`. -/
theorem ceilH_chartRed (v : Fin 5) (q : CuspE4) :
    ceilH (chartCube v q) (chartRed v q) = Work.Cusp.beta (xOf4 q) := by
  have hmem : redV v (uhsXj q) ∈ cubeBox (cubeOf v (uhsXj q)) := redV_mem_cubeBox v _
  -- `ceilH a y = β (y − h)` on the cube of `a`
  have h1 : ceilH (cubeOf v (uhsXj q)) (redV v (uhsXj q))
      = Work.Cusp.beta (redV v (uhsXj q) - cuspH) := by
    have h := ceilH_eq_beta (cubeOf v (uhsXj q))
      (y := redV v (uhsXj q) - cuspH) (by rw [sub_add_cancel]; exact hmem)
    rwa [sub_add_cancel] at h
  -- `redV v (x + h) − h = x + ofInt3 (−L)`
  have h2 : redV v (uhsXj q) - cuspH = xOf4 q + Work.Cusp.ofInt3 (fun i => -(redShift v (xOf4 q) i)) := by
    simpa only [uhsXj] using redV_sub_cuspH v (xOf4 q)
  -- `β` is `ℤ³`-periodic
  have h3 : Work.Cusp.beta (xOf4 q + Work.Cusp.ofInt3 (fun i => -(redShift v (xOf4 q) i)))
      = Work.Cusp.beta (xOf4 q) := Work.Cusp.beta_add_int _ _
  calc ceilH (chartCube v q) (chartRed v q)
      = ceilH (cubeOf v (uhsXj q)) (redV v (uhsXj q)) := rfl
    _ = Work.Cusp.beta (redV v (uhsXj q) - cuspH) := h1
    _ = Work.Cusp.beta (xOf4 q) := by rw [h2, h3]

/-- **The ceiling identity, in the form used by the fields of `CuspGlueData`**: on the region
`q 3 ≤ β (xOf q)` the point lies below the ceiling of its chart cube. -/
theorem le_ceilH_chartRed {v : Fin 5} {q : CuspE4} (h : q 3 ≤ Work.Cusp.beta (xOf4 q)) :
    q 3 ≤ ceilH (chartCube v q) (chartRed v q) := by
  rwa [ceilH_chartRed]

/-- **The ceiling is at least `s₁`**: `β x ≥ √(3/2) = betaMin > 11/10 = s₁`, so every point of the
ceiling lies in the height window of the collar boxes and the junk branch of the chart is never
taken at the ceiling. -/
theorem s1_le_beta (x : CuspE3) : 11 / 10 ≤ Work.Cusp.beta x := by
  refine le_trans ?_ (Work.Cusp.beta_min_le x)
  rw [Work.Cusp.betaMin]
  rw [show (11 : ℝ) / 10 = Real.sqrt ((11 / 10) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
  exact Real.sqrt_le_sqrt (by norm_num)

/-! ## The chart on its region -/

/-- **The cusp chart on the region below the ceiling, in cusp coordinates**: for `11/10 ≤ q 3` and
`q 3 ≤ β (xOf q)` the junk branch of `mbarLow` is never taken, so the chart is the `mk` of the
explicit Möbius chart of its cube.  This is `mbarLow_eq` with the ceiling identity `ceilH_chartRed`
substituted — the form in which the fields of `CuspGlueData` are proved. -/
theorem mbarLow_eq_beta (v : Fin 5) {q : CuspE4} (hs1 : 11 / 10 ≤ q 3)
    (hs2 : q 3 ≤ Work.Cusp.beta (xOf4 q)) :
    mbarLow v q = Work.FoldInst.mk (cubeBit (chartCube v q),
      ⟨redChart v (chartCube v q) q,
        chartKlein_mem (chartCube v q) (redV_mem_cubeBox v (uhsXj q)) hs1
          (le_ceilH_chartRed hs2)⟩) :=
  mbarLow_eq v hs1 (le_ceilH_chartRed hs2)

/-- **The ceiling point of the chart is the ceiling map**: the chart of the hyperbolic piece at the
ceiling point over the cusp coordinate `x` is the ceiling map of the development at the *cube*
coordinate `x + h`. -/
theorem mbarLow_ceiling_eq_mbarPt (v : Fin 5) (x : CuspE3) :
    mbarLow v (mkE4 x (Work.Cusp.beta x)) = mbarPt v (x + cuspH) := by
  set a : Fin 48 := cubeOf v (x + cuspH) with ha
  have hz : redV v (x + cuspH) ∈ cubeBox a := redV_mem_cubeBox v _
  have hzQ : kleinPt a (redV v (x + cuspH)) ∈ Work.FoldInst.Qbar :=
    cuspCert.cube_quad.1 a _ hz
  -- the ceiling identity at the reduced coordinate
  have hceil : ceilH a (redV v (x + cuspH)) = Work.Cusp.beta x := by
    simpa only [chartCube, uhsXj_mkE4, xOf4_mkE4, chartRed] using
      ceilH_chartRed v (mkE4 x (Work.Cusp.beta x))
  -- the chart value at the ceiling is the affine facet point
  have hval : chartKlein a (mkE4 (redV v (x + cuspH)) (Work.Cusp.beta x))
      = kleinPt a (redV v (x + cuspH)) := by
    rw [← hceil]
    exact chartKlein_ceiling a hz
  -- the value of `cuspLowPt` at the ceiling
  have hlow : cuspLowPt v (mkE4 x (Work.Cusp.beta x))
      = xbarOf a (kleinPt a (redV v (x + cuspH))) hzQ := by
    rw [cuspLowPt]
    split_ifs with hh
    · refine Prod.ext ?_ (Subtype.ext ?_)
      · show cubeBit (cubeOf v (uhsXj (mkE4 x (Work.Cusp.beta x)))) = cubeBit a
        rw [uhsXj_mkE4]
      · show redChart v (cubeOf v (uhsXj (mkE4 x (Work.Cusp.beta x))))
            (mkE4 x (Work.Cusp.beta x)) = kleinPt a (redV v (x + cuspH))
        rw [redChart, uhsXj_mkE4, mkE4_three, hval]
    · exact absurd (by
        rw [redChart, uhsXj_mkE4, mkE4_three, hval]
        exact cuspCert.cube_quad.1 a _ hz) hh
  rw [mbarLow, hlow, mbarPt, cuspPtX_of_mem v (x + cuspH) hzQ]

/-! ## The five cusps: the concrete ceiling data -/

/-- **The ceiling data of the five cusps of `M̄`**, in the concrete form of the development: the
ceiling map is `Work.RTOwed.mbarPt`, the `τ_v` homeomorphism is the explicit coordinate form of
`cuspCeilingData_exists`, and the truncation set is the disjoint union of the five ceiling tori. -/
noncomputable def ceilingData : CuspCeilingData :=
  { mbarPt := mbarPt
    tauHomeo := fun v => tauHomeo cuspCertificates v
    tset_eq := tset_eq_iUnion cuspCertificates
    disjoint := cuspCertificates.disj }

/-- **The ceiling points lie on the truncation set** (in the cube coordinates of the development). -/
theorem mbarPt_mem_Tset' (v : Fin 5) (x : CuspE3) : mbarPt v x ∈ Work.FoldInst.Tset :=
  mbarPt_mem_Tset cuspCertificates v x

/-- **The ceiling map in the cusp coordinates of the chart**: `x ↦ mbarPt v (x + h)`, i.e. the
`mbarPt` field of `CuspGlueData`. -/
noncomputable def mbarPtC (v : Fin 5) (x : CuspE3) : Work.FoldInst.Mbar := mbarPt v (x + cuspH)

/-- **The ceiling points lie on the truncation set** (form of `CuspGlueData.ceiling_mem`). -/
theorem mbarPtC_mem (v : Fin 5) (x : CuspE3) : mbarPtC v x ∈ Work.FoldInst.Tset :=
  mbarPt_mem_Tset' v (x + cuspH)

/-- The ceiling map of `CuspGlueData` is the chart at the ceiling: the field `mbarPt_eq`. -/
theorem mbarPtC_eq (v : Fin 5) (x : CuspE3) :
    mbarPtC v x = mbarLow v (mkE4 x (Work.Cusp.beta x)) :=
  (mbarLow_ceiling_eq_mbarPt v x).symm

/-- The ceiling point of the chart at the cusp coordinate `x` lies on the truncation set. -/
theorem mbarLow_ceiling_mem (v : Fin 5) (x : CuspE3) :
    mbarLow v (mkE4 x (Work.Cusp.beta x)) ∈ Work.FoldInst.Tset := by
  rw [mbarLow_ceiling_eq_mbarPt]
  exact mbarPt_mem_Tset' v (x + cuspH)

/-- The ceiling map in the cusp coordinates of the chart is the ceiling map of the ceiling data
composed with the coordinate translation `x ↦ x + h`. -/
theorem mbarPtC_eq_ceilingData (v : Fin 5) (x : CuspE3) :
    mbarPtC v x = ceilingData.mbarPt v (x + cuspH) := rfl

end Work.RTOwed
