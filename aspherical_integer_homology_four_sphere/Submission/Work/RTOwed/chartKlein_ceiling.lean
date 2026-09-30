/-
# `chartKlein` at the ceiling of a cube

The chart `Work.RTOwed.chartKlein a q` of the cube `a` is the Möbius map
`kleinOfHyp ((chartMat a) *ᵥ hypOfUHS q)`; this file proves that, **on the ceiling
`q = (x, ceilH a x)` of the closed unit cube `cubeBox a`**, it is the affine map `kleinPt a x`
of the truncation facet of the cube:

  `chartKlein a (mkE4 x (ceilH a x)) = kleinPt a x`.

## The computation

Write `q = (x, s)` with `s = ceilH a x` and `R = ‖q‖² = x 0 ² + x 1 ² + x 2 ² + s ²`.  Since
`hypOfUHS q = (x 0/s, x 1/s, x 2/s, (R-1)/(2s), (R+1)/(2s))`, the `k`-th coordinate of
`(chartMat a) *ᵥ hypOfUHS q` is `chartNum a x s k / (2 * s)`, where `chartNum a x s k` is the
affine function of `(x, s²)` defined below.  The `1/(2s)` factors cancel in the quotient defining
`kleinOfHyp`, and on the ceiling `s² = 9/4 - ∑ j (x j - γ j)²` (`γ j = cubeCorner a j + 1/2`), so
`chartNum a · 4` is a positive rational *constant* `D a` and

  `chartNum a x s i = kleinPt a x i * chartNum a x s 4`   (`i : Fin 4`)

is an identity of affine functions of `x`; it is checked cube by cube below (48 finite
computations, `chartMat` and `cubeXToKlein` being the concrete generated data tables).

This is the "restriction of the chart to the ceiling is `cubeXToKlein a`" statement of
`Submission/Work/RTOwed/cuspChartData.lean`.
-/
import Mathlib
import Submission.Work.RTOwed.cuspChart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option linter.unusedSimpArgs false

noncomputable section

open scoped Matrix
open Set Topology Function

namespace Work.RTOwed

/-! ### The numerator of the Möbius chart -/

/-- **The Möbius numerator of the chart of the cube `a` at `(x, s)`**: the `k`-th coordinate of
`(chartMat a) *ᵥ hypOfUHS (mkE4 x s)` is `chartNum a x s k / (2 * s)`. -/
def chartNum (a : Fin 48) (x : CuspE3) (s : ℝ) (k : Fin 5) : ℝ :=
  2 * (((chartMat a) k 0 : ℝ) * x 0 + ((chartMat a) k 1 : ℝ) * x 1
       + ((chartMat a) k 2 : ℝ) * x 2)
  + (((chartMat a) k 3 + (chartMat a) k 4 : ℤ) : ℝ)
      * (x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + s ^ 2)
  + (((chartMat a) k 4 - (chartMat a) k 3 : ℤ) : ℝ)

/-- **The chart matrix of the cube `a` applied to the hyperboloid point of `q`.** -/
def MV (a : Fin 48) (q : CuspE4) : Fin 5 → ℝ :=
  (chartMat a).map (Int.castRingHom ℝ) *ᵥ Work.HypModel.hypOfUHS q

@[simp] lemma mkE4_apply_zero (x : CuspE3) (s : ℝ) : mkE4 x s 0 = x 0 := rfl
@[simp] lemma mkE4_apply_one (x : CuspE3) (s : ℝ) : mkE4 x s 1 = x 1 := rfl
@[simp] lemma mkE4_apply_two (x : CuspE3) (s : ℝ) : mkE4 x s 2 = x 2 := rfl
@[simp] lemma mkE4_apply_three (x : CuspE3) (s : ℝ) : mkE4 x s 3 = s := rfl

lemma norm_sq_mkE4 (x : CuspE3) (s : ℝ) :
    ‖mkE4 x s‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + s ^ 2 := by
  simp only [mkE4]
  rw [EuclideanSpace.norm_sq_eq]
  simp [Fin.sum_univ_four]

/-- **`chartNum` computes the Möbius chart**: multiplying the `k`-th coordinate of
`(chartMat a) *ᵥ hypOfUHS (mkE4 x s)` by `2 * s` gives `chartNum a x s k`. -/
theorem chartNum_spec (a : Fin 48) (x : CuspE3) (s : ℝ) (hs : s ≠ 0) (k : Fin 5) :
    2 * s * (MV a (mkE4 x s) k) = chartNum a x s k := by
  have hnorm : ‖mkE4 x s‖ ^ 2 = x 0 ^ 2 + x 1 ^ 2 + x 2 ^ 2 + s ^ 2 := norm_sq_mkE4 x s
  simp only [MV]
  rw [Matrix.mulVec, dotProduct, Fin.sum_univ_five]
  simp only [Matrix.map_apply]
  rw [Work.HypModel.hypOfUHS_apply_zero, Work.HypModel.hypOfUHS_apply_one,
      Work.HypModel.hypOfUHS_apply_two, Work.HypModel.hypOfUHS_apply_three,
      Work.HypModel.hypOfUHS_apply_four, hnorm]
  simp only [mkE4_apply_zero, mkE4_apply_one, mkE4_apply_two, mkE4_apply_three]
  rw [chartNum]
  field_simp
  simp only [Int.coe_castRingHom]
  push_cast
  ring

/-- Componentwise description of `chartKlein`: it is the quotient of the `i`-th by the fourth
coordinate of the Möbius image of `hypOfUHS q`. -/
theorem chartKlein_apply_zero (a : Fin 48) (q : CuspE4) :
    chartKlein a q 0 = (MV a q 4)⁻¹ * (MV a q 0) := by
  simp only [chartKlein, MV, Work.HypModel.kleinOfHyp_apply_zero]

theorem chartKlein_apply_one (a : Fin 48) (q : CuspE4) :
    chartKlein a q 1 = (MV a q 4)⁻¹ * (MV a q 1) := by
  simp only [chartKlein, MV, Work.HypModel.kleinOfHyp_apply_one]

theorem chartKlein_apply_two (a : Fin 48) (q : CuspE4) :
    chartKlein a q 2 = (MV a q 4)⁻¹ * (MV a q 2) := by
  simp only [chartKlein, MV, Work.HypModel.kleinOfHyp_apply_two]

theorem chartKlein_apply_three (a : Fin 48) (q : CuspE4) :
    chartKlein a q 3 = (MV a q 4)⁻¹ * (MV a q 3) := by
  simp only [chartKlein, MV, Work.HypModel.kleinOfHyp_apply_three]

theorem chartKlein_apply (a : Fin 48) (q : CuspE4) (i : Fin 4) :
    chartKlein a q i = (MV a q 4)⁻¹ * (MV a q (Fin.castSucc i)) := by
  fin_cases i
  · exact chartKlein_apply_zero a q
  · exact chartKlein_apply_one a q
  · exact chartKlein_apply_two a q
  · exact chartKlein_apply_three a q

/-- **The ceiling is at most `3/4` below `9/4`**: the squared distance of `x` to the centre
`cubeCorner a + (1/2,1/2,1/2)` of the cube is at most `3/4`. -/
lemma ceilH_arg_le (a : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) :
    ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1 / 2)) ^ 2 ≤ 3 / 4 := by
  have hb : ∀ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1 / 2)) ^ 2 ≤ (1 / 4 : ℝ) := by
    intro j
    obtain ⟨h1, h2⟩ := hx j
    nlinarith [sq_nonneg (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1 / 2))]
  have h := Finset.sum_le_sum (fun j (_ : j ∈ Finset.univ) => hb j)
  have hc : (∑ _j : Fin 3, (1 / 4 : ℝ)) = 3 / 4 := by norm_num [Fin.sum_univ_three]
  linarith [h, hc]

/-- **The square of the ceiling**: for `x` in the closed cube `a`, `ceilH a x` is the height of
the hemisphere of radius `3/2` over the cube. -/
theorem ceilH_sq (a : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) :
    (ceilH a x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1 / 2)) ^ 2 := by
  have hsum := ceilH_arg_le a hx
  rw [ceilH, Real.sq_sqrt (by linarith)]

/-- **The ceiling is positive** on the closed cube `a`. -/
theorem ceilH_pos (a : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) : 0 < ceilH a x := by
  have hsum := ceilH_arg_le a hx
  rw [ceilH]
  exact Real.sqrt_pos.mpr (by linarith)


/-! ### The finite checks of the ceiling identity, one per cube -/

private lemma cnum_id_0_0 (x : CuspE3)
    (hs2 : (ceilH 0 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 0 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 0 x (ceilH 0 x) 0 = kleinPt 0 x 0 * chartNum 0 x (ceilH 0 x) 4 := by
  have hM00 : chartMat 0 0 0 = -2 := by decide +kernel
  have hM01 : chartMat 0 0 1 = -2 := by decide +kernel
  have hM02 : chartMat 0 0 2 = -2 := by decide +kernel
  have hM03 : chartMat 0 0 3 = 1 := by decide +kernel
  have hM04 : chartMat 0 0 4 = 3 := by decide +kernel
  have hM40 : chartMat 0 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 0 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 0 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 0 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 0 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 0 0 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 0 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 0 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 0 0 = ((4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 0 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 0 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 0 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_0_1 (x : CuspE3)
    (hs2 : (ceilH 0 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 0 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 0 x (ceilH 0 x) 1 = kleinPt 0 x 1 * chartNum 0 x (ceilH 0 x) 4 := by
  have hM10 : chartMat 0 1 0 = -2 := by decide +kernel
  have hM11 : chartMat 0 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 0 1 2 = 0 := by decide +kernel
  have hM13 : chartMat 0 1 3 = -1 := by decide +kernel
  have hM14 : chartMat 0 1 4 = 1 := by decide +kernel
  have hM40 : chartMat 0 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 0 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 0 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 0 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 0 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 0 1 0 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 0 1 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 0 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 0 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 0 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 0 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_0_2 (x : CuspE3)
    (hs2 : (ceilH 0 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 0 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 0 x (ceilH 0 x) 2 = kleinPt 0 x 2 * chartNum 0 x (ceilH 0 x) 4 := by
  have hM20 : chartMat 0 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 0 2 1 = -2 := by decide +kernel
  have hM22 : chartMat 0 2 2 = 0 := by decide +kernel
  have hM23 : chartMat 0 2 3 = -1 := by decide +kernel
  have hM24 : chartMat 0 2 4 = 1 := by decide +kernel
  have hM40 : chartMat 0 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 0 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 0 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 0 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 0 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 0 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 0 2 1 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 0 2 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 0 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 0 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 0 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_0_3 (x : CuspE3)
    (hs2 : (ceilH 0 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 0 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 0 x (ceilH 0 x) 3 = kleinPt 0 x 3 * chartNum 0 x (ceilH 0 x) 4 := by
  have hM30 : chartMat 0 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 0 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 0 3 2 = -2 := by decide +kernel
  have hM33 : chartMat 0 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 0 3 4 = 1 := by decide +kernel
  have hM40 : chartMat 0 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 0 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 0 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 0 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 0 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 0 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 0 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 0 3 2 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 0 3 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 0 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 0 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 0 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_1_0 (x : CuspE3)
    (hs2 : (ceilH 1 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 1 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 1 x (ceilH 1 x) 0 = kleinPt 1 x 0 * chartNum 1 x (ceilH 1 x) 4 := by
  have hM00 : chartMat 1 0 0 = -2 := by decide +kernel
  have hM01 : chartMat 1 0 1 = 2 := by decide +kernel
  have hM02 : chartMat 1 0 2 = 2 := by decide +kernel
  have hM03 : chartMat 1 0 3 = -1 := by decide +kernel
  have hM04 : chartMat 1 0 4 = -3 := by decide +kernel
  have hM40 : chartMat 1 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 1 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 1 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 1 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 1 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 1 0 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 1 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 1 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 1 0 = ((-4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 1 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 1 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 1 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_1_1 (x : CuspE3)
    (hs2 : (ceilH 1 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 1 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 1 x (ceilH 1 x) 1 = kleinPt 1 x 1 * chartNum 1 x (ceilH 1 x) 4 := by
  have hM10 : chartMat 1 1 0 = 2 := by decide +kernel
  have hM11 : chartMat 1 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 1 1 2 = 0 := by decide +kernel
  have hM13 : chartMat 1 1 3 = -1 := by decide +kernel
  have hM14 : chartMat 1 1 4 = 1 := by decide +kernel
  have hM40 : chartMat 1 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 1 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 1 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 1 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 1 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 1 1 0 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 1 1 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 1 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 1 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 1 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 1 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_1_2 (x : CuspE3)
    (hs2 : (ceilH 1 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 1 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 1 x (ceilH 1 x) 2 = kleinPt 1 x 2 * chartNum 1 x (ceilH 1 x) 4 := by
  have hM20 : chartMat 1 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 1 2 1 = -2 := by decide +kernel
  have hM22 : chartMat 1 2 2 = 0 := by decide +kernel
  have hM23 : chartMat 1 2 3 = -1 := by decide +kernel
  have hM24 : chartMat 1 2 4 = 1 := by decide +kernel
  have hM40 : chartMat 1 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 1 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 1 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 1 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 1 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 1 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 1 2 1 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 1 2 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 1 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 1 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 1 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_1_3 (x : CuspE3)
    (hs2 : (ceilH 1 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 1 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 1 x (ceilH 1 x) 3 = kleinPt 1 x 3 * chartNum 1 x (ceilH 1 x) 4 := by
  have hM30 : chartMat 1 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 1 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 1 3 2 = -2 := by decide +kernel
  have hM33 : chartMat 1 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 1 3 4 = 1 := by decide +kernel
  have hM40 : chartMat 1 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 1 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 1 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 1 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 1 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 1 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 1 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 1 3 2 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 1 3 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 1 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 1 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 1 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_2_0 (x : CuspE3)
    (hs2 : (ceilH 2 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 2 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 2 x (ceilH 2 x) 0 = kleinPt 2 x 0 * chartNum 2 x (ceilH 2 x) 4 := by
  have hM00 : chartMat 2 0 0 = 2 := by decide +kernel
  have hM01 : chartMat 2 0 1 = 2 := by decide +kernel
  have hM02 : chartMat 2 0 2 = -2 := by decide +kernel
  have hM03 : chartMat 2 0 3 = -1 := by decide +kernel
  have hM04 : chartMat 2 0 4 = -3 := by decide +kernel
  have hM40 : chartMat 2 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 2 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 2 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 2 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 2 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 2 0 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 2 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 2 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 2 0 = ((-4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 2 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 2 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 2 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_2_1 (x : CuspE3)
    (hs2 : (ceilH 2 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 2 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 2 x (ceilH 2 x) 1 = kleinPt 2 x 1 * chartNum 2 x (ceilH 2 x) 4 := by
  have hM10 : chartMat 2 1 0 = 2 := by decide +kernel
  have hM11 : chartMat 2 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 2 1 2 = 0 := by decide +kernel
  have hM13 : chartMat 2 1 3 = 1 := by decide +kernel
  have hM14 : chartMat 2 1 4 = -1 := by decide +kernel
  have hM40 : chartMat 2 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 2 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 2 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 2 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 2 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 2 1 0 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 2 1 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 2 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 2 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 2 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 2 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_2_2 (x : CuspE3)
    (hs2 : (ceilH 2 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 2 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 2 x (ceilH 2 x) 2 = kleinPt 2 x 2 * chartNum 2 x (ceilH 2 x) 4 := by
  have hM20 : chartMat 2 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 2 2 1 = 2 := by decide +kernel
  have hM22 : chartMat 2 2 2 = 0 := by decide +kernel
  have hM23 : chartMat 2 2 3 = 1 := by decide +kernel
  have hM24 : chartMat 2 2 4 = -1 := by decide +kernel
  have hM40 : chartMat 2 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 2 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 2 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 2 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 2 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 2 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 2 2 1 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 2 2 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 2 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 2 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 2 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_2_3 (x : CuspE3)
    (hs2 : (ceilH 2 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 2 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 2 x (ceilH 2 x) 3 = kleinPt 2 x 3 * chartNum 2 x (ceilH 2 x) 4 := by
  have hM30 : chartMat 2 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 2 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 2 3 2 = -2 := by decide +kernel
  have hM33 : chartMat 2 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 2 3 4 = -1 := by decide +kernel
  have hM40 : chartMat 2 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 2 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 2 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 2 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 2 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 2 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 2 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 2 3 2 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 2 3 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 2 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 2 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 2 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_3_0 (x : CuspE3)
    (hs2 : (ceilH 3 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 3 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 3 x (ceilH 3 x) 0 = kleinPt 3 x 0 * chartNum 3 x (ceilH 3 x) 4 := by
  have hM00 : chartMat 3 0 0 = 2 := by decide +kernel
  have hM01 : chartMat 3 0 1 = -2 := by decide +kernel
  have hM02 : chartMat 3 0 2 = 2 := by decide +kernel
  have hM03 : chartMat 3 0 3 = 1 := by decide +kernel
  have hM04 : chartMat 3 0 4 = 3 := by decide +kernel
  have hM40 : chartMat 3 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 3 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 3 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 3 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 3 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 3 0 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 3 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 3 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 3 0 = ((4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 3 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 3 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 3 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_3_1 (x : CuspE3)
    (hs2 : (ceilH 3 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 3 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 3 x (ceilH 3 x) 1 = kleinPt 3 x 1 * chartNum 3 x (ceilH 3 x) 4 := by
  have hM10 : chartMat 3 1 0 = -2 := by decide +kernel
  have hM11 : chartMat 3 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 3 1 2 = 0 := by decide +kernel
  have hM13 : chartMat 3 1 3 = 1 := by decide +kernel
  have hM14 : chartMat 3 1 4 = -1 := by decide +kernel
  have hM40 : chartMat 3 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 3 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 3 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 3 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 3 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 3 1 0 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 3 1 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 3 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 3 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 3 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 3 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_3_2 (x : CuspE3)
    (hs2 : (ceilH 3 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 3 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 3 x (ceilH 3 x) 2 = kleinPt 3 x 2 * chartNum 3 x (ceilH 3 x) 4 := by
  have hM20 : chartMat 3 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 3 2 1 = 2 := by decide +kernel
  have hM22 : chartMat 3 2 2 = 0 := by decide +kernel
  have hM23 : chartMat 3 2 3 = 1 := by decide +kernel
  have hM24 : chartMat 3 2 4 = -1 := by decide +kernel
  have hM40 : chartMat 3 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 3 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 3 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 3 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 3 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 3 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 3 2 1 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 3 2 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 3 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 3 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 3 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_3_3 (x : CuspE3)
    (hs2 : (ceilH 3 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 3 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 3 x (ceilH 3 x) 3 = kleinPt 3 x 3 * chartNum 3 x (ceilH 3 x) 4 := by
  have hM30 : chartMat 3 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 3 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 3 3 2 = -2 := by decide +kernel
  have hM33 : chartMat 3 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 3 3 4 = -1 := by decide +kernel
  have hM40 : chartMat 3 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 3 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 3 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 3 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 3 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 3 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 3 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 3 3 2 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 3 3 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 3 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 3 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 3 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_4_0 (x : CuspE3)
    (hs2 : (ceilH 4 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 4 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 4 x (ceilH 4 x) 0 = kleinPt 4 x 0 * chartNum 4 x (ceilH 4 x) 4 := by
  have hM00 : chartMat 4 0 0 = -2 := by decide +kernel
  have hM01 : chartMat 4 0 1 = 0 := by decide +kernel
  have hM02 : chartMat 4 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 4 0 3 = -1 := by decide +kernel
  have hM04 : chartMat 4 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 4 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 4 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 4 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 4 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 4 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 4 0 0 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 4 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 4 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 4 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 4 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 4 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 4 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_4_1 (x : CuspE3)
    (hs2 : (ceilH 4 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 4 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 4 x (ceilH 4 x) 1 = kleinPt 4 x 1 * chartNum 4 x (ceilH 4 x) 4 := by
  have hM10 : chartMat 4 1 0 = -2 := by decide +kernel
  have hM11 : chartMat 4 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 4 1 2 = -2 := by decide +kernel
  have hM13 : chartMat 4 1 3 = 1 := by decide +kernel
  have hM14 : chartMat 4 1 4 = 3 := by decide +kernel
  have hM40 : chartMat 4 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 4 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 4 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 4 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 4 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 4 1 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 4 1 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 4 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 4 1 = ((4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 4 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 4 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 4 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_4_2 (x : CuspE3)
    (hs2 : (ceilH 4 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 4 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 4 x (ceilH 4 x) 2 = kleinPt 4 x 2 * chartNum 4 x (ceilH 4 x) 4 := by
  have hM20 : chartMat 4 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 4 2 1 = -2 := by decide +kernel
  have hM22 : chartMat 4 2 2 = 0 := by decide +kernel
  have hM23 : chartMat 4 2 3 = -1 := by decide +kernel
  have hM24 : chartMat 4 2 4 = 1 := by decide +kernel
  have hM40 : chartMat 4 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 4 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 4 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 4 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 4 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 4 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 4 2 1 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 4 2 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 4 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 4 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 4 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 4 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_4_3 (x : CuspE3)
    (hs2 : (ceilH 4 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 4 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 4 x (ceilH 4 x) 3 = kleinPt 4 x 3 * chartNum 4 x (ceilH 4 x) 4 := by
  have hM30 : chartMat 4 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 4 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 4 3 2 = -2 := by decide +kernel
  have hM33 : chartMat 4 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 4 3 4 = 1 := by decide +kernel
  have hM40 : chartMat 4 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 4 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 4 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 4 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 4 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 4 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 4 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 4 3 2 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 4 3 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 4 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 4 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 4 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_5_0 (x : CuspE3)
    (hs2 : (ceilH 5 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 5 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 5 x (ceilH 5 x) 0 = kleinPt 5 x 0 * chartNum 5 x (ceilH 5 x) 4 := by
  have hM00 : chartMat 5 0 0 = 2 := by decide +kernel
  have hM01 : chartMat 5 0 1 = 0 := by decide +kernel
  have hM02 : chartMat 5 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 5 0 3 = 1 := by decide +kernel
  have hM04 : chartMat 5 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 5 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 5 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 5 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 5 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 5 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 5 0 0 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 5 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 5 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 5 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 5 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 5 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 5 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_5_1 (x : CuspE3)
    (hs2 : (ceilH 5 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 5 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 5 x (ceilH 5 x) 1 = kleinPt 5 x 1 * chartNum 5 x (ceilH 5 x) 4 := by
  have hM10 : chartMat 5 1 0 = 2 := by decide +kernel
  have hM11 : chartMat 5 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 5 1 2 = 2 := by decide +kernel
  have hM13 : chartMat 5 1 3 = -1 := by decide +kernel
  have hM14 : chartMat 5 1 4 = -3 := by decide +kernel
  have hM40 : chartMat 5 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 5 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 5 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 5 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 5 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 5 1 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 5 1 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 5 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 5 1 = ((-4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 5 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 5 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 5 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_5_2 (x : CuspE3)
    (hs2 : (ceilH 5 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 5 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 5 x (ceilH 5 x) 2 = kleinPt 5 x 2 * chartNum 5 x (ceilH 5 x) 4 := by
  have hM20 : chartMat 5 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 5 2 1 = -2 := by decide +kernel
  have hM22 : chartMat 5 2 2 = 0 := by decide +kernel
  have hM23 : chartMat 5 2 3 = 1 := by decide +kernel
  have hM24 : chartMat 5 2 4 = -1 := by decide +kernel
  have hM40 : chartMat 5 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 5 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 5 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 5 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 5 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 5 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 5 2 1 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 5 2 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 5 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 5 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 5 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 5 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_5_3 (x : CuspE3)
    (hs2 : (ceilH 5 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 5 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 5 x (ceilH 5 x) 3 = kleinPt 5 x 3 * chartNum 5 x (ceilH 5 x) 4 := by
  have hM30 : chartMat 5 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 5 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 5 3 2 = 2 := by decide +kernel
  have hM33 : chartMat 5 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 5 3 4 = -1 := by decide +kernel
  have hM40 : chartMat 5 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 5 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 5 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 5 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 5 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 5 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 5 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 5 3 2 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 5 3 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 5 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 5 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 5 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_6_0 (x : CuspE3)
    (hs2 : (ceilH 6 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 6 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 6 x (ceilH 6 x) 0 = kleinPt 6 x 0 * chartNum 6 x (ceilH 6 x) 4 := by
  have hM00 : chartMat 6 0 0 = -2 := by decide +kernel
  have hM01 : chartMat 6 0 1 = 0 := by decide +kernel
  have hM02 : chartMat 6 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 6 0 3 = -1 := by decide +kernel
  have hM04 : chartMat 6 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 6 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 6 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 6 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 6 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 6 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 6 0 0 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 6 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 6 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 6 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 6 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 6 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 6 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_6_1 (x : CuspE3)
    (hs2 : (ceilH 6 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 6 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 6 x (ceilH 6 x) 1 = kleinPt 6 x 1 * chartNum 6 x (ceilH 6 x) 4 := by
  have hM10 : chartMat 6 1 0 = 2 := by decide +kernel
  have hM11 : chartMat 6 1 1 = 2 := by decide +kernel
  have hM12 : chartMat 6 1 2 = -2 := by decide +kernel
  have hM13 : chartMat 6 1 3 = -1 := by decide +kernel
  have hM14 : chartMat 6 1 4 = -3 := by decide +kernel
  have hM40 : chartMat 6 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 6 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 6 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 6 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 6 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 6 1 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 6 1 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 6 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 6 1 = ((-4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 6 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 6 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 6 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_6_2 (x : CuspE3)
    (hs2 : (ceilH 6 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 6 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 6 x (ceilH 6 x) 2 = kleinPt 6 x 2 * chartNum 6 x (ceilH 6 x) 4 := by
  have hM20 : chartMat 6 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 6 2 1 = -2 := by decide +kernel
  have hM22 : chartMat 6 2 2 = 0 := by decide +kernel
  have hM23 : chartMat 6 2 3 = -1 := by decide +kernel
  have hM24 : chartMat 6 2 4 = 1 := by decide +kernel
  have hM40 : chartMat 6 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 6 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 6 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 6 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 6 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 6 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 6 2 1 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 6 2 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 6 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 6 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 6 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 6 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_6_3 (x : CuspE3)
    (hs2 : (ceilH 6 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 6 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 6 x (ceilH 6 x) 3 = kleinPt 6 x 3 * chartNum 6 x (ceilH 6 x) 4 := by
  have hM30 : chartMat 6 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 6 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 6 3 2 = 2 := by decide +kernel
  have hM33 : chartMat 6 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 6 3 4 = 1 := by decide +kernel
  have hM40 : chartMat 6 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 6 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 6 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 6 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 6 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 6 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 6 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 6 3 2 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 6 3 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 6 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 6 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 6 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_7_0 (x : CuspE3)
    (hs2 : (ceilH 7 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 7 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 7 x (ceilH 7 x) 0 = kleinPt 7 x 0 * chartNum 7 x (ceilH 7 x) 4 := by
  have hM00 : chartMat 7 0 0 = 2 := by decide +kernel
  have hM01 : chartMat 7 0 1 = 0 := by decide +kernel
  have hM02 : chartMat 7 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 7 0 3 = 1 := by decide +kernel
  have hM04 : chartMat 7 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 7 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 7 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 7 4 2 = -6 := by decide +kernel
  have hM43 : chartMat 7 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 7 4 4 = 8 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 7 0 0 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 7 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 7 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 7 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 7 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 7 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 7 2 = 1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_7_1 (x : CuspE3)
    (hs2 : (ceilH 7 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 7 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 7 x (ceilH 7 x) 1 = kleinPt 7 x 1 * chartNum 7 x (ceilH 7 x) 4 := by
  have hM10 : chartMat 7 1 0 = -2 := by decide +kernel
  have hM11 : chartMat 7 1 1 = 2 := by decide +kernel
  have hM12 : chartMat 7 1 2 = -6 := by decide +kernel
  have hM13 : chartMat 7 1 3 = -3 := by decide +kernel
  have hM14 : chartMat 7 1 4 = 7 := by decide +kernel
  have hM40 : chartMat 7 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 7 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 7 4 2 = -6 := by decide +kernel
  have hM43 : chartMat 7 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 7 4 4 = 8 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 7 1 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 7 1 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 7 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 7 1 = ((4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 7 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 7 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 7 2 = 1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_7_2 (x : CuspE3)
    (hs2 : (ceilH 7 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 7 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 7 x (ceilH 7 x) 2 = kleinPt 7 x 2 * chartNum 7 x (ceilH 7 x) 4 := by
  have hM20 : chartMat 7 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 7 2 1 = -2 := by decide +kernel
  have hM22 : chartMat 7 2 2 = 0 := by decide +kernel
  have hM23 : chartMat 7 2 3 = 1 := by decide +kernel
  have hM24 : chartMat 7 2 4 = -1 := by decide +kernel
  have hM40 : chartMat 7 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 7 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 7 4 2 = -6 := by decide +kernel
  have hM43 : chartMat 7 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 7 4 4 = 8 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 7 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 7 2 1 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 7 2 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 7 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 7 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 7 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 7 2 = 1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_7_3 (x : CuspE3)
    (hs2 : (ceilH 7 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 7 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 7 x (ceilH 7 x) 3 = kleinPt 7 x 3 * chartNum 7 x (ceilH 7 x) 4 := by
  have hM30 : chartMat 7 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 7 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 7 3 2 = -2 := by decide +kernel
  have hM33 : chartMat 7 3 3 = -3 := by decide +kernel
  have hM34 : chartMat 7 3 4 = 3 := by decide +kernel
  have hM40 : chartMat 7 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 7 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 7 4 2 = -6 := by decide +kernel
  have hM43 : chartMat 7 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 7 4 4 = 8 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 7 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 7 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 7 3 2 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 7 3 = ((3 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 7 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 7 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 7 2 = 1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_8_0 (x : CuspE3)
    (hs2 : (ceilH 8 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 8 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 8 x (ceilH 8 x) 0 = kleinPt 8 x 0 * chartNum 8 x (ceilH 8 x) 4 := by
  have hM00 : chartMat 8 0 0 = -2 := by decide +kernel
  have hM01 : chartMat 8 0 1 = 0 := by decide +kernel
  have hM02 : chartMat 8 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 8 0 3 = -1 := by decide +kernel
  have hM04 : chartMat 8 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 8 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 8 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 8 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 8 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 8 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 8 0 0 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 8 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 8 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 8 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 8 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 8 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 8 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_8_1 (x : CuspE3)
    (hs2 : (ceilH 8 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 8 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 8 x (ceilH 8 x) 1 = kleinPt 8 x 1 * chartNum 8 x (ceilH 8 x) 4 := by
  have hM10 : chartMat 8 1 0 = 0 := by decide +kernel
  have hM11 : chartMat 8 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 8 1 2 = 0 := by decide +kernel
  have hM13 : chartMat 8 1 3 = -1 := by decide +kernel
  have hM14 : chartMat 8 1 4 = 1 := by decide +kernel
  have hM40 : chartMat 8 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 8 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 8 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 8 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 8 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 8 1 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 8 1 1 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 8 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 8 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 8 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 8 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 8 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_8_2 (x : CuspE3)
    (hs2 : (ceilH 8 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 8 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 8 x (ceilH 8 x) 2 = kleinPt 8 x 2 * chartNum 8 x (ceilH 8 x) 4 := by
  have hM20 : chartMat 8 2 0 = -2 := by decide +kernel
  have hM21 : chartMat 8 2 1 = -2 := by decide +kernel
  have hM22 : chartMat 8 2 2 = -2 := by decide +kernel
  have hM23 : chartMat 8 2 3 = 1 := by decide +kernel
  have hM24 : chartMat 8 2 4 = 3 := by decide +kernel
  have hM40 : chartMat 8 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 8 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 8 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 8 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 8 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 8 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 8 2 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 8 2 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 8 2 = ((4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 8 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 8 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 8 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_8_3 (x : CuspE3)
    (hs2 : (ceilH 8 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 8 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 8 x (ceilH 8 x) 3 = kleinPt 8 x 3 * chartNum 8 x (ceilH 8 x) 4 := by
  have hM30 : chartMat 8 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 8 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 8 3 2 = -2 := by decide +kernel
  have hM33 : chartMat 8 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 8 3 4 = 1 := by decide +kernel
  have hM40 : chartMat 8 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 8 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 8 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 8 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 8 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 8 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 8 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 8 3 2 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 8 3 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 8 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 8 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 8 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_9_0 (x : CuspE3)
    (hs2 : (ceilH 9 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 9 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 9 x (ceilH 9 x) 0 = kleinPt 9 x 0 * chartNum 9 x (ceilH 9 x) 4 := by
  have hM00 : chartMat 9 0 0 = 2 := by decide +kernel
  have hM01 : chartMat 9 0 1 = 0 := by decide +kernel
  have hM02 : chartMat 9 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 9 0 3 = -1 := by decide +kernel
  have hM04 : chartMat 9 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 9 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 9 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 9 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 9 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 9 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 9 0 0 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 9 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 9 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 9 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 9 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 9 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 9 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_9_1 (x : CuspE3)
    (hs2 : (ceilH 9 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 9 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 9 x (ceilH 9 x) 1 = kleinPt 9 x 1 * chartNum 9 x (ceilH 9 x) 4 := by
  have hM10 : chartMat 9 1 0 = 0 := by decide +kernel
  have hM11 : chartMat 9 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 9 1 2 = 0 := by decide +kernel
  have hM13 : chartMat 9 1 3 = -1 := by decide +kernel
  have hM14 : chartMat 9 1 4 = 1 := by decide +kernel
  have hM40 : chartMat 9 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 9 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 9 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 9 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 9 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 9 1 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 9 1 1 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 9 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 9 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 9 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 9 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 9 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_9_2 (x : CuspE3)
    (hs2 : (ceilH 9 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 9 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 9 x (ceilH 9 x) 2 = kleinPt 9 x 2 * chartNum 9 x (ceilH 9 x) 4 := by
  have hM20 : chartMat 9 2 0 = -2 := by decide +kernel
  have hM21 : chartMat 9 2 1 = 2 := by decide +kernel
  have hM22 : chartMat 9 2 2 = 2 := by decide +kernel
  have hM23 : chartMat 9 2 3 = -1 := by decide +kernel
  have hM24 : chartMat 9 2 4 = -3 := by decide +kernel
  have hM40 : chartMat 9 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 9 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 9 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 9 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 9 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 9 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 9 2 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 9 2 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 9 2 = ((-4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 9 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 9 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 9 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_9_3 (x : CuspE3)
    (hs2 : (ceilH 9 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 9 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 9 x (ceilH 9 x) 3 = kleinPt 9 x 3 * chartNum 9 x (ceilH 9 x) 4 := by
  have hM30 : chartMat 9 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 9 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 9 3 2 = -2 := by decide +kernel
  have hM33 : chartMat 9 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 9 3 4 = 1 := by decide +kernel
  have hM40 : chartMat 9 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 9 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 9 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 9 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 9 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 9 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 9 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 9 3 2 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 9 3 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 9 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 9 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 9 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_10_0 (x : CuspE3)
    (hs2 : (ceilH 10 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 10 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 10 x (ceilH 10 x) 0 = kleinPt 10 x 0 * chartNum 10 x (ceilH 10 x) 4 := by
  have hM00 : chartMat 10 0 0 = 2 := by decide +kernel
  have hM01 : chartMat 10 0 1 = 0 := by decide +kernel
  have hM02 : chartMat 10 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 10 0 3 = 1 := by decide +kernel
  have hM04 : chartMat 10 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 10 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 10 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 10 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 10 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 10 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 10 0 0 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 10 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 10 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 10 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 10 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 10 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 10 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_10_1 (x : CuspE3)
    (hs2 : (ceilH 10 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 10 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 10 x (ceilH 10 x) 1 = kleinPt 10 x 1 * chartNum 10 x (ceilH 10 x) 4 := by
  have hM10 : chartMat 10 1 0 = 0 := by decide +kernel
  have hM11 : chartMat 10 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 10 1 2 = 0 := by decide +kernel
  have hM13 : chartMat 10 1 3 = 1 := by decide +kernel
  have hM14 : chartMat 10 1 4 = -1 := by decide +kernel
  have hM40 : chartMat 10 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 10 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 10 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 10 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 10 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 10 1 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 10 1 1 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 10 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 10 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 10 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 10 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 10 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_10_2 (x : CuspE3)
    (hs2 : (ceilH 10 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 10 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 10 x (ceilH 10 x) 2 = kleinPt 10 x 2 * chartNum 10 x (ceilH 10 x) 4 := by
  have hM20 : chartMat 10 2 0 = 2 := by decide +kernel
  have hM21 : chartMat 10 2 1 = -2 := by decide +kernel
  have hM22 : chartMat 10 2 2 = 2 := by decide +kernel
  have hM23 : chartMat 10 2 3 = -1 := by decide +kernel
  have hM24 : chartMat 10 2 4 = -3 := by decide +kernel
  have hM40 : chartMat 10 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 10 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 10 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 10 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 10 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 10 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 10 2 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 10 2 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 10 2 = ((-4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 10 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 10 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 10 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_10_3 (x : CuspE3)
    (hs2 : (ceilH 10 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 10 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 10 x (ceilH 10 x) 3 = kleinPt 10 x 3 * chartNum 10 x (ceilH 10 x) 4 := by
  have hM30 : chartMat 10 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 10 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 10 3 2 = 2 := by decide +kernel
  have hM33 : chartMat 10 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 10 3 4 = -1 := by decide +kernel
  have hM40 : chartMat 10 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 10 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 10 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 10 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 10 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 10 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 10 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 10 3 2 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 10 3 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 10 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 10 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 10 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_11_0 (x : CuspE3)
    (hs2 : (ceilH 11 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 11 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 11 x (ceilH 11 x) 0 = kleinPt 11 x 0 * chartNum 11 x (ceilH 11 x) 4 := by
  have hM00 : chartMat 11 0 0 = -2 := by decide +kernel
  have hM01 : chartMat 11 0 1 = 0 := by decide +kernel
  have hM02 : chartMat 11 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 11 0 3 = 1 := by decide +kernel
  have hM04 : chartMat 11 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 11 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 11 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 11 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 11 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 11 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 11 0 0 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 11 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 11 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 11 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 11 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 11 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 11 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_11_1 (x : CuspE3)
    (hs2 : (ceilH 11 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 11 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 11 x (ceilH 11 x) 1 = kleinPt 11 x 1 * chartNum 11 x (ceilH 11 x) 4 := by
  have hM10 : chartMat 11 1 0 = 0 := by decide +kernel
  have hM11 : chartMat 11 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 11 1 2 = 0 := by decide +kernel
  have hM13 : chartMat 11 1 3 = 1 := by decide +kernel
  have hM14 : chartMat 11 1 4 = -1 := by decide +kernel
  have hM40 : chartMat 11 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 11 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 11 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 11 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 11 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 11 1 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 11 1 1 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 11 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 11 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 11 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 11 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 11 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_11_2 (x : CuspE3)
    (hs2 : (ceilH 11 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 11 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 11 x (ceilH 11 x) 2 = kleinPt 11 x 2 * chartNum 11 x (ceilH 11 x) 4 := by
  have hM20 : chartMat 11 2 0 = 2 := by decide +kernel
  have hM21 : chartMat 11 2 1 = 2 := by decide +kernel
  have hM22 : chartMat 11 2 2 = -2 := by decide +kernel
  have hM23 : chartMat 11 2 3 = 1 := by decide +kernel
  have hM24 : chartMat 11 2 4 = 3 := by decide +kernel
  have hM40 : chartMat 11 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 11 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 11 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 11 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 11 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 11 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 11 2 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 11 2 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 11 2 = ((4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 11 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 11 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 11 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_11_3 (x : CuspE3)
    (hs2 : (ceilH 11 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 11 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 11 x (ceilH 11 x) 3 = kleinPt 11 x 3 * chartNum 11 x (ceilH 11 x) 4 := by
  have hM30 : chartMat 11 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 11 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 11 3 2 = 2 := by decide +kernel
  have hM33 : chartMat 11 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 11 3 4 = -1 := by decide +kernel
  have hM40 : chartMat 11 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 11 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 11 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 11 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 11 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 11 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 11 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 11 3 2 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 11 3 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 11 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 11 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 11 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_12_0 (x : CuspE3)
    (hs2 : (ceilH 12 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 12 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 12 x (ceilH 12 x) 0 = kleinPt 12 x 0 * chartNum 12 x (ceilH 12 x) 4 := by
  have hM00 : chartMat 12 0 0 = -2 := by decide +kernel
  have hM01 : chartMat 12 0 1 = 0 := by decide +kernel
  have hM02 : chartMat 12 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 12 0 3 = -1 := by decide +kernel
  have hM04 : chartMat 12 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 12 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 12 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 12 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 12 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 12 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 12 0 0 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 12 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 12 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 12 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 12 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 12 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 12 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_12_1 (x : CuspE3)
    (hs2 : (ceilH 12 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 12 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 12 x (ceilH 12 x) 1 = kleinPt 12 x 1 * chartNum 12 x (ceilH 12 x) 4 := by
  have hM10 : chartMat 12 1 0 = 0 := by decide +kernel
  have hM11 : chartMat 12 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 12 1 2 = 0 := by decide +kernel
  have hM13 : chartMat 12 1 3 = -1 := by decide +kernel
  have hM14 : chartMat 12 1 4 = 1 := by decide +kernel
  have hM40 : chartMat 12 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 12 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 12 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 12 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 12 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 12 1 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 12 1 1 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 12 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 12 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 12 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 12 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 12 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_12_2 (x : CuspE3)
    (hs2 : (ceilH 12 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 12 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 12 x (ceilH 12 x) 2 = kleinPt 12 x 2 * chartNum 12 x (ceilH 12 x) 4 := by
  have hM20 : chartMat 12 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 12 2 1 = 0 := by decide +kernel
  have hM22 : chartMat 12 2 2 = -2 := by decide +kernel
  have hM23 : chartMat 12 2 3 = -1 := by decide +kernel
  have hM24 : chartMat 12 2 4 = 1 := by decide +kernel
  have hM40 : chartMat 12 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 12 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 12 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 12 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 12 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 12 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 12 2 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 12 2 2 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 12 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 12 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 12 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 12 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_12_3 (x : CuspE3)
    (hs2 : (ceilH 12 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 12 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 12 x (ceilH 12 x) 3 = kleinPt 12 x 3 * chartNum 12 x (ceilH 12 x) 4 := by
  have hM30 : chartMat 12 3 0 = -2 := by decide +kernel
  have hM31 : chartMat 12 3 1 = -2 := by decide +kernel
  have hM32 : chartMat 12 3 2 = -2 := by decide +kernel
  have hM33 : chartMat 12 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 12 3 4 = 3 := by decide +kernel
  have hM40 : chartMat 12 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 12 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 12 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 12 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 12 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 12 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 12 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 12 3 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 12 3 = ((4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 12 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 12 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 12 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_13_0 (x : CuspE3)
    (hs2 : (ceilH 13 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 13 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 13 x (ceilH 13 x) 0 = kleinPt 13 x 0 * chartNum 13 x (ceilH 13 x) 4 := by
  have hM00 : chartMat 13 0 0 = -2 := by decide +kernel
  have hM01 : chartMat 13 0 1 = 0 := by decide +kernel
  have hM02 : chartMat 13 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 13 0 3 = 1 := by decide +kernel
  have hM04 : chartMat 13 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 13 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 13 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 13 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 13 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 13 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 13 0 0 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 13 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 13 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 13 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 13 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 13 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 13 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_13_1 (x : CuspE3)
    (hs2 : (ceilH 13 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 13 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 13 x (ceilH 13 x) 1 = kleinPt 13 x 1 * chartNum 13 x (ceilH 13 x) 4 := by
  have hM10 : chartMat 13 1 0 = 0 := by decide +kernel
  have hM11 : chartMat 13 1 1 = 2 := by decide +kernel
  have hM12 : chartMat 13 1 2 = 0 := by decide +kernel
  have hM13 : chartMat 13 1 3 = 1 := by decide +kernel
  have hM14 : chartMat 13 1 4 = -1 := by decide +kernel
  have hM40 : chartMat 13 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 13 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 13 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 13 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 13 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 13 1 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 13 1 1 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 13 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 13 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 13 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 13 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 13 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_13_2 (x : CuspE3)
    (hs2 : (ceilH 13 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 13 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 13 x (ceilH 13 x) 2 = kleinPt 13 x 2 * chartNum 13 x (ceilH 13 x) 4 := by
  have hM20 : chartMat 13 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 13 2 1 = 0 := by decide +kernel
  have hM22 : chartMat 13 2 2 = 2 := by decide +kernel
  have hM23 : chartMat 13 2 3 = 1 := by decide +kernel
  have hM24 : chartMat 13 2 4 = -1 := by decide +kernel
  have hM40 : chartMat 13 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 13 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 13 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 13 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 13 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 13 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 13 2 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 13 2 2 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 13 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 13 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 13 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 13 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_13_3 (x : CuspE3)
    (hs2 : (ceilH 13 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 13 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 13 x (ceilH 13 x) 3 = kleinPt 13 x 3 * chartNum 13 x (ceilH 13 x) 4 := by
  have hM30 : chartMat 13 3 0 = -2 := by decide +kernel
  have hM31 : chartMat 13 3 1 = 2 := by decide +kernel
  have hM32 : chartMat 13 3 2 = 2 := by decide +kernel
  have hM33 : chartMat 13 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 13 3 4 = -3 := by decide +kernel
  have hM40 : chartMat 13 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 13 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 13 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 13 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 13 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 13 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 13 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 13 3 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 13 3 = ((-4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 13 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 13 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 13 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_14_0 (x : CuspE3)
    (hs2 : (ceilH 14 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 14 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 14 x (ceilH 14 x) 0 = kleinPt 14 x 0 * chartNum 14 x (ceilH 14 x) 4 := by
  have hM00 : chartMat 14 0 0 = -2 := by decide +kernel
  have hM01 : chartMat 14 0 1 = 0 := by decide +kernel
  have hM02 : chartMat 14 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 14 0 3 = -1 := by decide +kernel
  have hM04 : chartMat 14 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 14 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 14 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 14 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 14 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 14 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 14 0 0 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 14 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 14 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 14 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 14 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 14 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 14 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_14_1 (x : CuspE3)
    (hs2 : (ceilH 14 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 14 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 14 x (ceilH 14 x) 1 = kleinPt 14 x 1 * chartNum 14 x (ceilH 14 x) 4 := by
  have hM10 : chartMat 14 1 0 = 0 := by decide +kernel
  have hM11 : chartMat 14 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 14 1 2 = 0 := by decide +kernel
  have hM13 : chartMat 14 1 3 = -1 := by decide +kernel
  have hM14 : chartMat 14 1 4 = 1 := by decide +kernel
  have hM40 : chartMat 14 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 14 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 14 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 14 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 14 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 14 1 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 14 1 1 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 14 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 14 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 14 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 14 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 14 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_14_2 (x : CuspE3)
    (hs2 : (ceilH 14 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 14 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 14 x (ceilH 14 x) 2 = kleinPt 14 x 2 * chartNum 14 x (ceilH 14 x) 4 := by
  have hM20 : chartMat 14 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 14 2 1 = 0 := by decide +kernel
  have hM22 : chartMat 14 2 2 = 2 := by decide +kernel
  have hM23 : chartMat 14 2 3 = -1 := by decide +kernel
  have hM24 : chartMat 14 2 4 = 1 := by decide +kernel
  have hM40 : chartMat 14 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 14 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 14 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 14 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 14 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 14 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 14 2 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 14 2 2 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 14 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 14 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 14 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 14 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_14_3 (x : CuspE3)
    (hs2 : (ceilH 14 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 14 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 14 x (ceilH 14 x) 3 = kleinPt 14 x 3 * chartNum 14 x (ceilH 14 x) 4 := by
  have hM30 : chartMat 14 3 0 = 2 := by decide +kernel
  have hM31 : chartMat 14 3 1 = 2 := by decide +kernel
  have hM32 : chartMat 14 3 2 = -2 := by decide +kernel
  have hM33 : chartMat 14 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 14 3 4 = -3 := by decide +kernel
  have hM40 : chartMat 14 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 14 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 14 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 14 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 14 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 14 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 14 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 14 3 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 14 3 = ((-4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 14 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 14 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 14 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_15_0 (x : CuspE3)
    (hs2 : (ceilH 15 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 15 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 15 x (ceilH 15 x) 0 = kleinPt 15 x 0 * chartNum 15 x (ceilH 15 x) 4 := by
  have hM00 : chartMat 15 0 0 = -2 := by decide +kernel
  have hM01 : chartMat 15 0 1 = 0 := by decide +kernel
  have hM02 : chartMat 15 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 15 0 3 = 1 := by decide +kernel
  have hM04 : chartMat 15 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 15 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 15 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 15 4 2 = -6 := by decide +kernel
  have hM43 : chartMat 15 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 15 4 4 = 8 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 15 0 0 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 15 0 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 15 0 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 15 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 15 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 15 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 15 2 = 1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_15_1 (x : CuspE3)
    (hs2 : (ceilH 15 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 15 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 15 x (ceilH 15 x) 1 = kleinPt 15 x 1 * chartNum 15 x (ceilH 15 x) 4 := by
  have hM10 : chartMat 15 1 0 = 0 := by decide +kernel
  have hM11 : chartMat 15 1 1 = 2 := by decide +kernel
  have hM12 : chartMat 15 1 2 = 0 := by decide +kernel
  have hM13 : chartMat 15 1 3 = 1 := by decide +kernel
  have hM14 : chartMat 15 1 4 = -1 := by decide +kernel
  have hM40 : chartMat 15 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 15 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 15 4 2 = -6 := by decide +kernel
  have hM43 : chartMat 15 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 15 4 4 = 8 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 15 1 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 15 1 1 = ((2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 15 1 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 15 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 15 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 15 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 15 2 = 1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_15_2 (x : CuspE3)
    (hs2 : (ceilH 15 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 15 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 15 x (ceilH 15 x) 2 = kleinPt 15 x 2 * chartNum 15 x (ceilH 15 x) 4 := by
  have hM20 : chartMat 15 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 15 2 1 = 0 := by decide +kernel
  have hM22 : chartMat 15 2 2 = -2 := by decide +kernel
  have hM23 : chartMat 15 2 3 = -3 := by decide +kernel
  have hM24 : chartMat 15 2 4 = 3 := by decide +kernel
  have hM40 : chartMat 15 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 15 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 15 4 2 = -6 := by decide +kernel
  have hM43 : chartMat 15 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 15 4 4 = 8 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 15 2 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 15 2 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 15 2 2 = ((-2 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 15 2 = ((3 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 15 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 15 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 15 2 = 1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_15_3 (x : CuspE3)
    (hs2 : (ceilH 15 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 15 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 15 x (ceilH 15 x) 3 = kleinPt 15 x 3 * chartNum 15 x (ceilH 15 x) 4 := by
  have hM30 : chartMat 15 3 0 = 2 := by decide +kernel
  have hM31 : chartMat 15 3 1 = -2 := by decide +kernel
  have hM32 : chartMat 15 3 2 = -6 := by decide +kernel
  have hM33 : chartMat 15 3 3 = -3 := by decide +kernel
  have hM34 : chartMat 15 3 4 = 7 := by decide +kernel
  have hM40 : chartMat 15 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 15 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 15 4 2 = -6 := by decide +kernel
  have hM43 : chartMat 15 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 15 4 4 = 8 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 15 3 0 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 15 3 1 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 15 3 2 = ((0 : ℚ)/1) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 15 3 = ((4 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 15 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 15 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 15 2 = 1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_16_0 (x : CuspE3)
    (hs2 : (ceilH 16 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 16 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 16 x (ceilH 16 x) 0 = kleinPt 16 x 0 * chartNum 16 x (ceilH 16 x) 4 := by
  have hM00 : chartMat 16 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 16 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 16 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 16 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 16 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 16 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 16 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 16 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 16 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 16 4 4 = 2 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 16 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 16 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 16 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 16 0 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 16 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 16 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 16 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_16_1 (x : CuspE3)
    (hs2 : (ceilH 16 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 16 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 16 x (ceilH 16 x) 1 = kleinPt 16 x 1 * chartNum 16 x (ceilH 16 x) 4 := by
  have hM10 : chartMat 16 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 16 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 16 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 16 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 16 1 4 = -1 := by decide +kernel
  have hM40 : chartMat 16 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 16 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 16 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 16 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 16 4 4 = 2 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 16 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 16 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 16 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 16 1 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 16 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 16 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 16 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_16_2 (x : CuspE3)
    (hs2 : (ceilH 16 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 16 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 16 x (ceilH 16 x) 2 = kleinPt 16 x 2 * chartNum 16 x (ceilH 16 x) 4 := by
  have hM20 : chartMat 16 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 16 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 16 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 16 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 16 2 4 = -1 := by decide +kernel
  have hM40 : chartMat 16 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 16 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 16 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 16 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 16 4 4 = 2 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 16 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 16 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 16 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 16 2 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 16 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 16 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 16 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_16_3 (x : CuspE3)
    (hs2 : (ceilH 16 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 16 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 16 x (ceilH 16 x) 3 = kleinPt 16 x 3 * chartNum 16 x (ceilH 16 x) 4 := by
  have hM30 : chartMat 16 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 16 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 16 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 16 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 16 3 4 = 0 := by decide +kernel
  have hM40 : chartMat 16 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 16 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 16 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 16 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 16 4 4 = 2 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 16 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 16 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 16 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 16 3 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 16 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 16 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 16 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_17_0 (x : CuspE3)
    (hs2 : (ceilH 17 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 17 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 17 x (ceilH 17 x) 0 = kleinPt 17 x 0 * chartNum 17 x (ceilH 17 x) 4 := by
  have hM00 : chartMat 17 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 17 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 17 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 17 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 17 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 17 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 17 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 17 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 17 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 17 4 4 = 2 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 17 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 17 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 17 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 17 0 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 17 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 17 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 17 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_17_1 (x : CuspE3)
    (hs2 : (ceilH 17 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 17 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 17 x (ceilH 17 x) 1 = kleinPt 17 x 1 * chartNum 17 x (ceilH 17 x) 4 := by
  have hM10 : chartMat 17 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 17 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 17 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 17 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 17 1 4 = -1 := by decide +kernel
  have hM40 : chartMat 17 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 17 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 17 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 17 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 17 4 4 = 2 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 17 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 17 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 17 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 17 1 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 17 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 17 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 17 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_17_2 (x : CuspE3)
    (hs2 : (ceilH 17 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 17 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 17 x (ceilH 17 x) 2 = kleinPt 17 x 2 * chartNum 17 x (ceilH 17 x) 4 := by
  have hM20 : chartMat 17 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 17 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 17 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 17 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 17 2 4 = -1 := by decide +kernel
  have hM40 : chartMat 17 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 17 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 17 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 17 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 17 4 4 = 2 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 17 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 17 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 17 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 17 2 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 17 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 17 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 17 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_17_3 (x : CuspE3)
    (hs2 : (ceilH 17 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 17 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 17 x (ceilH 17 x) 3 = kleinPt 17 x 3 * chartNum 17 x (ceilH 17 x) 4 := by
  have hM30 : chartMat 17 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 17 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 17 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 17 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 17 3 4 = 0 := by decide +kernel
  have hM40 : chartMat 17 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 17 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 17 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 17 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 17 4 4 = 2 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 17 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 17 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 17 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 17 3 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 17 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 17 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 17 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_18_0 (x : CuspE3)
    (hs2 : (ceilH 18 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 18 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 18 x (ceilH 18 x) 0 = kleinPt 18 x 0 * chartNum 18 x (ceilH 18 x) 4 := by
  have hM00 : chartMat 18 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 18 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 18 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 18 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 18 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 18 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 18 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 18 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 18 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 18 4 4 = 2 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 18 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 18 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 18 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 18 0 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 18 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 18 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 18 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_18_1 (x : CuspE3)
    (hs2 : (ceilH 18 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 18 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 18 x (ceilH 18 x) 1 = kleinPt 18 x 1 * chartNum 18 x (ceilH 18 x) 4 := by
  have hM10 : chartMat 18 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 18 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 18 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 18 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 18 1 4 = -1 := by decide +kernel
  have hM40 : chartMat 18 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 18 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 18 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 18 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 18 4 4 = 2 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 18 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 18 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 18 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 18 1 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 18 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 18 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 18 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_18_2 (x : CuspE3)
    (hs2 : (ceilH 18 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 18 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 18 x (ceilH 18 x) 2 = kleinPt 18 x 2 * chartNum 18 x (ceilH 18 x) 4 := by
  have hM20 : chartMat 18 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 18 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 18 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 18 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 18 2 4 = 1 := by decide +kernel
  have hM40 : chartMat 18 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 18 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 18 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 18 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 18 4 4 = 2 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 18 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 18 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 18 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 18 2 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 18 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 18 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 18 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_18_3 (x : CuspE3)
    (hs2 : (ceilH 18 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 18 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 18 x (ceilH 18 x) 3 = kleinPt 18 x 3 * chartNum 18 x (ceilH 18 x) 4 := by
  have hM30 : chartMat 18 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 18 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 18 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 18 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 18 3 4 = 0 := by decide +kernel
  have hM40 : chartMat 18 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 18 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 18 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 18 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 18 4 4 = 2 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 18 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 18 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 18 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 18 3 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 18 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 18 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 18 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_19_0 (x : CuspE3)
    (hs2 : (ceilH 19 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 19 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 19 x (ceilH 19 x) 0 = kleinPt 19 x 0 * chartNum 19 x (ceilH 19 x) 4 := by
  have hM00 : chartMat 19 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 19 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 19 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 19 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 19 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 19 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 19 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 19 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 19 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 19 4 4 = 2 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 19 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 19 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 19 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 19 0 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 19 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 19 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 19 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_19_1 (x : CuspE3)
    (hs2 : (ceilH 19 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 19 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 19 x (ceilH 19 x) 1 = kleinPt 19 x 1 * chartNum 19 x (ceilH 19 x) 4 := by
  have hM10 : chartMat 19 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 19 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 19 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 19 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 19 1 4 = 1 := by decide +kernel
  have hM40 : chartMat 19 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 19 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 19 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 19 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 19 4 4 = 2 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 19 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 19 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 19 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 19 1 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 19 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 19 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 19 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_19_2 (x : CuspE3)
    (hs2 : (ceilH 19 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 19 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 19 x (ceilH 19 x) 2 = kleinPt 19 x 2 * chartNum 19 x (ceilH 19 x) 4 := by
  have hM20 : chartMat 19 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 19 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 19 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 19 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 19 2 4 = 1 := by decide +kernel
  have hM40 : chartMat 19 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 19 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 19 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 19 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 19 4 4 = 2 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 19 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 19 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 19 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 19 2 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 19 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 19 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 19 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_19_3 (x : CuspE3)
    (hs2 : (ceilH 19 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 19 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 19 x (ceilH 19 x) 3 = kleinPt 19 x 3 * chartNum 19 x (ceilH 19 x) 4 := by
  have hM30 : chartMat 19 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 19 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 19 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 19 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 19 3 4 = 0 := by decide +kernel
  have hM40 : chartMat 19 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 19 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 19 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 19 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 19 4 4 = 2 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 19 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 19 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 19 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 19 3 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 19 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 19 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 19 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_20_0 (x : CuspE3)
    (hs2 : (ceilH 20 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 20 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 20 x (ceilH 20 x) 0 = kleinPt 20 x 0 * chartNum 20 x (ceilH 20 x) 4 := by
  have hM00 : chartMat 20 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 20 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 20 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 20 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 20 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 20 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 20 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 20 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 20 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 20 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 20 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 20 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 20 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 20 0 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 20 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 20 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 20 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_20_1 (x : CuspE3)
    (hs2 : (ceilH 20 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 20 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 20 x (ceilH 20 x) 1 = kleinPt 20 x 1 * chartNum 20 x (ceilH 20 x) 4 := by
  have hM10 : chartMat 20 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 20 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 20 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 20 1 3 = -2 := by decide +kernel
  have hM14 : chartMat 20 1 4 = 3 := by decide +kernel
  have hM40 : chartMat 20 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 20 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 20 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 20 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 20 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 20 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 20 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 20 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 20 1 = ((9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 20 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 20 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 20 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_20_2 (x : CuspE3)
    (hs2 : (ceilH 20 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 20 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 20 x (ceilH 20 x) 2 = kleinPt 20 x 2 * chartNum 20 x (ceilH 20 x) 4 := by
  have hM20 : chartMat 20 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 20 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 20 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 20 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 20 2 4 = -1 := by decide +kernel
  have hM40 : chartMat 20 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 20 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 20 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 20 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 20 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 20 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 20 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 20 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 20 2 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 20 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 20 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 20 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_20_3 (x : CuspE3)
    (hs2 : (ceilH 20 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 20 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 20 x (ceilH 20 x) 3 = kleinPt 20 x 3 * chartNum 20 x (ceilH 20 x) 4 := by
  have hM30 : chartMat 20 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 20 3 1 = 2 := by decide +kernel
  have hM32 : chartMat 20 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 20 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 20 3 4 = -2 := by decide +kernel
  have hM40 : chartMat 20 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 20 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 20 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 20 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 20 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 20 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 20 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 20 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 20 3 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 20 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 20 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 20 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_21_0 (x : CuspE3)
    (hs2 : (ceilH 21 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 21 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 21 x (ceilH 21 x) 0 = kleinPt 21 x 0 * chartNum 21 x (ceilH 21 x) 4 := by
  have hM00 : chartMat 21 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 21 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 21 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 21 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 21 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 21 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 21 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 21 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 21 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 21 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 21 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 21 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 21 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 21 0 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 21 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 21 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 21 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_21_1 (x : CuspE3)
    (hs2 : (ceilH 21 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 21 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 21 x (ceilH 21 x) 1 = kleinPt 21 x 1 * chartNum 21 x (ceilH 21 x) 4 := by
  have hM10 : chartMat 21 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 21 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 21 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 21 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 21 1 4 = -1 := by decide +kernel
  have hM40 : chartMat 21 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 21 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 21 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 21 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 21 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 21 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 21 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 21 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 21 1 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 21 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 21 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 21 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_21_2 (x : CuspE3)
    (hs2 : (ceilH 21 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 21 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 21 x (ceilH 21 x) 2 = kleinPt 21 x 2 * chartNum 21 x (ceilH 21 x) 4 := by
  have hM20 : chartMat 21 2 0 = 2 := by decide +kernel
  have hM21 : chartMat 21 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 21 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 21 2 3 = 2 := by decide +kernel
  have hM24 : chartMat 21 2 4 = -3 := by decide +kernel
  have hM40 : chartMat 21 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 21 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 21 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 21 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 21 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 21 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 21 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 21 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 21 2 = ((-9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 21 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 21 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 21 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_21_3 (x : CuspE3)
    (hs2 : (ceilH 21 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 21 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 21 x (ceilH 21 x) 3 = kleinPt 21 x 3 * chartNum 21 x (ceilH 21 x) 4 := by
  have hM30 : chartMat 21 3 0 = -2 := by decide +kernel
  have hM31 : chartMat 21 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 21 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 21 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 21 3 4 = 2 := by decide +kernel
  have hM40 : chartMat 21 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 21 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 21 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 21 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 21 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 21 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 21 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 21 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 21 3 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 21 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 21 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 21 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_22_0 (x : CuspE3)
    (hs2 : (ceilH 22 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 22 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 22 x (ceilH 22 x) 0 = kleinPt 22 x 0 * chartNum 22 x (ceilH 22 x) 4 := by
  have hM00 : chartMat 22 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 22 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 22 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 22 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 22 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 22 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 22 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 22 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 22 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 22 4 4 = 2 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 22 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 22 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 22 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 22 0 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 22 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 22 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 22 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_22_1 (x : CuspE3)
    (hs2 : (ceilH 22 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 22 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 22 x (ceilH 22 x) 1 = kleinPt 22 x 1 * chartNum 22 x (ceilH 22 x) 4 := by
  have hM10 : chartMat 22 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 22 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 22 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 22 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 22 1 4 = -1 := by decide +kernel
  have hM40 : chartMat 22 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 22 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 22 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 22 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 22 4 4 = 2 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 22 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 22 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 22 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 22 1 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 22 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 22 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 22 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_22_2 (x : CuspE3)
    (hs2 : (ceilH 22 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 22 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 22 x (ceilH 22 x) 2 = kleinPt 22 x 2 * chartNum 22 x (ceilH 22 x) 4 := by
  have hM20 : chartMat 22 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 22 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 22 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 22 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 22 2 4 = 1 := by decide +kernel
  have hM40 : chartMat 22 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 22 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 22 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 22 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 22 4 4 = 2 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 22 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 22 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 22 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 22 2 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 22 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 22 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 22 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_22_3 (x : CuspE3)
    (hs2 : (ceilH 22 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 22 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 22 x (ceilH 22 x) 3 = kleinPt 22 x 3 * chartNum 22 x (ceilH 22 x) 4 := by
  have hM30 : chartMat 22 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 22 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 22 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 22 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 22 3 4 = 0 := by decide +kernel
  have hM40 : chartMat 22 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 22 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 22 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 22 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 22 4 4 = 2 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 22 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 22 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 22 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 22 3 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 22 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 22 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 22 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_23_0 (x : CuspE3)
    (hs2 : (ceilH 23 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 23 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 23 x (ceilH 23 x) 0 = kleinPt 23 x 0 * chartNum 23 x (ceilH 23 x) 4 := by
  have hM00 : chartMat 23 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 23 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 23 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 23 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 23 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 23 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 23 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 23 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 23 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 23 4 4 = 2 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 23 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 23 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 23 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 23 0 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 23 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 23 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 23 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_23_1 (x : CuspE3)
    (hs2 : (ceilH 23 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 23 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 23 x (ceilH 23 x) 1 = kleinPt 23 x 1 * chartNum 23 x (ceilH 23 x) 4 := by
  have hM10 : chartMat 23 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 23 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 23 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 23 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 23 1 4 = 1 := by decide +kernel
  have hM40 : chartMat 23 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 23 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 23 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 23 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 23 4 4 = 2 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 23 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 23 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 23 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 23 1 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 23 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 23 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 23 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_23_2 (x : CuspE3)
    (hs2 : (ceilH 23 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 23 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 23 x (ceilH 23 x) 2 = kleinPt 23 x 2 * chartNum 23 x (ceilH 23 x) 4 := by
  have hM20 : chartMat 23 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 23 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 23 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 23 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 23 2 4 = 1 := by decide +kernel
  have hM40 : chartMat 23 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 23 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 23 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 23 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 23 4 4 = 2 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 23 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 23 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 23 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 23 2 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 23 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 23 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 23 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_23_3 (x : CuspE3)
    (hs2 : (ceilH 23 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 23 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 23 x (ceilH 23 x) 3 = kleinPt 23 x 3 * chartNum 23 x (ceilH 23 x) 4 := by
  have hM30 : chartMat 23 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 23 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 23 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 23 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 23 3 4 = 0 := by decide +kernel
  have hM40 : chartMat 23 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 23 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 23 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 23 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 23 4 4 = 2 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 23 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 23 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 23 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 23 3 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 23 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 23 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 23 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_24_0 (x : CuspE3)
    (hs2 : (ceilH 24 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 24 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 24 x (ceilH 24 x) 0 = kleinPt 24 x 0 * chartNum 24 x (ceilH 24 x) 4 := by
  have hM00 : chartMat 24 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 24 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 24 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 24 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 24 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 24 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 24 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 24 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 24 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 24 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 24 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 24 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 24 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 24 0 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 24 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 24 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 24 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_24_1 (x : CuspE3)
    (hs2 : (ceilH 24 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 24 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 24 x (ceilH 24 x) 1 = kleinPt 24 x 1 * chartNum 24 x (ceilH 24 x) 4 := by
  have hM10 : chartMat 24 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 24 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 24 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 24 1 3 = -2 := by decide +kernel
  have hM14 : chartMat 24 1 4 = 3 := by decide +kernel
  have hM40 : chartMat 24 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 24 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 24 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 24 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 24 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 24 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 24 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 24 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 24 1 = ((9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 24 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 24 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 24 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_24_2 (x : CuspE3)
    (hs2 : (ceilH 24 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 24 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 24 x (ceilH 24 x) 2 = kleinPt 24 x 2 * chartNum 24 x (ceilH 24 x) 4 := by
  have hM20 : chartMat 24 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 24 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 24 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 24 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 24 2 4 = -1 := by decide +kernel
  have hM40 : chartMat 24 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 24 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 24 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 24 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 24 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 24 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 24 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 24 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 24 2 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 24 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 24 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 24 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_24_3 (x : CuspE3)
    (hs2 : (ceilH 24 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 24 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 24 x (ceilH 24 x) 3 = kleinPt 24 x 3 * chartNum 24 x (ceilH 24 x) 4 := by
  have hM30 : chartMat 24 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 24 3 1 = 2 := by decide +kernel
  have hM32 : chartMat 24 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 24 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 24 3 4 = -2 := by decide +kernel
  have hM40 : chartMat 24 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 24 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 24 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 24 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 24 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 24 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 24 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 24 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 24 3 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 24 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 24 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 24 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_25_0 (x : CuspE3)
    (hs2 : (ceilH 25 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 25 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 25 x (ceilH 25 x) 0 = kleinPt 25 x 0 * chartNum 25 x (ceilH 25 x) 4 := by
  have hM00 : chartMat 25 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 25 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 25 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 25 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 25 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 25 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 25 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 25 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 25 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 25 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 25 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 25 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 25 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 25 0 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 25 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 25 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 25 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_25_1 (x : CuspE3)
    (hs2 : (ceilH 25 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 25 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 25 x (ceilH 25 x) 1 = kleinPt 25 x 1 * chartNum 25 x (ceilH 25 x) 4 := by
  have hM10 : chartMat 25 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 25 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 25 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 25 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 25 1 4 = -1 := by decide +kernel
  have hM40 : chartMat 25 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 25 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 25 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 25 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 25 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 25 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 25 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 25 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 25 1 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 25 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 25 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 25 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_25_2 (x : CuspE3)
    (hs2 : (ceilH 25 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 25 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 25 x (ceilH 25 x) 2 = kleinPt 25 x 2 * chartNum 25 x (ceilH 25 x) 4 := by
  have hM20 : chartMat 25 2 0 = -2 := by decide +kernel
  have hM21 : chartMat 25 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 25 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 25 2 3 = 2 := by decide +kernel
  have hM24 : chartMat 25 2 4 = -3 := by decide +kernel
  have hM40 : chartMat 25 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 25 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 25 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 25 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 25 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 25 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 25 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 25 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 25 2 = ((-9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 25 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 25 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 25 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_25_3 (x : CuspE3)
    (hs2 : (ceilH 25 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 25 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 25 x (ceilH 25 x) 3 = kleinPt 25 x 3 * chartNum 25 x (ceilH 25 x) 4 := by
  have hM30 : chartMat 25 3 0 = 2 := by decide +kernel
  have hM31 : chartMat 25 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 25 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 25 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 25 3 4 = 2 := by decide +kernel
  have hM40 : chartMat 25 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 25 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 25 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 25 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 25 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 25 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 25 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 25 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 25 3 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 25 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 25 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 25 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_26_0 (x : CuspE3)
    (hs2 : (ceilH 26 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 26 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 26 x (ceilH 26 x) 0 = kleinPt 26 x 0 * chartNum 26 x (ceilH 26 x) 4 := by
  have hM00 : chartMat 26 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 26 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 26 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 26 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 26 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 26 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 26 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 26 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 26 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 26 4 4 = 2 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 26 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 26 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 26 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 26 0 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 26 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 26 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 26 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_26_1 (x : CuspE3)
    (hs2 : (ceilH 26 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 26 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 26 x (ceilH 26 x) 1 = kleinPt 26 x 1 * chartNum 26 x (ceilH 26 x) 4 := by
  have hM10 : chartMat 26 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 26 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 26 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 26 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 26 1 4 = 1 := by decide +kernel
  have hM40 : chartMat 26 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 26 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 26 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 26 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 26 4 4 = 2 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 26 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 26 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 26 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 26 1 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 26 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 26 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 26 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_26_2 (x : CuspE3)
    (hs2 : (ceilH 26 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 26 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 26 x (ceilH 26 x) 2 = kleinPt 26 x 2 * chartNum 26 x (ceilH 26 x) 4 := by
  have hM20 : chartMat 26 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 26 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 26 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 26 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 26 2 4 = -1 := by decide +kernel
  have hM40 : chartMat 26 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 26 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 26 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 26 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 26 4 4 = 2 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 26 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 26 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 26 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 26 2 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 26 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 26 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 26 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_26_3 (x : CuspE3)
    (hs2 : (ceilH 26 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 26 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 26 x (ceilH 26 x) 3 = kleinPt 26 x 3 * chartNum 26 x (ceilH 26 x) 4 := by
  have hM30 : chartMat 26 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 26 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 26 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 26 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 26 3 4 = 0 := by decide +kernel
  have hM40 : chartMat 26 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 26 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 26 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 26 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 26 4 4 = 2 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 26 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 26 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 26 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 26 3 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 26 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 26 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 26 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_27_0 (x : CuspE3)
    (hs2 : (ceilH 27 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 27 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 27 x (ceilH 27 x) 0 = kleinPt 27 x 0 * chartNum 27 x (ceilH 27 x) 4 := by
  have hM00 : chartMat 27 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 27 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 27 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 27 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 27 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 27 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 27 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 27 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 27 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 27 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 27 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 27 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 27 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 27 0 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 27 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 27 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 27 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_27_1 (x : CuspE3)
    (hs2 : (ceilH 27 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 27 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 27 x (ceilH 27 x) 1 = kleinPt 27 x 1 * chartNum 27 x (ceilH 27 x) 4 := by
  have hM10 : chartMat 27 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 27 1 1 = 2 := by decide +kernel
  have hM12 : chartMat 27 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 27 1 3 = -2 := by decide +kernel
  have hM14 : chartMat 27 1 4 = 3 := by decide +kernel
  have hM40 : chartMat 27 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 27 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 27 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 27 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 27 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 27 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 27 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 27 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 27 1 = ((9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 27 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 27 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 27 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_27_2 (x : CuspE3)
    (hs2 : (ceilH 27 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 27 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 27 x (ceilH 27 x) 2 = kleinPt 27 x 2 * chartNum 27 x (ceilH 27 x) 4 := by
  have hM20 : chartMat 27 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 27 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 27 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 27 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 27 2 4 = 1 := by decide +kernel
  have hM40 : chartMat 27 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 27 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 27 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 27 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 27 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 27 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 27 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 27 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 27 2 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 27 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 27 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 27 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_27_3 (x : CuspE3)
    (hs2 : (ceilH 27 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 27 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 27 x (ceilH 27 x) 3 = kleinPt 27 x 3 * chartNum 27 x (ceilH 27 x) 4 := by
  have hM30 : chartMat 27 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 27 3 1 = -2 := by decide +kernel
  have hM32 : chartMat 27 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 27 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 27 3 4 = -2 := by decide +kernel
  have hM40 : chartMat 27 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 27 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 27 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 27 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 27 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 27 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 27 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 27 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 27 3 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 27 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 27 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 27 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_28_0 (x : CuspE3)
    (hs2 : (ceilH 28 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 28 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 28 x (ceilH 28 x) 0 = kleinPt 28 x 0 * chartNum 28 x (ceilH 28 x) 4 := by
  have hM00 : chartMat 28 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 28 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 28 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 28 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 28 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 28 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 28 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 28 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 28 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 28 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 28 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 28 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 28 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 28 0 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 28 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 28 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 28 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_28_1 (x : CuspE3)
    (hs2 : (ceilH 28 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 28 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 28 x (ceilH 28 x) 1 = kleinPt 28 x 1 * chartNum 28 x (ceilH 28 x) 4 := by
  have hM10 : chartMat 28 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 28 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 28 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 28 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 28 1 4 = -1 := by decide +kernel
  have hM40 : chartMat 28 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 28 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 28 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 28 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 28 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 28 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 28 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 28 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 28 1 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 28 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 28 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 28 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_28_2 (x : CuspE3)
    (hs2 : (ceilH 28 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 28 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 28 x (ceilH 28 x) 2 = kleinPt 28 x 2 * chartNum 28 x (ceilH 28 x) 4 := by
  have hM20 : chartMat 28 2 0 = -2 := by decide +kernel
  have hM21 : chartMat 28 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 28 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 28 2 3 = -2 := by decide +kernel
  have hM24 : chartMat 28 2 4 = 3 := by decide +kernel
  have hM40 : chartMat 28 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 28 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 28 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 28 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 28 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 28 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 28 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 28 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 28 2 = ((9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 28 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 28 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 28 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_28_3 (x : CuspE3)
    (hs2 : (ceilH 28 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 28 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 28 x (ceilH 28 x) 3 = kleinPt 28 x 3 * chartNum 28 x (ceilH 28 x) 4 := by
  have hM30 : chartMat 28 3 0 = -2 := by decide +kernel
  have hM31 : chartMat 28 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 28 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 28 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 28 3 4 = 2 := by decide +kernel
  have hM40 : chartMat 28 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 28 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 28 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 28 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 28 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 28 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 28 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 28 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 28 3 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 28 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 28 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 28 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_29_0 (x : CuspE3)
    (hs2 : (ceilH 29 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 29 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 29 x (ceilH 29 x) 0 = kleinPt 29 x 0 * chartNum 29 x (ceilH 29 x) 4 := by
  have hM00 : chartMat 29 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 29 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 29 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 29 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 29 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 29 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 29 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 29 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 29 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 29 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 29 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 29 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 29 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 29 0 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 29 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 29 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 29 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_29_1 (x : CuspE3)
    (hs2 : (ceilH 29 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 29 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 29 x (ceilH 29 x) 1 = kleinPt 29 x 1 * chartNum 29 x (ceilH 29 x) 4 := by
  have hM10 : chartMat 29 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 29 1 1 = 2 := by decide +kernel
  have hM12 : chartMat 29 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 29 1 3 = 2 := by decide +kernel
  have hM14 : chartMat 29 1 4 = -3 := by decide +kernel
  have hM40 : chartMat 29 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 29 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 29 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 29 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 29 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 29 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 29 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 29 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 29 1 = ((-9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 29 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 29 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 29 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_29_2 (x : CuspE3)
    (hs2 : (ceilH 29 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 29 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 29 x (ceilH 29 x) 2 = kleinPt 29 x 2 * chartNum 29 x (ceilH 29 x) 4 := by
  have hM20 : chartMat 29 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 29 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 29 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 29 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 29 2 4 = 1 := by decide +kernel
  have hM40 : chartMat 29 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 29 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 29 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 29 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 29 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 29 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 29 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 29 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 29 2 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 29 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 29 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 29 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_29_3 (x : CuspE3)
    (hs2 : (ceilH 29 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 29 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 29 x (ceilH 29 x) 3 = kleinPt 29 x 3 * chartNum 29 x (ceilH 29 x) 4 := by
  have hM30 : chartMat 29 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 29 3 1 = -2 := by decide +kernel
  have hM32 : chartMat 29 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 29 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 29 3 4 = 2 := by decide +kernel
  have hM40 : chartMat 29 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 29 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 29 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 29 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 29 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 29 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 29 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 29 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 29 3 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 29 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 29 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 29 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_30_0 (x : CuspE3)
    (hs2 : (ceilH 30 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 30 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 30 x (ceilH 30 x) 0 = kleinPt 30 x 0 * chartNum 30 x (ceilH 30 x) 4 := by
  have hM00 : chartMat 30 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 30 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 30 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 30 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 30 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 30 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 30 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 30 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 30 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 30 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 30 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 30 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 30 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 30 0 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 30 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 30 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 30 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_30_1 (x : CuspE3)
    (hs2 : (ceilH 30 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 30 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 30 x (ceilH 30 x) 1 = kleinPt 30 x 1 * chartNum 30 x (ceilH 30 x) 4 := by
  have hM10 : chartMat 30 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 30 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 30 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 30 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 30 1 4 = 1 := by decide +kernel
  have hM40 : chartMat 30 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 30 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 30 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 30 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 30 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 30 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 30 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 30 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 30 1 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 30 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 30 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 30 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_30_2 (x : CuspE3)
    (hs2 : (ceilH 30 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 30 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 30 x (ceilH 30 x) 2 = kleinPt 30 x 2 * chartNum 30 x (ceilH 30 x) 4 := by
  have hM20 : chartMat 30 2 0 = -2 := by decide +kernel
  have hM21 : chartMat 30 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 30 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 30 2 3 = -2 := by decide +kernel
  have hM24 : chartMat 30 2 4 = 3 := by decide +kernel
  have hM40 : chartMat 30 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 30 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 30 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 30 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 30 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 30 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 30 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 30 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 30 2 = ((9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 30 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 30 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 30 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_30_3 (x : CuspE3)
    (hs2 : (ceilH 30 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 30 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 30 x (ceilH 30 x) 3 = kleinPt 30 x 3 * chartNum 30 x (ceilH 30 x) 4 := by
  have hM30 : chartMat 30 3 0 = 2 := by decide +kernel
  have hM31 : chartMat 30 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 30 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 30 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 30 3 4 = -2 := by decide +kernel
  have hM40 : chartMat 30 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 30 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 30 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 30 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 30 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 30 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 30 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 30 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 30 3 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 30 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 30 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 30 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_31_0 (x : CuspE3)
    (hs2 : (ceilH 31 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 31 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 31 x (ceilH 31 x) 0 = kleinPt 31 x 0 * chartNum 31 x (ceilH 31 x) 4 := by
  have hM00 : chartMat 31 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 31 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 31 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 31 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 31 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 31 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 31 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 31 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 31 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 31 4 4 = 6 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 31 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 31 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 31 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 31 0 = ((3 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 31 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 31 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 31 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_31_1 (x : CuspE3)
    (hs2 : (ceilH 31 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 31 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 31 x (ceilH 31 x) 1 = kleinPt 31 x 1 * chartNum 31 x (ceilH 31 x) 4 := by
  have hM10 : chartMat 31 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 31 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 31 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 31 1 3 = -2 := by decide +kernel
  have hM14 : chartMat 31 1 4 = 3 := by decide +kernel
  have hM40 : chartMat 31 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 31 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 31 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 31 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 31 4 4 = 6 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 31 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 31 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 31 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 31 1 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 31 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 31 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 31 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_31_2 (x : CuspE3)
    (hs2 : (ceilH 31 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 31 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 31 x (ceilH 31 x) 2 = kleinPt 31 x 2 * chartNum 31 x (ceilH 31 x) 4 := by
  have hM20 : chartMat 31 2 0 = 2 := by decide +kernel
  have hM21 : chartMat 31 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 31 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 31 2 3 = 2 := by decide +kernel
  have hM24 : chartMat 31 2 4 = -3 := by decide +kernel
  have hM40 : chartMat 31 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 31 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 31 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 31 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 31 4 4 = 6 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 31 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 31 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 31 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 31 2 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 31 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 31 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 31 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_31_3 (x : CuspE3)
    (hs2 : (ceilH 31 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 31 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 31 x (ceilH 31 x) 3 = kleinPt 31 x 3 * chartNum 31 x (ceilH 31 x) 4 := by
  have hM30 : chartMat 31 3 0 = -2 := by decide +kernel
  have hM31 : chartMat 31 3 1 = -2 := by decide +kernel
  have hM32 : chartMat 31 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 31 3 3 = -3 := by decide +kernel
  have hM34 : chartMat 31 3 4 = 4 := by decide +kernel
  have hM40 : chartMat 31 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 31 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 31 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 31 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 31 4 4 = 6 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 31 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 31 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 31 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 31 3 = ((9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 31 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 31 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 31 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_32_0 (x : CuspE3)
    (hs2 : (ceilH 32 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 32 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 32 x (ceilH 32 x) 0 = kleinPt 32 x 0 * chartNum 32 x (ceilH 32 x) 4 := by
  have hM00 : chartMat 32 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 32 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 32 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 32 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 32 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 32 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 32 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 32 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 32 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 32 4 4 = 2 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 32 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 32 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 32 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 32 0 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 32 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 32 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 32 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_32_1 (x : CuspE3)
    (hs2 : (ceilH 32 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 32 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 32 x (ceilH 32 x) 1 = kleinPt 32 x 1 * chartNum 32 x (ceilH 32 x) 4 := by
  have hM10 : chartMat 32 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 32 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 32 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 32 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 32 1 4 = 1 := by decide +kernel
  have hM40 : chartMat 32 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 32 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 32 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 32 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 32 4 4 = 2 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 32 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 32 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 32 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 32 1 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 32 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 32 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 32 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_32_2 (x : CuspE3)
    (hs2 : (ceilH 32 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 32 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 32 x (ceilH 32 x) 2 = kleinPt 32 x 2 * chartNum 32 x (ceilH 32 x) 4 := by
  have hM20 : chartMat 32 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 32 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 32 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 32 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 32 2 4 = -1 := by decide +kernel
  have hM40 : chartMat 32 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 32 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 32 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 32 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 32 4 4 = 2 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 32 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 32 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 32 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 32 2 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 32 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 32 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 32 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_32_3 (x : CuspE3)
    (hs2 : (ceilH 32 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 32 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 32 x (ceilH 32 x) 3 = kleinPt 32 x 3 * chartNum 32 x (ceilH 32 x) 4 := by
  have hM30 : chartMat 32 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 32 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 32 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 32 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 32 3 4 = 0 := by decide +kernel
  have hM40 : chartMat 32 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 32 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 32 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 32 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 32 4 4 = 2 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 32 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 32 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 32 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 32 3 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 32 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 32 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 32 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_33_0 (x : CuspE3)
    (hs2 : (ceilH 33 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 33 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 33 x (ceilH 33 x) 0 = kleinPt 33 x 0 * chartNum 33 x (ceilH 33 x) 4 := by
  have hM00 : chartMat 33 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 33 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 33 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 33 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 33 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 33 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 33 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 33 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 33 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 33 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 33 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 33 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 33 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 33 0 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 33 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 33 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 33 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_33_1 (x : CuspE3)
    (hs2 : (ceilH 33 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 33 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 33 x (ceilH 33 x) 1 = kleinPt 33 x 1 * chartNum 33 x (ceilH 33 x) 4 := by
  have hM10 : chartMat 33 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 33 1 1 = 2 := by decide +kernel
  have hM12 : chartMat 33 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 33 1 3 = -2 := by decide +kernel
  have hM14 : chartMat 33 1 4 = 3 := by decide +kernel
  have hM40 : chartMat 33 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 33 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 33 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 33 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 33 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 33 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 33 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 33 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 33 1 = ((9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 33 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 33 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 33 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_33_2 (x : CuspE3)
    (hs2 : (ceilH 33 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 33 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 33 x (ceilH 33 x) 2 = kleinPt 33 x 2 * chartNum 33 x (ceilH 33 x) 4 := by
  have hM20 : chartMat 33 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 33 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 33 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 33 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 33 2 4 = 1 := by decide +kernel
  have hM40 : chartMat 33 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 33 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 33 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 33 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 33 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 33 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 33 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 33 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 33 2 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 33 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 33 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 33 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_33_3 (x : CuspE3)
    (hs2 : (ceilH 33 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 33 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 33 x (ceilH 33 x) 3 = kleinPt 33 x 3 * chartNum 33 x (ceilH 33 x) 4 := by
  have hM30 : chartMat 33 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 33 3 1 = -2 := by decide +kernel
  have hM32 : chartMat 33 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 33 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 33 3 4 = -2 := by decide +kernel
  have hM40 : chartMat 33 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 33 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 33 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 33 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 33 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 33 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 33 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 33 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 33 3 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 33 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 33 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 33 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_34_0 (x : CuspE3)
    (hs2 : (ceilH 34 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 34 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 34 x (ceilH 34 x) 0 = kleinPt 34 x 0 * chartNum 34 x (ceilH 34 x) 4 := by
  have hM00 : chartMat 34 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 34 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 34 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 34 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 34 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 34 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 34 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 34 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 34 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 34 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 34 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 34 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 34 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 34 0 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 34 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 34 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 34 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_34_1 (x : CuspE3)
    (hs2 : (ceilH 34 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 34 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 34 x (ceilH 34 x) 1 = kleinPt 34 x 1 * chartNum 34 x (ceilH 34 x) 4 := by
  have hM10 : chartMat 34 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 34 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 34 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 34 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 34 1 4 = -1 := by decide +kernel
  have hM40 : chartMat 34 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 34 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 34 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 34 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 34 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 34 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 34 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 34 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 34 1 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 34 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 34 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 34 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_34_2 (x : CuspE3)
    (hs2 : (ceilH 34 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 34 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 34 x (ceilH 34 x) 2 = kleinPt 34 x 2 * chartNum 34 x (ceilH 34 x) 4 := by
  have hM20 : chartMat 34 2 0 = 2 := by decide +kernel
  have hM21 : chartMat 34 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 34 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 34 2 3 = -2 := by decide +kernel
  have hM24 : chartMat 34 2 4 = 3 := by decide +kernel
  have hM40 : chartMat 34 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 34 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 34 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 34 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 34 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 34 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 34 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 34 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 34 2 = ((9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 34 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 34 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 34 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_34_3 (x : CuspE3)
    (hs2 : (ceilH 34 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 34 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 34 x (ceilH 34 x) 3 = kleinPt 34 x 3 * chartNum 34 x (ceilH 34 x) 4 := by
  have hM30 : chartMat 34 3 0 = 2 := by decide +kernel
  have hM31 : chartMat 34 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 34 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 34 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 34 3 4 = 2 := by decide +kernel
  have hM40 : chartMat 34 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 34 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 34 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 34 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 34 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 34 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 34 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 34 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 34 3 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 34 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 34 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 34 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_35_0 (x : CuspE3)
    (hs2 : (ceilH 35 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 35 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 35 x (ceilH 35 x) 0 = kleinPt 35 x 0 * chartNum 35 x (ceilH 35 x) 4 := by
  have hM00 : chartMat 35 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 35 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 35 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 35 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 35 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 35 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 35 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 35 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 35 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 35 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 35 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 35 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 35 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 35 0 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 35 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 35 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 35 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_35_1 (x : CuspE3)
    (hs2 : (ceilH 35 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 35 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 35 x (ceilH 35 x) 1 = kleinPt 35 x 1 * chartNum 35 x (ceilH 35 x) 4 := by
  have hM10 : chartMat 35 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 35 1 1 = 2 := by decide +kernel
  have hM12 : chartMat 35 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 35 1 3 = 2 := by decide +kernel
  have hM14 : chartMat 35 1 4 = -3 := by decide +kernel
  have hM40 : chartMat 35 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 35 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 35 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 35 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 35 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 35 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 35 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 35 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 35 1 = ((-9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 35 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 35 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 35 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_35_2 (x : CuspE3)
    (hs2 : (ceilH 35 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 35 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 35 x (ceilH 35 x) 2 = kleinPt 35 x 2 * chartNum 35 x (ceilH 35 x) 4 := by
  have hM20 : chartMat 35 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 35 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 35 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 35 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 35 2 4 = 1 := by decide +kernel
  have hM40 : chartMat 35 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 35 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 35 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 35 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 35 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 35 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 35 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 35 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 35 2 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 35 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 35 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 35 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_35_3 (x : CuspE3)
    (hs2 : (ceilH 35 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 35 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 35 x (ceilH 35 x) 3 = kleinPt 35 x 3 * chartNum 35 x (ceilH 35 x) 4 := by
  have hM30 : chartMat 35 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 35 3 1 = -2 := by decide +kernel
  have hM32 : chartMat 35 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 35 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 35 3 4 = 2 := by decide +kernel
  have hM40 : chartMat 35 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 35 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 35 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 35 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 35 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 35 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 35 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 35 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 35 3 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 35 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 35 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 35 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_36_0 (x : CuspE3)
    (hs2 : (ceilH 36 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 36 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 36 x (ceilH 36 x) 0 = kleinPt 36 x 0 * chartNum 36 x (ceilH 36 x) 4 := by
  have hM00 : chartMat 36 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 36 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 36 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 36 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 36 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 36 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 36 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 36 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 36 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 36 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 36 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 36 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 36 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 36 0 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 36 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 36 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 36 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_36_1 (x : CuspE3)
    (hs2 : (ceilH 36 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 36 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 36 x (ceilH 36 x) 1 = kleinPt 36 x 1 * chartNum 36 x (ceilH 36 x) 4 := by
  have hM10 : chartMat 36 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 36 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 36 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 36 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 36 1 4 = 1 := by decide +kernel
  have hM40 : chartMat 36 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 36 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 36 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 36 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 36 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 36 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 36 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 36 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 36 1 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 36 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 36 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 36 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_36_2 (x : CuspE3)
    (hs2 : (ceilH 36 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 36 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 36 x (ceilH 36 x) 2 = kleinPt 36 x 2 * chartNum 36 x (ceilH 36 x) 4 := by
  have hM20 : chartMat 36 2 0 = 2 := by decide +kernel
  have hM21 : chartMat 36 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 36 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 36 2 3 = -2 := by decide +kernel
  have hM24 : chartMat 36 2 4 = 3 := by decide +kernel
  have hM40 : chartMat 36 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 36 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 36 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 36 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 36 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 36 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 36 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 36 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 36 2 = ((9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 36 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 36 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 36 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_36_3 (x : CuspE3)
    (hs2 : (ceilH 36 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 36 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 36 x (ceilH 36 x) 3 = kleinPt 36 x 3 * chartNum 36 x (ceilH 36 x) 4 := by
  have hM30 : chartMat 36 3 0 = -2 := by decide +kernel
  have hM31 : chartMat 36 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 36 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 36 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 36 3 4 = -2 := by decide +kernel
  have hM40 : chartMat 36 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 36 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 36 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 36 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 36 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 36 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 36 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 36 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 36 3 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 36 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 36 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 36 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_37_0 (x : CuspE3)
    (hs2 : (ceilH 37 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 37 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 37 x (ceilH 37 x) 0 = kleinPt 37 x 0 * chartNum 37 x (ceilH 37 x) 4 := by
  have hM00 : chartMat 37 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 37 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 37 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 37 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 37 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 37 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 37 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 37 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 37 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 37 4 4 = 6 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 37 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 37 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 37 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 37 0 = ((-3 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 37 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 37 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 37 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_37_1 (x : CuspE3)
    (hs2 : (ceilH 37 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 37 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 37 x (ceilH 37 x) 1 = kleinPt 37 x 1 * chartNum 37 x (ceilH 37 x) 4 := by
  have hM10 : chartMat 37 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 37 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 37 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 37 1 3 = -2 := by decide +kernel
  have hM14 : chartMat 37 1 4 = 3 := by decide +kernel
  have hM40 : chartMat 37 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 37 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 37 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 37 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 37 4 4 = 6 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 37 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 37 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 37 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 37 1 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 37 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 37 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 37 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_37_2 (x : CuspE3)
    (hs2 : (ceilH 37 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 37 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 37 x (ceilH 37 x) 2 = kleinPt 37 x 2 * chartNum 37 x (ceilH 37 x) 4 := by
  have hM20 : chartMat 37 2 0 = -2 := by decide +kernel
  have hM21 : chartMat 37 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 37 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 37 2 3 = 2 := by decide +kernel
  have hM24 : chartMat 37 2 4 = -3 := by decide +kernel
  have hM40 : chartMat 37 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 37 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 37 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 37 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 37 4 4 = 6 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 37 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 37 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 37 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 37 2 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 37 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 37 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 37 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_37_3 (x : CuspE3)
    (hs2 : (ceilH 37 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 37 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 37 x (ceilH 37 x) 3 = kleinPt 37 x 3 * chartNum 37 x (ceilH 37 x) 4 := by
  have hM30 : chartMat 37 3 0 = 2 := by decide +kernel
  have hM31 : chartMat 37 3 1 = -2 := by decide +kernel
  have hM32 : chartMat 37 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 37 3 3 = -3 := by decide +kernel
  have hM34 : chartMat 37 3 4 = 4 := by decide +kernel
  have hM40 : chartMat 37 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 37 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 37 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 37 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 37 4 4 = 6 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 37 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 37 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 37 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 37 3 = ((9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 37 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 37 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 37 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_38_0 (x : CuspE3)
    (hs2 : (ceilH 38 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 38 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 38 x (ceilH 38 x) 0 = kleinPt 38 x 0 * chartNum 38 x (ceilH 38 x) 4 := by
  have hM00 : chartMat 38 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 38 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 38 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 38 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 38 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 38 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 38 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 38 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 38 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 38 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 38 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 38 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 38 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 38 0 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 38 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 38 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 38 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_38_1 (x : CuspE3)
    (hs2 : (ceilH 38 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 38 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 38 x (ceilH 38 x) 1 = kleinPt 38 x 1 * chartNum 38 x (ceilH 38 x) 4 := by
  have hM10 : chartMat 38 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 38 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 38 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 38 1 3 = 2 := by decide +kernel
  have hM14 : chartMat 38 1 4 = -3 := by decide +kernel
  have hM40 : chartMat 38 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 38 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 38 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 38 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 38 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 38 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 38 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 38 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 38 1 = ((-9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 38 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 38 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 38 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_38_2 (x : CuspE3)
    (hs2 : (ceilH 38 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 38 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 38 x (ceilH 38 x) 2 = kleinPt 38 x 2 * chartNum 38 x (ceilH 38 x) 4 := by
  have hM20 : chartMat 38 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 38 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 38 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 38 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 38 2 4 = -1 := by decide +kernel
  have hM40 : chartMat 38 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 38 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 38 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 38 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 38 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 38 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 38 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 38 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 38 2 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 38 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 38 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 38 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_38_3 (x : CuspE3)
    (hs2 : (ceilH 38 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 38 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 38 x (ceilH 38 x) 3 = kleinPt 38 x 3 * chartNum 38 x (ceilH 38 x) 4 := by
  have hM30 : chartMat 38 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 38 3 1 = 2 := by decide +kernel
  have hM32 : chartMat 38 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 38 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 38 3 4 = 2 := by decide +kernel
  have hM40 : chartMat 38 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 38 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 38 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 38 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 38 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 38 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 38 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 38 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 38 3 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 38 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 38 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 38 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_39_0 (x : CuspE3)
    (hs2 : (ceilH 39 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 39 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 39 x (ceilH 39 x) 0 = kleinPt 39 x 0 * chartNum 39 x (ceilH 39 x) 4 := by
  have hM00 : chartMat 39 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 39 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 39 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 39 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 39 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 39 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 39 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 39 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 39 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 39 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 39 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 39 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 39 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 39 0 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 39 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 39 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 39 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_39_1 (x : CuspE3)
    (hs2 : (ceilH 39 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 39 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 39 x (ceilH 39 x) 1 = kleinPt 39 x 1 * chartNum 39 x (ceilH 39 x) 4 := by
  have hM10 : chartMat 39 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 39 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 39 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 39 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 39 1 4 = 1 := by decide +kernel
  have hM40 : chartMat 39 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 39 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 39 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 39 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 39 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 39 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 39 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 39 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 39 1 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 39 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 39 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 39 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_39_2 (x : CuspE3)
    (hs2 : (ceilH 39 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 39 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 39 x (ceilH 39 x) 2 = kleinPt 39 x 2 * chartNum 39 x (ceilH 39 x) 4 := by
  have hM20 : chartMat 39 2 0 = 2 := by decide +kernel
  have hM21 : chartMat 39 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 39 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 39 2 3 = 2 := by decide +kernel
  have hM24 : chartMat 39 2 4 = -3 := by decide +kernel
  have hM40 : chartMat 39 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 39 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 39 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 39 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 39 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 39 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 39 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 39 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 39 2 = ((-9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 39 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 39 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 39 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_39_3 (x : CuspE3)
    (hs2 : (ceilH 39 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 39 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 39 x (ceilH 39 x) 3 = kleinPt 39 x 3 * chartNum 39 x (ceilH 39 x) 4 := by
  have hM30 : chartMat 39 3 0 = 2 := by decide +kernel
  have hM31 : chartMat 39 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 39 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 39 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 39 3 4 = -2 := by decide +kernel
  have hM40 : chartMat 39 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 39 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 39 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 39 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 39 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 39 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 39 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 39 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 39 3 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 39 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 39 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 39 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_40_0 (x : CuspE3)
    (hs2 : (ceilH 40 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 40 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 40 x (ceilH 40 x) 0 = kleinPt 40 x 0 * chartNum 40 x (ceilH 40 x) 4 := by
  have hM00 : chartMat 40 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 40 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 40 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 40 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 40 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 40 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 40 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 40 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 40 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 40 4 4 = 6 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 40 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 40 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 40 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 40 0 = ((3 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 40 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 40 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 40 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_40_1 (x : CuspE3)
    (hs2 : (ceilH 40 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 40 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 40 x (ceilH 40 x) 1 = kleinPt 40 x 1 * chartNum 40 x (ceilH 40 x) 4 := by
  have hM10 : chartMat 40 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 40 1 1 = 2 := by decide +kernel
  have hM12 : chartMat 40 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 40 1 3 = -2 := by decide +kernel
  have hM14 : chartMat 40 1 4 = 3 := by decide +kernel
  have hM40 : chartMat 40 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 40 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 40 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 40 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 40 4 4 = 6 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 40 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 40 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 40 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 40 1 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 40 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 40 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 40 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_40_2 (x : CuspE3)
    (hs2 : (ceilH 40 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 40 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 40 x (ceilH 40 x) 2 = kleinPt 40 x 2 * chartNum 40 x (ceilH 40 x) 4 := by
  have hM20 : chartMat 40 2 0 = -2 := by decide +kernel
  have hM21 : chartMat 40 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 40 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 40 2 3 = -2 := by decide +kernel
  have hM24 : chartMat 40 2 4 = 3 := by decide +kernel
  have hM40 : chartMat 40 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 40 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 40 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 40 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 40 4 4 = 6 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 40 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 40 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 40 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 40 2 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 40 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 40 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 40 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_40_3 (x : CuspE3)
    (hs2 : (ceilH 40 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 40 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 40 x (ceilH 40 x) 3 = kleinPt 40 x 3 * chartNum 40 x (ceilH 40 x) 4 := by
  have hM30 : chartMat 40 3 0 = -2 := by decide +kernel
  have hM31 : chartMat 40 3 1 = 2 := by decide +kernel
  have hM32 : chartMat 40 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 40 3 3 = -3 := by decide +kernel
  have hM34 : chartMat 40 3 4 = 4 := by decide +kernel
  have hM40 : chartMat 40 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 40 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 40 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 40 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 40 4 4 = 6 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 40 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 40 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 40 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 40 3 = ((9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 40 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 40 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 40 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_41_0 (x : CuspE3)
    (hs2 : (ceilH 41 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 41 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 41 x (ceilH 41 x) 0 = kleinPt 41 x 0 * chartNum 41 x (ceilH 41 x) 4 := by
  have hM00 : chartMat 41 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 41 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 41 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 41 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 41 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 41 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 41 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 41 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 41 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 41 4 4 = 6 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 41 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 41 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 41 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 41 0 = ((-3 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 41 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 41 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 41 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_41_1 (x : CuspE3)
    (hs2 : (ceilH 41 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 41 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 41 x (ceilH 41 x) 1 = kleinPt 41 x 1 * chartNum 41 x (ceilH 41 x) 4 := by
  have hM10 : chartMat 41 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 41 1 1 = 2 := by decide +kernel
  have hM12 : chartMat 41 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 41 1 3 = 2 := by decide +kernel
  have hM14 : chartMat 41 1 4 = -3 := by decide +kernel
  have hM40 : chartMat 41 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 41 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 41 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 41 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 41 4 4 = 6 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 41 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 41 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 41 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 41 1 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 41 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 41 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 41 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_41_2 (x : CuspE3)
    (hs2 : (ceilH 41 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 41 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 41 x (ceilH 41 x) 2 = kleinPt 41 x 2 * chartNum 41 x (ceilH 41 x) 4 := by
  have hM20 : chartMat 41 2 0 = -2 := by decide +kernel
  have hM21 : chartMat 41 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 41 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 41 2 3 = -2 := by decide +kernel
  have hM24 : chartMat 41 2 4 = 3 := by decide +kernel
  have hM40 : chartMat 41 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 41 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 41 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 41 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 41 4 4 = 6 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 41 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 41 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 41 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 41 2 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 41 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 41 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 41 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_41_3 (x : CuspE3)
    (hs2 : (ceilH 41 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 41 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 41 x (ceilH 41 x) 3 = kleinPt 41 x 3 * chartNum 41 x (ceilH 41 x) 4 := by
  have hM30 : chartMat 41 3 0 = 2 := by decide +kernel
  have hM31 : chartMat 41 3 1 = 2 := by decide +kernel
  have hM32 : chartMat 41 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 41 3 3 = 3 := by decide +kernel
  have hM34 : chartMat 41 3 4 = -4 := by decide +kernel
  have hM40 : chartMat 41 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 41 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 41 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 41 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 41 4 4 = 6 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 41 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 41 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 41 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 41 3 = ((-9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 41 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 41 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 41 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_42_0 (x : CuspE3)
    (hs2 : (ceilH 42 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 42 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 42 x (ceilH 42 x) 0 = kleinPt 42 x 0 * chartNum 42 x (ceilH 42 x) 4 := by
  have hM00 : chartMat 42 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 42 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 42 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 42 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 42 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 42 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 42 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 42 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 42 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 42 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 42 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 42 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 42 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 42 0 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 42 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 42 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 42 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_42_1 (x : CuspE3)
    (hs2 : (ceilH 42 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 42 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 42 x (ceilH 42 x) 1 = kleinPt 42 x 1 * chartNum 42 x (ceilH 42 x) 4 := by
  have hM10 : chartMat 42 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 42 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 42 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 42 1 3 = 2 := by decide +kernel
  have hM14 : chartMat 42 1 4 = -3 := by decide +kernel
  have hM40 : chartMat 42 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 42 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 42 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 42 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 42 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 42 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 42 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 42 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 42 1 = ((-9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 42 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 42 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 42 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_42_2 (x : CuspE3)
    (hs2 : (ceilH 42 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 42 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 42 x (ceilH 42 x) 2 = kleinPt 42 x 2 * chartNum 42 x (ceilH 42 x) 4 := by
  have hM20 : chartMat 42 2 0 = 0 := by decide +kernel
  have hM21 : chartMat 42 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 42 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 42 2 3 = 0 := by decide +kernel
  have hM24 : chartMat 42 2 4 = -1 := by decide +kernel
  have hM40 : chartMat 42 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 42 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 42 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 42 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 42 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 42 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 42 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 42 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 42 2 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 42 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 42 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 42 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_42_3 (x : CuspE3)
    (hs2 : (ceilH 42 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 42 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 42 x (ceilH 42 x) 3 = kleinPt 42 x 3 * chartNum 42 x (ceilH 42 x) 4 := by
  have hM30 : chartMat 42 3 0 = 0 := by decide +kernel
  have hM31 : chartMat 42 3 1 = 2 := by decide +kernel
  have hM32 : chartMat 42 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 42 3 3 = -1 := by decide +kernel
  have hM34 : chartMat 42 3 4 = 2 := by decide +kernel
  have hM40 : chartMat 42 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 42 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 42 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 42 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 42 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 42 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 42 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 42 3 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 42 3 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 42 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 42 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 42 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_43_0 (x : CuspE3)
    (hs2 : (ceilH 43 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 43 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 43 x (ceilH 43 x) 0 = kleinPt 43 x 0 * chartNum 43 x (ceilH 43 x) 4 := by
  have hM00 : chartMat 43 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 43 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 43 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 43 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 43 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 43 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 43 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 43 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 43 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 43 4 4 = 4 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 43 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 43 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 43 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 43 0 = ((-1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 43 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 43 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 43 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_43_1 (x : CuspE3)
    (hs2 : (ceilH 43 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 43 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 43 x (ceilH 43 x) 1 = kleinPt 43 x 1 * chartNum 43 x (ceilH 43 x) 4 := by
  have hM10 : chartMat 43 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 43 1 1 = 0 := by decide +kernel
  have hM12 : chartMat 43 1 2 = 1 := by decide +kernel
  have hM13 : chartMat 43 1 3 = 0 := by decide +kernel
  have hM14 : chartMat 43 1 4 = 1 := by decide +kernel
  have hM40 : chartMat 43 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 43 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 43 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 43 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 43 4 4 = 4 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 43 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 43 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 43 1 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 43 1 = ((1 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 43 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 43 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 43 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_43_2 (x : CuspE3)
    (hs2 : (ceilH 43 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 43 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 43 x (ceilH 43 x) 2 = kleinPt 43 x 2 * chartNum 43 x (ceilH 43 x) 4 := by
  have hM20 : chartMat 43 2 0 = -2 := by decide +kernel
  have hM21 : chartMat 43 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 43 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 43 2 3 = 2 := by decide +kernel
  have hM24 : chartMat 43 2 4 = -3 := by decide +kernel
  have hM40 : chartMat 43 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 43 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 43 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 43 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 43 4 4 = 4 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 43 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 43 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 43 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 43 2 = ((-9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 43 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 43 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 43 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_43_3 (x : CuspE3)
    (hs2 : (ceilH 43 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 43 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 43 x (ceilH 43 x) 3 = kleinPt 43 x 3 * chartNum 43 x (ceilH 43 x) 4 := by
  have hM30 : chartMat 43 3 0 = -2 := by decide +kernel
  have hM31 : chartMat 43 3 1 = 0 := by decide +kernel
  have hM32 : chartMat 43 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 43 3 3 = 1 := by decide +kernel
  have hM34 : chartMat 43 3 4 = -2 := by decide +kernel
  have hM40 : chartMat 43 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 43 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 43 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 43 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 43 4 4 = 4 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 43 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 43 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 43 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 43 3 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 43 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 43 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 43 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_44_0 (x : CuspE3)
    (hs2 : (ceilH 44 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 44 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 44 x (ceilH 44 x) 0 = kleinPt 44 x 0 * chartNum 44 x (ceilH 44 x) 4 := by
  have hM00 : chartMat 44 0 0 = 1 := by decide +kernel
  have hM01 : chartMat 44 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 44 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 44 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 44 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 44 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 44 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 44 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 44 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 44 4 4 = 6 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 44 0 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 44 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 44 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 44 0 = ((-3 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 44 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 44 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 44 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_44_1 (x : CuspE3)
    (hs2 : (ceilH 44 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 44 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 44 x (ceilH 44 x) 1 = kleinPt 44 x 1 * chartNum 44 x (ceilH 44 x) 4 := by
  have hM10 : chartMat 44 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 44 1 1 = 2 := by decide +kernel
  have hM12 : chartMat 44 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 44 1 3 = -2 := by decide +kernel
  have hM14 : chartMat 44 1 4 = 3 := by decide +kernel
  have hM40 : chartMat 44 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 44 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 44 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 44 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 44 4 4 = 6 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 44 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 44 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 44 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 44 1 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 44 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 44 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 44 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_44_2 (x : CuspE3)
    (hs2 : (ceilH 44 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 44 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 44 x (ceilH 44 x) 2 = kleinPt 44 x 2 * chartNum 44 x (ceilH 44 x) 4 := by
  have hM20 : chartMat 44 2 0 = 2 := by decide +kernel
  have hM21 : chartMat 44 2 1 = 1 := by decide +kernel
  have hM22 : chartMat 44 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 44 2 3 = -2 := by decide +kernel
  have hM24 : chartMat 44 2 4 = 3 := by decide +kernel
  have hM40 : chartMat 44 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 44 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 44 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 44 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 44 4 4 = 6 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 44 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 44 2 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 44 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 44 2 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 44 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 44 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 44 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_44_3 (x : CuspE3)
    (hs2 : (ceilH 44 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 44 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 44 x (ceilH 44 x) 3 = kleinPt 44 x 3 * chartNum 44 x (ceilH 44 x) 4 := by
  have hM30 : chartMat 44 3 0 = 2 := by decide +kernel
  have hM31 : chartMat 44 3 1 = 2 := by decide +kernel
  have hM32 : chartMat 44 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 44 3 3 = -3 := by decide +kernel
  have hM34 : chartMat 44 3 4 = 4 := by decide +kernel
  have hM40 : chartMat 44 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 44 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 44 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 44 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 44 4 4 = 6 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 44 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 44 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 44 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 44 3 = ((9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 44 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 44 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 44 2 = 0 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_45_0 (x : CuspE3)
    (hs2 : (ceilH 45 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 45 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 45 x (ceilH 45 x) 0 = kleinPt 45 x 0 * chartNum 45 x (ceilH 45 x) 4 := by
  have hM00 : chartMat 45 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 45 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 45 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 45 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 45 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 45 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 45 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 45 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 45 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 45 4 4 = 6 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 45 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 45 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 45 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 45 0 = ((3 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 45 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 45 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 45 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_45_1 (x : CuspE3)
    (hs2 : (ceilH 45 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 45 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 45 x (ceilH 45 x) 1 = kleinPt 45 x 1 * chartNum 45 x (ceilH 45 x) 4 := by
  have hM10 : chartMat 45 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 45 1 1 = 2 := by decide +kernel
  have hM12 : chartMat 45 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 45 1 3 = 2 := by decide +kernel
  have hM14 : chartMat 45 1 4 = -3 := by decide +kernel
  have hM40 : chartMat 45 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 45 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 45 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 45 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 45 4 4 = 6 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 45 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 45 1 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 45 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 45 1 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 45 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 45 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 45 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_45_2 (x : CuspE3)
    (hs2 : (ceilH 45 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 45 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 45 x (ceilH 45 x) 2 = kleinPt 45 x 2 * chartNum 45 x (ceilH 45 x) 4 := by
  have hM20 : chartMat 45 2 0 = 2 := by decide +kernel
  have hM21 : chartMat 45 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 45 2 2 = 1 := by decide +kernel
  have hM23 : chartMat 45 2 3 = -2 := by decide +kernel
  have hM24 : chartMat 45 2 4 = 3 := by decide +kernel
  have hM40 : chartMat 45 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 45 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 45 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 45 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 45 4 4 = 6 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 45 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 45 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 45 2 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 45 2 = ((1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 45 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 45 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 45 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_45_3 (x : CuspE3)
    (hs2 : (ceilH 45 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 45 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 45 x (ceilH 45 x) 3 = kleinPt 45 x 3 * chartNum 45 x (ceilH 45 x) 4 := by
  have hM30 : chartMat 45 3 0 = -2 := by decide +kernel
  have hM31 : chartMat 45 3 1 = 2 := by decide +kernel
  have hM32 : chartMat 45 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 45 3 3 = 3 := by decide +kernel
  have hM34 : chartMat 45 3 4 = -4 := by decide +kernel
  have hM40 : chartMat 45 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 45 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 45 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 45 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 45 4 4 = 6 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 45 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 45 3 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 45 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 45 3 = ((-9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 45 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 45 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 45 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_46_0 (x : CuspE3)
    (hs2 : (ceilH 46 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 46 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 46 x (ceilH 46 x) 0 = kleinPt 46 x 0 * chartNum 46 x (ceilH 46 x) 4 := by
  have hM00 : chartMat 46 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 46 0 1 = 1 := by decide +kernel
  have hM02 : chartMat 46 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 46 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 46 0 4 = 1 := by decide +kernel
  have hM40 : chartMat 46 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 46 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 46 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 46 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 46 4 4 = 6 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 46 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 46 0 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 46 0 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 46 0 = ((-3 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 46 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 46 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 46 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_46_1 (x : CuspE3)
    (hs2 : (ceilH 46 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 46 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 46 x (ceilH 46 x) 1 = kleinPt 46 x 1 * chartNum 46 x (ceilH 46 x) 4 := by
  have hM10 : chartMat 46 1 0 = 1 := by decide +kernel
  have hM11 : chartMat 46 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 46 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 46 1 3 = 2 := by decide +kernel
  have hM14 : chartMat 46 1 4 = -3 := by decide +kernel
  have hM40 : chartMat 46 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 46 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 46 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 46 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 46 4 4 = 6 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 46 1 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 46 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 46 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 46 1 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 46 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 46 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 46 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_46_2 (x : CuspE3)
    (hs2 : (ceilH 46 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 46 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 46 x (ceilH 46 x) 2 = kleinPt 46 x 2 * chartNum 46 x (ceilH 46 x) 4 := by
  have hM20 : chartMat 46 2 0 = 2 := by decide +kernel
  have hM21 : chartMat 46 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 46 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 46 2 3 = 2 := by decide +kernel
  have hM24 : chartMat 46 2 4 = -3 := by decide +kernel
  have hM40 : chartMat 46 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 46 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 46 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 46 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 46 4 4 = 6 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 46 2 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 46 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 46 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 46 2 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 46 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 46 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 46 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_46_3 (x : CuspE3)
    (hs2 : (ceilH 46 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 46 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 46 x (ceilH 46 x) 3 = kleinPt 46 x 3 * chartNum 46 x (ceilH 46 x) 4 := by
  have hM30 : chartMat 46 3 0 = 2 := by decide +kernel
  have hM31 : chartMat 46 3 1 = -2 := by decide +kernel
  have hM32 : chartMat 46 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 46 3 3 = 3 := by decide +kernel
  have hM34 : chartMat 46 3 4 = -4 := by decide +kernel
  have hM40 : chartMat 46 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 46 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 46 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 46 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 46 4 4 = 6 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 46 3 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 46 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 46 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 46 3 = ((-9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 46 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 46 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 46 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_47_0 (x : CuspE3)
    (hs2 : (ceilH 47 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 47 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 47 x (ceilH 47 x) 0 = kleinPt 47 x 0 * chartNum 47 x (ceilH 47 x) 4 := by
  have hM00 : chartMat 47 0 0 = -1 := by decide +kernel
  have hM01 : chartMat 47 0 1 = -1 := by decide +kernel
  have hM02 : chartMat 47 0 2 = 0 := by decide +kernel
  have hM03 : chartMat 47 0 3 = 0 := by decide +kernel
  have hM04 : chartMat 47 0 4 = -1 := by decide +kernel
  have hM40 : chartMat 47 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 47 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 47 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 47 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 47 4 4 = 6 := by decide +kernel
  have hX00 : Work.Cusp.cubeXToKlein 47 0 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX01 : Work.Cusp.cubeXToKlein 47 0 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX02 : Work.Cusp.cubeXToKlein 47 0 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb0 : Work.Cusp.cubeXToKleinb 47 0 = ((3 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 47 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 47 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 47 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM00, hM01, hM02, hM03, hM04, hM40, hM41, hM42, hM43, hM44, hX00, hX01, hX02, hb0, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_47_1 (x : CuspE3)
    (hs2 : (ceilH 47 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 47 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 47 x (ceilH 47 x) 1 = kleinPt 47 x 1 * chartNum 47 x (ceilH 47 x) 4 := by
  have hM10 : chartMat 47 1 0 = -1 := by decide +kernel
  have hM11 : chartMat 47 1 1 = -2 := by decide +kernel
  have hM12 : chartMat 47 1 2 = -1 := by decide +kernel
  have hM13 : chartMat 47 1 3 = 2 := by decide +kernel
  have hM14 : chartMat 47 1 4 = -3 := by decide +kernel
  have hM40 : chartMat 47 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 47 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 47 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 47 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 47 4 4 = 6 := by decide +kernel
  have hX10 : Work.Cusp.cubeXToKlein 47 1 0 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX11 : Work.Cusp.cubeXToKlein 47 1 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX12 : Work.Cusp.cubeXToKlein 47 1 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb1 : Work.Cusp.cubeXToKleinb 47 1 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 47 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 47 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 47 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM10, hM11, hM12, hM13, hM14, hM40, hM41, hM42, hM43, hM44, hX10, hX11, hX12, hb1, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_47_2 (x : CuspE3)
    (hs2 : (ceilH 47 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 47 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 47 x (ceilH 47 x) 2 = kleinPt 47 x 2 * chartNum 47 x (ceilH 47 x) 4 := by
  have hM20 : chartMat 47 2 0 = -2 := by decide +kernel
  have hM21 : chartMat 47 2 1 = -1 := by decide +kernel
  have hM22 : chartMat 47 2 2 = -1 := by decide +kernel
  have hM23 : chartMat 47 2 3 = 2 := by decide +kernel
  have hM24 : chartMat 47 2 4 = -3 := by decide +kernel
  have hM40 : chartMat 47 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 47 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 47 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 47 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 47 4 4 = 6 := by decide +kernel
  have hX20 : Work.Cusp.cubeXToKlein 47 2 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX21 : Work.Cusp.cubeXToKlein 47 2 1 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX22 : Work.Cusp.cubeXToKlein 47 2 2 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb2 : Work.Cusp.cubeXToKleinb 47 2 = ((-1 : ℚ)/2) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 47 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 47 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 47 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM20, hM21, hM22, hM23, hM24, hM40, hM41, hM42, hM43, hM44, hX20, hX21, hX22, hb2, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_47_3 (x : CuspE3)
    (hs2 : (ceilH 47 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 47 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 47 x (ceilH 47 x) 3 = kleinPt 47 x 3 * chartNum 47 x (ceilH 47 x) 4 := by
  have hM30 : chartMat 47 3 0 = -2 := by decide +kernel
  have hM31 : chartMat 47 3 1 = -2 := by decide +kernel
  have hM32 : chartMat 47 3 2 = 0 := by decide +kernel
  have hM33 : chartMat 47 3 3 = 3 := by decide +kernel
  have hM34 : chartMat 47 3 4 = -4 := by decide +kernel
  have hM40 : chartMat 47 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 47 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 47 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 47 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 47 4 4 = 6 := by decide +kernel
  have hX30 : Work.Cusp.cubeXToKlein 47 3 0 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX31 : Work.Cusp.cubeXToKlein 47 3 1 = ((-1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hX32 : Work.Cusp.cubeXToKlein 47 3 2 = ((1 : ℚ)/5) := by norm_num [Work.Cusp.cubeXToKlein]
  have hb3 : Work.Cusp.cubeXToKleinb 47 3 = ((-9 : ℚ)/10) := by norm_num [Work.Cusp.cubeXToKleinb]
  have hc0 : Work.Cusp.cubeCorner 47 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 47 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 47 2 = -1 := by decide +kernel
  simp only [chartNum, kleinPt, Fin.sum_univ_three,
    hM30, hM31, hM32, hM33, hM34, hM40, hM41, hM42, hM43, hM44, hX30, hX31, hX32, hb3, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum_id_c0 (a : Fin 48) (x : CuspE3) (hs2 : (ceilH a x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1 / 2)) ^ 2) :
    chartNum a x (ceilH a x) 0 = kleinPt a x 0 * chartNum a x (ceilH a x) 4 := by
  fin_cases a
  · exact cnum_id_0_0 x hs2
  · exact cnum_id_1_0 x hs2
  · exact cnum_id_2_0 x hs2
  · exact cnum_id_3_0 x hs2
  · exact cnum_id_4_0 x hs2
  · exact cnum_id_5_0 x hs2
  · exact cnum_id_6_0 x hs2
  · exact cnum_id_7_0 x hs2
  · exact cnum_id_8_0 x hs2
  · exact cnum_id_9_0 x hs2
  · exact cnum_id_10_0 x hs2
  · exact cnum_id_11_0 x hs2
  · exact cnum_id_12_0 x hs2
  · exact cnum_id_13_0 x hs2
  · exact cnum_id_14_0 x hs2
  · exact cnum_id_15_0 x hs2
  · exact cnum_id_16_0 x hs2
  · exact cnum_id_17_0 x hs2
  · exact cnum_id_18_0 x hs2
  · exact cnum_id_19_0 x hs2
  · exact cnum_id_20_0 x hs2
  · exact cnum_id_21_0 x hs2
  · exact cnum_id_22_0 x hs2
  · exact cnum_id_23_0 x hs2
  · exact cnum_id_24_0 x hs2
  · exact cnum_id_25_0 x hs2
  · exact cnum_id_26_0 x hs2
  · exact cnum_id_27_0 x hs2
  · exact cnum_id_28_0 x hs2
  · exact cnum_id_29_0 x hs2
  · exact cnum_id_30_0 x hs2
  · exact cnum_id_31_0 x hs2
  · exact cnum_id_32_0 x hs2
  · exact cnum_id_33_0 x hs2
  · exact cnum_id_34_0 x hs2
  · exact cnum_id_35_0 x hs2
  · exact cnum_id_36_0 x hs2
  · exact cnum_id_37_0 x hs2
  · exact cnum_id_38_0 x hs2
  · exact cnum_id_39_0 x hs2
  · exact cnum_id_40_0 x hs2
  · exact cnum_id_41_0 x hs2
  · exact cnum_id_42_0 x hs2
  · exact cnum_id_43_0 x hs2
  · exact cnum_id_44_0 x hs2
  · exact cnum_id_45_0 x hs2
  · exact cnum_id_46_0 x hs2
  · exact cnum_id_47_0 x hs2

private lemma cnum_id_c1 (a : Fin 48) (x : CuspE3) (hs2 : (ceilH a x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1 / 2)) ^ 2) :
    chartNum a x (ceilH a x) 1 = kleinPt a x 1 * chartNum a x (ceilH a x) 4 := by
  fin_cases a
  · exact cnum_id_0_1 x hs2
  · exact cnum_id_1_1 x hs2
  · exact cnum_id_2_1 x hs2
  · exact cnum_id_3_1 x hs2
  · exact cnum_id_4_1 x hs2
  · exact cnum_id_5_1 x hs2
  · exact cnum_id_6_1 x hs2
  · exact cnum_id_7_1 x hs2
  · exact cnum_id_8_1 x hs2
  · exact cnum_id_9_1 x hs2
  · exact cnum_id_10_1 x hs2
  · exact cnum_id_11_1 x hs2
  · exact cnum_id_12_1 x hs2
  · exact cnum_id_13_1 x hs2
  · exact cnum_id_14_1 x hs2
  · exact cnum_id_15_1 x hs2
  · exact cnum_id_16_1 x hs2
  · exact cnum_id_17_1 x hs2
  · exact cnum_id_18_1 x hs2
  · exact cnum_id_19_1 x hs2
  · exact cnum_id_20_1 x hs2
  · exact cnum_id_21_1 x hs2
  · exact cnum_id_22_1 x hs2
  · exact cnum_id_23_1 x hs2
  · exact cnum_id_24_1 x hs2
  · exact cnum_id_25_1 x hs2
  · exact cnum_id_26_1 x hs2
  · exact cnum_id_27_1 x hs2
  · exact cnum_id_28_1 x hs2
  · exact cnum_id_29_1 x hs2
  · exact cnum_id_30_1 x hs2
  · exact cnum_id_31_1 x hs2
  · exact cnum_id_32_1 x hs2
  · exact cnum_id_33_1 x hs2
  · exact cnum_id_34_1 x hs2
  · exact cnum_id_35_1 x hs2
  · exact cnum_id_36_1 x hs2
  · exact cnum_id_37_1 x hs2
  · exact cnum_id_38_1 x hs2
  · exact cnum_id_39_1 x hs2
  · exact cnum_id_40_1 x hs2
  · exact cnum_id_41_1 x hs2
  · exact cnum_id_42_1 x hs2
  · exact cnum_id_43_1 x hs2
  · exact cnum_id_44_1 x hs2
  · exact cnum_id_45_1 x hs2
  · exact cnum_id_46_1 x hs2
  · exact cnum_id_47_1 x hs2

private lemma cnum_id_c2 (a : Fin 48) (x : CuspE3) (hs2 : (ceilH a x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1 / 2)) ^ 2) :
    chartNum a x (ceilH a x) 2 = kleinPt a x 2 * chartNum a x (ceilH a x) 4 := by
  fin_cases a
  · exact cnum_id_0_2 x hs2
  · exact cnum_id_1_2 x hs2
  · exact cnum_id_2_2 x hs2
  · exact cnum_id_3_2 x hs2
  · exact cnum_id_4_2 x hs2
  · exact cnum_id_5_2 x hs2
  · exact cnum_id_6_2 x hs2
  · exact cnum_id_7_2 x hs2
  · exact cnum_id_8_2 x hs2
  · exact cnum_id_9_2 x hs2
  · exact cnum_id_10_2 x hs2
  · exact cnum_id_11_2 x hs2
  · exact cnum_id_12_2 x hs2
  · exact cnum_id_13_2 x hs2
  · exact cnum_id_14_2 x hs2
  · exact cnum_id_15_2 x hs2
  · exact cnum_id_16_2 x hs2
  · exact cnum_id_17_2 x hs2
  · exact cnum_id_18_2 x hs2
  · exact cnum_id_19_2 x hs2
  · exact cnum_id_20_2 x hs2
  · exact cnum_id_21_2 x hs2
  · exact cnum_id_22_2 x hs2
  · exact cnum_id_23_2 x hs2
  · exact cnum_id_24_2 x hs2
  · exact cnum_id_25_2 x hs2
  · exact cnum_id_26_2 x hs2
  · exact cnum_id_27_2 x hs2
  · exact cnum_id_28_2 x hs2
  · exact cnum_id_29_2 x hs2
  · exact cnum_id_30_2 x hs2
  · exact cnum_id_31_2 x hs2
  · exact cnum_id_32_2 x hs2
  · exact cnum_id_33_2 x hs2
  · exact cnum_id_34_2 x hs2
  · exact cnum_id_35_2 x hs2
  · exact cnum_id_36_2 x hs2
  · exact cnum_id_37_2 x hs2
  · exact cnum_id_38_2 x hs2
  · exact cnum_id_39_2 x hs2
  · exact cnum_id_40_2 x hs2
  · exact cnum_id_41_2 x hs2
  · exact cnum_id_42_2 x hs2
  · exact cnum_id_43_2 x hs2
  · exact cnum_id_44_2 x hs2
  · exact cnum_id_45_2 x hs2
  · exact cnum_id_46_2 x hs2
  · exact cnum_id_47_2 x hs2

private lemma cnum_id_c3 (a : Fin 48) (x : CuspE3) (hs2 : (ceilH a x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1 / 2)) ^ 2) :
    chartNum a x (ceilH a x) 3 = kleinPt a x 3 * chartNum a x (ceilH a x) 4 := by
  fin_cases a
  · exact cnum_id_0_3 x hs2
  · exact cnum_id_1_3 x hs2
  · exact cnum_id_2_3 x hs2
  · exact cnum_id_3_3 x hs2
  · exact cnum_id_4_3 x hs2
  · exact cnum_id_5_3 x hs2
  · exact cnum_id_6_3 x hs2
  · exact cnum_id_7_3 x hs2
  · exact cnum_id_8_3 x hs2
  · exact cnum_id_9_3 x hs2
  · exact cnum_id_10_3 x hs2
  · exact cnum_id_11_3 x hs2
  · exact cnum_id_12_3 x hs2
  · exact cnum_id_13_3 x hs2
  · exact cnum_id_14_3 x hs2
  · exact cnum_id_15_3 x hs2
  · exact cnum_id_16_3 x hs2
  · exact cnum_id_17_3 x hs2
  · exact cnum_id_18_3 x hs2
  · exact cnum_id_19_3 x hs2
  · exact cnum_id_20_3 x hs2
  · exact cnum_id_21_3 x hs2
  · exact cnum_id_22_3 x hs2
  · exact cnum_id_23_3 x hs2
  · exact cnum_id_24_3 x hs2
  · exact cnum_id_25_3 x hs2
  · exact cnum_id_26_3 x hs2
  · exact cnum_id_27_3 x hs2
  · exact cnum_id_28_3 x hs2
  · exact cnum_id_29_3 x hs2
  · exact cnum_id_30_3 x hs2
  · exact cnum_id_31_3 x hs2
  · exact cnum_id_32_3 x hs2
  · exact cnum_id_33_3 x hs2
  · exact cnum_id_34_3 x hs2
  · exact cnum_id_35_3 x hs2
  · exact cnum_id_36_3 x hs2
  · exact cnum_id_37_3 x hs2
  · exact cnum_id_38_3 x hs2
  · exact cnum_id_39_3 x hs2
  · exact cnum_id_40_3 x hs2
  · exact cnum_id_41_3 x hs2
  · exact cnum_id_42_3 x hs2
  · exact cnum_id_43_3 x hs2
  · exact cnum_id_44_3 x hs2
  · exact cnum_id_45_3 x hs2
  · exact cnum_id_46_3 x hs2
  · exact cnum_id_47_3 x hs2

private lemma cnum4_eq_0 (x : CuspE3)
    (hs2 : (ceilH 0 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 0 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 0 x (ceilH 0 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 0 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 0 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 0 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 0 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 0 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 0 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 0 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 0 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_1 (x : CuspE3)
    (hs2 : (ceilH 1 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 1 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 1 x (ceilH 1 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 1 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 1 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 1 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 1 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 1 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 1 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 1 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 1 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_2 (x : CuspE3)
    (hs2 : (ceilH 2 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 2 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 2 x (ceilH 2 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 2 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 2 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 2 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 2 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 2 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 2 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 2 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 2 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_3 (x : CuspE3)
    (hs2 : (ceilH 3 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 3 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 3 x (ceilH 3 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 3 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 3 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 3 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 3 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 3 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 3 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 3 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 3 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_4 (x : CuspE3)
    (hs2 : (ceilH 4 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 4 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 4 x (ceilH 4 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 4 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 4 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 4 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 4 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 4 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 4 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 4 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 4 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_5 (x : CuspE3)
    (hs2 : (ceilH 5 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 5 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 5 x (ceilH 5 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 5 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 5 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 5 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 5 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 5 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 5 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 5 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 5 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_6 (x : CuspE3)
    (hs2 : (ceilH 6 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 6 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 6 x (ceilH 6 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 6 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 6 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 6 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 6 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 6 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 6 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 6 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 6 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_7 (x : CuspE3)
    (hs2 : (ceilH 7 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 7 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 7 x (ceilH 7 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 7 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 7 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 7 4 2 = -6 := by decide +kernel
  have hM43 : chartMat 7 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 7 4 4 = 8 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 7 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 7 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 7 2 = 1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_8 (x : CuspE3)
    (hs2 : (ceilH 8 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 8 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 8 x (ceilH 8 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 8 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 8 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 8 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 8 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 8 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 8 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 8 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 8 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_9 (x : CuspE3)
    (hs2 : (ceilH 9 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 9 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 9 x (ceilH 9 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 9 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 9 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 9 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 9 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 9 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 9 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 9 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 9 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_10 (x : CuspE3)
    (hs2 : (ceilH 10 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 10 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 10 x (ceilH 10 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 10 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 10 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 10 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 10 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 10 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 10 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 10 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 10 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_11 (x : CuspE3)
    (hs2 : (ceilH 11 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 11 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 11 x (ceilH 11 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 11 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 11 4 1 = 2 := by decide +kernel
  have hM42 : chartMat 11 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 11 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 11 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 11 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 11 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 11 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_12 (x : CuspE3)
    (hs2 : (ceilH 12 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 12 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 12 x (ceilH 12 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 12 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 12 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 12 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 12 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 12 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 12 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 12 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 12 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_13 (x : CuspE3)
    (hs2 : (ceilH 13 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 13 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 13 x (ceilH 13 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 13 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 13 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 13 4 2 = -2 := by decide +kernel
  have hM43 : chartMat 13 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 13 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 13 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 13 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 13 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_14 (x : CuspE3)
    (hs2 : (ceilH 14 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 14 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 14 x (ceilH 14 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 14 4 0 = -2 := by decide +kernel
  have hM41 : chartMat 14 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 14 4 2 = 2 := by decide +kernel
  have hM43 : chartMat 14 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 14 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 14 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 14 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 14 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_15 (x : CuspE3)
    (hs2 : (ceilH 15 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 15 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 15 x (ceilH 15 x) 4 = ( 10 : ℝ) := by
  have hM40 : chartMat 15 4 0 = 2 := by decide +kernel
  have hM41 : chartMat 15 4 1 = -2 := by decide +kernel
  have hM42 : chartMat 15 4 2 = -6 := by decide +kernel
  have hM43 : chartMat 15 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 15 4 4 = 8 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 15 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 15 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 15 2 = 1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_16 (x : CuspE3)
    (hs2 : (ceilH 16 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 16 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 16 x (ceilH 16 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 16 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 16 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 16 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 16 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 16 4 4 = 2 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 16 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 16 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 16 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_17 (x : CuspE3)
    (hs2 : (ceilH 17 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 17 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 17 x (ceilH 17 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 17 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 17 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 17 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 17 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 17 4 4 = 2 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 17 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 17 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 17 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_18 (x : CuspE3)
    (hs2 : (ceilH 18 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 18 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 18 x (ceilH 18 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 18 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 18 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 18 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 18 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 18 4 4 = 2 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 18 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 18 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 18 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_19 (x : CuspE3)
    (hs2 : (ceilH 19 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 19 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 19 x (ceilH 19 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 19 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 19 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 19 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 19 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 19 4 4 = 2 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 19 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 19 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 19 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_20 (x : CuspE3)
    (hs2 : (ceilH 20 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 20 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 20 x (ceilH 20 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 20 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 20 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 20 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 20 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 20 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 20 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 20 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 20 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_21 (x : CuspE3)
    (hs2 : (ceilH 21 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 21 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 21 x (ceilH 21 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 21 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 21 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 21 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 21 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 21 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 21 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 21 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 21 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_22 (x : CuspE3)
    (hs2 : (ceilH 22 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 22 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 22 x (ceilH 22 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 22 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 22 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 22 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 22 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 22 4 4 = 2 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 22 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 22 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 22 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_23 (x : CuspE3)
    (hs2 : (ceilH 23 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 23 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 23 x (ceilH 23 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 23 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 23 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 23 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 23 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 23 4 4 = 2 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 23 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 23 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 23 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_24 (x : CuspE3)
    (hs2 : (ceilH 24 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 24 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 24 x (ceilH 24 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 24 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 24 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 24 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 24 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 24 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 24 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 24 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 24 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_25 (x : CuspE3)
    (hs2 : (ceilH 25 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 25 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 25 x (ceilH 25 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 25 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 25 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 25 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 25 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 25 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 25 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 25 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 25 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_26 (x : CuspE3)
    (hs2 : (ceilH 26 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 26 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 26 x (ceilH 26 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 26 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 26 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 26 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 26 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 26 4 4 = 2 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 26 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 26 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 26 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_27 (x : CuspE3)
    (hs2 : (ceilH 27 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 27 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 27 x (ceilH 27 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 27 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 27 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 27 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 27 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 27 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 27 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 27 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 27 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_28 (x : CuspE3)
    (hs2 : (ceilH 28 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 28 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 28 x (ceilH 28 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 28 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 28 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 28 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 28 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 28 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 28 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 28 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 28 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_29 (x : CuspE3)
    (hs2 : (ceilH 29 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 29 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 29 x (ceilH 29 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 29 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 29 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 29 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 29 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 29 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 29 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 29 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 29 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_30 (x : CuspE3)
    (hs2 : (ceilH 30 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 30 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 30 x (ceilH 30 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 30 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 30 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 30 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 30 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 30 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 30 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 30 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 30 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_31 (x : CuspE3)
    (hs2 : (ceilH 31 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 31 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 31 x (ceilH 31 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 31 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 31 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 31 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 31 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 31 4 4 = 6 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 31 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 31 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 31 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_32 (x : CuspE3)
    (hs2 : (ceilH 32 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 32 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 32 x (ceilH 32 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 32 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 32 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 32 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 32 4 3 = 0 := by decide +kernel
  have hM44 : chartMat 32 4 4 = 2 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 32 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 32 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 32 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_33 (x : CuspE3)
    (hs2 : (ceilH 33 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 33 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 33 x (ceilH 33 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 33 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 33 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 33 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 33 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 33 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 33 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 33 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 33 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_34 (x : CuspE3)
    (hs2 : (ceilH 34 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 34 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 34 x (ceilH 34 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 34 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 34 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 34 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 34 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 34 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 34 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 34 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 34 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_35 (x : CuspE3)
    (hs2 : (ceilH 35 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 35 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 35 x (ceilH 35 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 35 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 35 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 35 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 35 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 35 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 35 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 35 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 35 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_36 (x : CuspE3)
    (hs2 : (ceilH 36 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 36 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 36 x (ceilH 36 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 36 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 36 4 1 = -1 := by decide +kernel
  have hM42 : chartMat 36 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 36 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 36 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 36 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 36 1 = 0 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 36 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_37 (x : CuspE3)
    (hs2 : (ceilH 37 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 37 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 37 x (ceilH 37 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 37 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 37 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 37 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 37 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 37 4 4 = 6 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 37 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 37 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 37 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_38 (x : CuspE3)
    (hs2 : (ceilH 38 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 38 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 38 x (ceilH 38 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 38 4 0 = -1 := by decide +kernel
  have hM41 : chartMat 38 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 38 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 38 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 38 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 38 0 = 0 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 38 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 38 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_39 (x : CuspE3)
    (hs2 : (ceilH 39 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 39 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 39 x (ceilH 39 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 39 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 39 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 39 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 39 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 39 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 39 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 39 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 39 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_40 (x : CuspE3)
    (hs2 : (ceilH 40 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 40 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 40 x (ceilH 40 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 40 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 40 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 40 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 40 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 40 4 4 = 6 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 40 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 40 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 40 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_41 (x : CuspE3)
    (hs2 : (ceilH 41 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 41 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 41 x (ceilH 41 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 41 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 41 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 41 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 41 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 41 4 4 = 6 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 41 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 41 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 41 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_42 (x : CuspE3)
    (hs2 : (ceilH 42 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 42 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 42 x (ceilH 42 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 42 4 0 = 1 := by decide +kernel
  have hM41 : chartMat 42 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 42 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 42 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 42 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 42 0 = -1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 42 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 42 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_43 (x : CuspE3)
    (hs2 : (ceilH 43 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 43 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 43 x (ceilH 43 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 43 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 43 4 1 = 1 := by decide +kernel
  have hM42 : chartMat 43 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 43 4 3 = -2 := by decide +kernel
  have hM44 : chartMat 43 4 4 = 4 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 43 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 43 1 = -1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 43 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_44 (x : CuspE3)
    (hs2 : (ceilH 44 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 44 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 44 x (ceilH 44 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 44 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 44 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 44 4 2 = -1 := by decide +kernel
  have hM43 : chartMat 44 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 44 4 4 = 6 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 44 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 44 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 44 2 = 0 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_45 (x : CuspE3)
    (hs2 : (ceilH 45 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 45 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 45 x (ceilH 45 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 45 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 45 4 1 = -3 := by decide +kernel
  have hM42 : chartMat 45 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 45 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 45 4 4 = 6 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 45 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 45 1 = 1 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 45 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_46 (x : CuspE3)
    (hs2 : (ceilH 46 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 46 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 46 x (ceilH 46 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 46 4 0 = -3 := by decide +kernel
  have hM41 : chartMat 46 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 46 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 46 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 46 4 4 = 6 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 46 0 = 1 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 46 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 46 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_eq_47 (x : CuspE3)
    (hs2 : (ceilH 47 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 47 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 47 x (ceilH 47 x) 4 = ( 5 : ℝ) := by
  have hM40 : chartMat 47 4 0 = 3 := by decide +kernel
  have hM41 : chartMat 47 4 1 = 3 := by decide +kernel
  have hM42 : chartMat 47 4 2 = 1 := by decide +kernel
  have hM43 : chartMat 47 4 3 = -4 := by decide +kernel
  have hM44 : chartMat 47 4 4 = 6 := by decide +kernel
  have hc0 : Work.Cusp.cubeCorner 47 0 = -2 := by decide +kernel
  have hc1 : Work.Cusp.cubeCorner 47 1 = -2 := by decide +kernel
  have hc2 : Work.Cusp.cubeCorner 47 2 = -1 := by decide +kernel
  simp only [chartNum, Fin.sum_univ_three,
    hM40, hM41, hM42, hM43, hM44, hc0, hc1, hc2]
  rw [hs2]
  simp only [Fin.sum_univ_three, hc0, hc1, hc2]
  push_cast
  ring

private lemma cnum4_ne_0 (x : CuspE3) (hs2 : (ceilH 0 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 0 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 0 x (ceilH 0 x) 4 ≠ 0 := by
  rw [cnum4_eq_0 x hs2]
  norm_num

private lemma cnum4_ne_1 (x : CuspE3) (hs2 : (ceilH 1 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 1 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 1 x (ceilH 1 x) 4 ≠ 0 := by
  rw [cnum4_eq_1 x hs2]
  norm_num

private lemma cnum4_ne_2 (x : CuspE3) (hs2 : (ceilH 2 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 2 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 2 x (ceilH 2 x) 4 ≠ 0 := by
  rw [cnum4_eq_2 x hs2]
  norm_num

private lemma cnum4_ne_3 (x : CuspE3) (hs2 : (ceilH 3 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 3 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 3 x (ceilH 3 x) 4 ≠ 0 := by
  rw [cnum4_eq_3 x hs2]
  norm_num

private lemma cnum4_ne_4 (x : CuspE3) (hs2 : (ceilH 4 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 4 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 4 x (ceilH 4 x) 4 ≠ 0 := by
  rw [cnum4_eq_4 x hs2]
  norm_num

private lemma cnum4_ne_5 (x : CuspE3) (hs2 : (ceilH 5 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 5 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 5 x (ceilH 5 x) 4 ≠ 0 := by
  rw [cnum4_eq_5 x hs2]
  norm_num

private lemma cnum4_ne_6 (x : CuspE3) (hs2 : (ceilH 6 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 6 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 6 x (ceilH 6 x) 4 ≠ 0 := by
  rw [cnum4_eq_6 x hs2]
  norm_num

private lemma cnum4_ne_7 (x : CuspE3) (hs2 : (ceilH 7 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 7 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 7 x (ceilH 7 x) 4 ≠ 0 := by
  rw [cnum4_eq_7 x hs2]
  norm_num

private lemma cnum4_ne_8 (x : CuspE3) (hs2 : (ceilH 8 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 8 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 8 x (ceilH 8 x) 4 ≠ 0 := by
  rw [cnum4_eq_8 x hs2]
  norm_num

private lemma cnum4_ne_9 (x : CuspE3) (hs2 : (ceilH 9 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 9 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 9 x (ceilH 9 x) 4 ≠ 0 := by
  rw [cnum4_eq_9 x hs2]
  norm_num

private lemma cnum4_ne_10 (x : CuspE3) (hs2 : (ceilH 10 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 10 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 10 x (ceilH 10 x) 4 ≠ 0 := by
  rw [cnum4_eq_10 x hs2]
  norm_num

private lemma cnum4_ne_11 (x : CuspE3) (hs2 : (ceilH 11 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 11 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 11 x (ceilH 11 x) 4 ≠ 0 := by
  rw [cnum4_eq_11 x hs2]
  norm_num

private lemma cnum4_ne_12 (x : CuspE3) (hs2 : (ceilH 12 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 12 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 12 x (ceilH 12 x) 4 ≠ 0 := by
  rw [cnum4_eq_12 x hs2]
  norm_num

private lemma cnum4_ne_13 (x : CuspE3) (hs2 : (ceilH 13 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 13 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 13 x (ceilH 13 x) 4 ≠ 0 := by
  rw [cnum4_eq_13 x hs2]
  norm_num

private lemma cnum4_ne_14 (x : CuspE3) (hs2 : (ceilH 14 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 14 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 14 x (ceilH 14 x) 4 ≠ 0 := by
  rw [cnum4_eq_14 x hs2]
  norm_num

private lemma cnum4_ne_15 (x : CuspE3) (hs2 : (ceilH 15 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 15 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 15 x (ceilH 15 x) 4 ≠ 0 := by
  rw [cnum4_eq_15 x hs2]
  norm_num

private lemma cnum4_ne_16 (x : CuspE3) (hs2 : (ceilH 16 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 16 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 16 x (ceilH 16 x) 4 ≠ 0 := by
  rw [cnum4_eq_16 x hs2]
  norm_num

private lemma cnum4_ne_17 (x : CuspE3) (hs2 : (ceilH 17 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 17 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 17 x (ceilH 17 x) 4 ≠ 0 := by
  rw [cnum4_eq_17 x hs2]
  norm_num

private lemma cnum4_ne_18 (x : CuspE3) (hs2 : (ceilH 18 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 18 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 18 x (ceilH 18 x) 4 ≠ 0 := by
  rw [cnum4_eq_18 x hs2]
  norm_num

private lemma cnum4_ne_19 (x : CuspE3) (hs2 : (ceilH 19 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 19 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 19 x (ceilH 19 x) 4 ≠ 0 := by
  rw [cnum4_eq_19 x hs2]
  norm_num

private lemma cnum4_ne_20 (x : CuspE3) (hs2 : (ceilH 20 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 20 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 20 x (ceilH 20 x) 4 ≠ 0 := by
  rw [cnum4_eq_20 x hs2]
  norm_num

private lemma cnum4_ne_21 (x : CuspE3) (hs2 : (ceilH 21 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 21 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 21 x (ceilH 21 x) 4 ≠ 0 := by
  rw [cnum4_eq_21 x hs2]
  norm_num

private lemma cnum4_ne_22 (x : CuspE3) (hs2 : (ceilH 22 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 22 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 22 x (ceilH 22 x) 4 ≠ 0 := by
  rw [cnum4_eq_22 x hs2]
  norm_num

private lemma cnum4_ne_23 (x : CuspE3) (hs2 : (ceilH 23 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 23 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 23 x (ceilH 23 x) 4 ≠ 0 := by
  rw [cnum4_eq_23 x hs2]
  norm_num

private lemma cnum4_ne_24 (x : CuspE3) (hs2 : (ceilH 24 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 24 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 24 x (ceilH 24 x) 4 ≠ 0 := by
  rw [cnum4_eq_24 x hs2]
  norm_num

private lemma cnum4_ne_25 (x : CuspE3) (hs2 : (ceilH 25 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 25 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 25 x (ceilH 25 x) 4 ≠ 0 := by
  rw [cnum4_eq_25 x hs2]
  norm_num

private lemma cnum4_ne_26 (x : CuspE3) (hs2 : (ceilH 26 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 26 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 26 x (ceilH 26 x) 4 ≠ 0 := by
  rw [cnum4_eq_26 x hs2]
  norm_num

private lemma cnum4_ne_27 (x : CuspE3) (hs2 : (ceilH 27 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 27 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 27 x (ceilH 27 x) 4 ≠ 0 := by
  rw [cnum4_eq_27 x hs2]
  norm_num

private lemma cnum4_ne_28 (x : CuspE3) (hs2 : (ceilH 28 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 28 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 28 x (ceilH 28 x) 4 ≠ 0 := by
  rw [cnum4_eq_28 x hs2]
  norm_num

private lemma cnum4_ne_29 (x : CuspE3) (hs2 : (ceilH 29 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 29 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 29 x (ceilH 29 x) 4 ≠ 0 := by
  rw [cnum4_eq_29 x hs2]
  norm_num

private lemma cnum4_ne_30 (x : CuspE3) (hs2 : (ceilH 30 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 30 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 30 x (ceilH 30 x) 4 ≠ 0 := by
  rw [cnum4_eq_30 x hs2]
  norm_num

private lemma cnum4_ne_31 (x : CuspE3) (hs2 : (ceilH 31 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 31 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 31 x (ceilH 31 x) 4 ≠ 0 := by
  rw [cnum4_eq_31 x hs2]
  norm_num

private lemma cnum4_ne_32 (x : CuspE3) (hs2 : (ceilH 32 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 32 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 32 x (ceilH 32 x) 4 ≠ 0 := by
  rw [cnum4_eq_32 x hs2]
  norm_num

private lemma cnum4_ne_33 (x : CuspE3) (hs2 : (ceilH 33 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 33 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 33 x (ceilH 33 x) 4 ≠ 0 := by
  rw [cnum4_eq_33 x hs2]
  norm_num

private lemma cnum4_ne_34 (x : CuspE3) (hs2 : (ceilH 34 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 34 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 34 x (ceilH 34 x) 4 ≠ 0 := by
  rw [cnum4_eq_34 x hs2]
  norm_num

private lemma cnum4_ne_35 (x : CuspE3) (hs2 : (ceilH 35 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 35 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 35 x (ceilH 35 x) 4 ≠ 0 := by
  rw [cnum4_eq_35 x hs2]
  norm_num

private lemma cnum4_ne_36 (x : CuspE3) (hs2 : (ceilH 36 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 36 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 36 x (ceilH 36 x) 4 ≠ 0 := by
  rw [cnum4_eq_36 x hs2]
  norm_num

private lemma cnum4_ne_37 (x : CuspE3) (hs2 : (ceilH 37 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 37 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 37 x (ceilH 37 x) 4 ≠ 0 := by
  rw [cnum4_eq_37 x hs2]
  norm_num

private lemma cnum4_ne_38 (x : CuspE3) (hs2 : (ceilH 38 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 38 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 38 x (ceilH 38 x) 4 ≠ 0 := by
  rw [cnum4_eq_38 x hs2]
  norm_num

private lemma cnum4_ne_39 (x : CuspE3) (hs2 : (ceilH 39 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 39 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 39 x (ceilH 39 x) 4 ≠ 0 := by
  rw [cnum4_eq_39 x hs2]
  norm_num

private lemma cnum4_ne_40 (x : CuspE3) (hs2 : (ceilH 40 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 40 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 40 x (ceilH 40 x) 4 ≠ 0 := by
  rw [cnum4_eq_40 x hs2]
  norm_num

private lemma cnum4_ne_41 (x : CuspE3) (hs2 : (ceilH 41 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 41 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 41 x (ceilH 41 x) 4 ≠ 0 := by
  rw [cnum4_eq_41 x hs2]
  norm_num

private lemma cnum4_ne_42 (x : CuspE3) (hs2 : (ceilH 42 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 42 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 42 x (ceilH 42 x) 4 ≠ 0 := by
  rw [cnum4_eq_42 x hs2]
  norm_num

private lemma cnum4_ne_43 (x : CuspE3) (hs2 : (ceilH 43 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 43 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 43 x (ceilH 43 x) 4 ≠ 0 := by
  rw [cnum4_eq_43 x hs2]
  norm_num

private lemma cnum4_ne_44 (x : CuspE3) (hs2 : (ceilH 44 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 44 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 44 x (ceilH 44 x) 4 ≠ 0 := by
  rw [cnum4_eq_44 x hs2]
  norm_num

private lemma cnum4_ne_45 (x : CuspE3) (hs2 : (ceilH 45 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 45 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 45 x (ceilH 45 x) 4 ≠ 0 := by
  rw [cnum4_eq_45 x hs2]
  norm_num

private lemma cnum4_ne_46 (x : CuspE3) (hs2 : (ceilH 46 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 46 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 46 x (ceilH 46 x) 4 ≠ 0 := by
  rw [cnum4_eq_46 x hs2]
  norm_num

private lemma cnum4_ne_47 (x : CuspE3) (hs2 : (ceilH 47 x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner 47 j : ℝ) + 1 / 2)) ^ 2) :
    chartNum 47 x (ceilH 47 x) 4 ≠ 0 := by
  rw [cnum4_eq_47 x hs2]
  norm_num

private lemma cnum4_ne (a : Fin 48) (x : CuspE3) (hs2 : (ceilH a x) ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1 / 2)) ^ 2) :
    chartNum a x (ceilH a x) 4 ≠ 0 := by
  fin_cases a
  · exact cnum4_ne_0 x hs2
  · exact cnum4_ne_1 x hs2
  · exact cnum4_ne_2 x hs2
  · exact cnum4_ne_3 x hs2
  · exact cnum4_ne_4 x hs2
  · exact cnum4_ne_5 x hs2
  · exact cnum4_ne_6 x hs2
  · exact cnum4_ne_7 x hs2
  · exact cnum4_ne_8 x hs2
  · exact cnum4_ne_9 x hs2
  · exact cnum4_ne_10 x hs2
  · exact cnum4_ne_11 x hs2
  · exact cnum4_ne_12 x hs2
  · exact cnum4_ne_13 x hs2
  · exact cnum4_ne_14 x hs2
  · exact cnum4_ne_15 x hs2
  · exact cnum4_ne_16 x hs2
  · exact cnum4_ne_17 x hs2
  · exact cnum4_ne_18 x hs2
  · exact cnum4_ne_19 x hs2
  · exact cnum4_ne_20 x hs2
  · exact cnum4_ne_21 x hs2
  · exact cnum4_ne_22 x hs2
  · exact cnum4_ne_23 x hs2
  · exact cnum4_ne_24 x hs2
  · exact cnum4_ne_25 x hs2
  · exact cnum4_ne_26 x hs2
  · exact cnum4_ne_27 x hs2
  · exact cnum4_ne_28 x hs2
  · exact cnum4_ne_29 x hs2
  · exact cnum4_ne_30 x hs2
  · exact cnum4_ne_31 x hs2
  · exact cnum4_ne_32 x hs2
  · exact cnum4_ne_33 x hs2
  · exact cnum4_ne_34 x hs2
  · exact cnum4_ne_35 x hs2
  · exact cnum4_ne_36 x hs2
  · exact cnum4_ne_37 x hs2
  · exact cnum4_ne_38 x hs2
  · exact cnum4_ne_39 x hs2
  · exact cnum4_ne_40 x hs2
  · exact cnum4_ne_41 x hs2
  · exact cnum4_ne_42 x hs2
  · exact cnum4_ne_43 x hs2
  · exact cnum4_ne_44 x hs2
  · exact cnum4_ne_45 x hs2
  · exact cnum4_ne_46 x hs2
  · exact cnum4_ne_47 x hs2

/-- **The chart of the cube `a` at its ceiling is the affine facet map.** -/
theorem chartKlein_ceiling (a : Fin 48) {x : Work.RTOwed.CuspE3}
    (hx : x ∈ Work.RTOwed.cubeBox a) :
    Work.RTOwed.chartKlein a (Work.RTOwed.mkE4 x (Work.RTOwed.ceilH a x)) =
      Work.RTOwed.kleinPt a x := by
  have hs2 : (ceilH a x) ^ 2 = 9 / 4 - ∑ j : Fin 3,
      (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1 / 2)) ^ 2 := ceilH_sq a hx
  have hspos : 0 < ceilH a x := ceilH_pos a hx
  have hs : ceilH a x ≠ 0 := ne_of_gt hspos
  have h2s : (2 : ℝ) * ceilH a x ≠ 0 := by positivity
  have hD : chartNum a x (ceilH a x) 4 ≠ 0 := cnum4_ne a x hs2
  ext i
  have hNi : chartNum a x (ceilH a x) (Fin.castSucc i) =
      kleinPt a x i * chartNum a x (ceilH a x) 4 := by
    fin_cases i
    · exact cnum_id_c0 a x hs2
    · exact cnum_id_c1 a x hs2
    · exact cnum_id_c2 a x hs2
    · exact cnum_id_c3 a x hs2
  rw [chartKlein_apply]
  have hi : MV a (mkE4 x (ceilH a x)) (Fin.castSucc i) =
      chartNum a x (ceilH a x) (Fin.castSucc i) / (2 * ceilH a x) := by
    rw [eq_div_iff h2s, mul_comm]
    exact chartNum_spec a x (ceilH a x) hs (Fin.castSucc i)
  have h4 : MV a (mkE4 x (ceilH a x)) 4 =
      chartNum a x (ceilH a x) 4 / (2 * ceilH a x) := by
    rw [eq_div_iff h2s, mul_comm]
    exact chartNum_spec a x (ceilH a x) hs 4
  rw [hi, h4, hNi, inv_div]
  field_simp

end Work.RTOwed
