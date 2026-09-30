/-
# The chart of a cube lands in `Q̄` (`Work.RTOwed.chartKlein_mem`)

This file proves the certificate `Work.RTOwed.chartKlein_mem`: for a cube `a : Fin 48` of the cusp
development, a point `x` of the closed unit cube `cubeBox a` and a height `s` with
`11/10 ≤ s ≤ ceilH a x`, the Möbius chart `chartKlein a (mkE4 x s)` of `cuspChart.lean` lies in the
truncated 24-cell `Work.FoldInst.Qbar`.

## Method

Write `V = chartMat a *ᵥ uhsVec x s`, where `uhsVec x s = 2s · hypOfUHS (mkE4 x s)`; then
`chartKlein a (mkE4 x s) i = V i / V 4` on the first four coordinates.  A side of `Q̄` is
`n · y ≤ 1`, a truncation is `p_w · y ≤ 4/5`, so the two families of constraints are

  `Nside a S x s = V 4 - ∑ n_i V i ≥ 0`,  `Ntrunc a w x s = 8 V 4 - 5 ∑ t_i V i ≥ 0`

(and `V 4 > 0`).  Each `V i` is a quadratic polynomial in `(x, s)` of the shape

  `V i = Cq a i · (∑ x_j² + s²) + ∑_j Cl a i j · x_j + Ck a i`

with *integer* coefficients `Cq, Cl, Ck` read off `chartMat a`.  Hence every constraint has the same
shape `H = c · (∑ x_j² + s²) + ∑ l_j x_j + e`, and the sign of `c` decides where its minimum over
the region `{x ∈ cubeBox a, 11/10 ≤ s ≤ ceilH a x}` is attained:

* `c > 0`: `H` is increasing in `s`, and `c t² + l t ≥ -l²/(4c)` for every `t`, so
  `H ≥ c·(11/10)² + e - ∑ l_j²/(4c)`.  This is a single integer inequality, cleared of denominators:
  `121 c² + 100 c e - 25 ∑ l_j² ≥ 0` (`certPos`).
* `c = 0`: `H = ∑ l_j x_j + e` is affine in `x`; with `t_j = x_j - corner a j ∈ [0,1]` its minimum
  on the cube is `e + ∑ min l_j 0 + ∑ l_j (corner a j)` (`certZero`).
* `c < 0`: `H` is decreasing in `s`, so `H ≥ H (x, ceilH a x)`, which is affine in `x`; the ceiling
  relation `ceilH a x² = 9/4 - ∑ (x_j - corner a j - 1/2)²` turns its minimum on the cube into the
  integer expression `certNeg` (twice the bound).

The certificates are finite checks over `a : Fin 48` and the 48 constraints, proved by `decide`
(`certS_nonneg`, `certT_nonneg`, `cert4_pos`, `Cq4_pos`).
-/
import Mathlib
import Submission.Work.RTOwed.cuspChart

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


set_option maxHeartbeats 4000000
set_option maxRecDepth 100000

noncomputable section

open scoped Matrix BigOperators
open Set Topology Function

namespace Work.RTOwed

/- The helper namespace of the certificate `chartKlein_mem`: all definitions and auxiliary lemmas
live here so that the file can be imported alongside the other chart certificates without
duplicating names in `Work.RTOwed`. -/
namespace chartKleinMem

/-! ## The chart in terms of the integer matrix

`chartMat a` is the (integral) chart matrix of the cube `a`; `uhsVec x s` is `2s · hypOfUHS (mkE4 x
s)`, so that the chart of the cube is `kleinOfHyp (chartMat a *ᵥ uhsVec x s)`, whose coordinates are
quotients of the components of `chartVec a x s = chartMat a *ᵥ uhsVec x s`. -/

/-- The squared radius `∑ x_j² + s²` of `mkE4 x s`. -/
def qsq (x : CuspE3) (s : ℝ) : ℝ := ∑ j : Fin 3, x j ^ 2 + s ^ 2

/-- `2 s · hypOfUHS (mkE4 x s)` (the homogenised upper half space coordinates). -/
def uhsVec (x : CuspE3) (s : ℝ) : Fin 5 → ℝ :=
  ![2 * x 0, 2 * x 1, 2 * x 2, qsq x s - 1, qsq x s + 1]

/-- `chartMat a` with real entries. -/
def chartMatR (a : Fin 48) : Matrix (Fin 5) (Fin 5) ℝ := (chartMat a).map (Int.castRingHom ℝ)

/-- The chart vector of the cube `a` at `(x, s)`. -/
def chartVec (a : Fin 48) (x : CuspE3) (s : ℝ) : Fin 5 → ℝ := chartMatR a *ᵥ uhsVec x s

/-- `∑ x_j²` of `mkE4 x s`. -/
lemma norm_sq_mkE4 (x : CuspE3) (s : ℝ) : ‖mkE4 x s‖ ^ 2 = qsq x s := by
  rw [EuclideanSpace.real_norm_sq_eq, mkE4]
  simp only [qsq, Fin.sum_univ_four, Fin.sum_univ_three]
  norm_num

lemma mkE4_apply_zero (x : CuspE3) (s : ℝ) : (mkE4 x s) 0 = x 0 := by simp [mkE4]
lemma mkE4_apply_one (x : CuspE3) (s : ℝ) : (mkE4 x s) 1 = x 1 := by simp [mkE4]
lemma mkE4_apply_two (x : CuspE3) (s : ℝ) : (mkE4 x s) 2 = x 2 := by simp [mkE4]
lemma mkE4_apply_three (x : CuspE3) (s : ℝ) : (mkE4 x s) 3 = s := by simp [mkE4]

lemma uhsVec_zero (x : CuspE3) (s : ℝ) : uhsVec x s 0 = 2 * x 0 := rfl
lemma uhsVec_one (x : CuspE3) (s : ℝ) : uhsVec x s 1 = 2 * x 1 := rfl
lemma uhsVec_two (x : CuspE3) (s : ℝ) : uhsVec x s 2 = 2 * x 2 := rfl
lemma uhsVec_three (x : CuspE3) (s : ℝ) : uhsVec x s 3 = qsq x s - 1 := rfl
lemma uhsVec_four (x : CuspE3) (s : ℝ) : uhsVec x s 4 = qsq x s + 1 := rfl

/-- `hypOfUHS (mkE4 x s) = (2s)⁻¹ • uhsVec x s`. -/
theorem hypOfUHS_mkE4 (x : CuspE3) (s : ℝ) :
    Work.HypModel.hypOfUHS (mkE4 x s) = (2 * s)⁻¹ • uhsVec x s := by
  have c0 : Work.HypModel.hypOfUHS (mkE4 x s) 0 = (2 * s)⁻¹ * uhsVec x s 0 := by
    rw [Work.HypModel.hypOfUHS_apply_zero, mkE4_apply_three, mkE4_apply_zero, uhsVec_zero]
    field_simp
  have c1 : Work.HypModel.hypOfUHS (mkE4 x s) 1 = (2 * s)⁻¹ * uhsVec x s 1 := by
    rw [Work.HypModel.hypOfUHS_apply_one, mkE4_apply_three, mkE4_apply_one, uhsVec_one]
    field_simp
  have c2 : Work.HypModel.hypOfUHS (mkE4 x s) 2 = (2 * s)⁻¹ * uhsVec x s 2 := by
    rw [Work.HypModel.hypOfUHS_apply_two, mkE4_apply_three, mkE4_apply_two, uhsVec_two]
    field_simp
  have c3 : Work.HypModel.hypOfUHS (mkE4 x s) 3 = (2 * s)⁻¹ * uhsVec x s 3 := by
    rw [Work.HypModel.hypOfUHS_apply_three, mkE4_apply_three, norm_sq_mkE4, uhsVec_three]
    field_simp
  have c4 : Work.HypModel.hypOfUHS (mkE4 x s) 4 = (2 * s)⁻¹ * uhsVec x s 4 := by
    rw [Work.HypModel.hypOfUHS_apply_four, mkE4_apply_three, norm_sq_mkE4, uhsVec_four]
    field_simp
  funext i
  fin_cases i
  · exact c0
  · exact c1
  · exact c2
  · exact c3
  · exact c4

/-- `kleinOfHyp` is invariant under a nonzero scaling of the ambient vector. -/
theorem kleinOfHyp_smul {c : ℝ} (hc : c ≠ 0) (P : Work.HypModel.V5) :
    Work.HypModel.kleinOfHyp (c • P) = Work.HypModel.kleinOfHyp P := by
  ext i
  fin_cases i <;>
    simp [Work.HypModel.kleinOfHyp, Work.HypModel.proj4, Pi.smul_apply, smul_eq_mul]
    <;> field_simp

/-- The chart of the cube at `(x, s)` is the normalised chart vector. -/
theorem chartKlein_mkE4_0 (a : Fin 48) (x : CuspE3) (s : ℝ) (hs : s ≠ 0) :
    chartKlein a (mkE4 x s) 0 = chartVec a x s 0 / chartVec a x s 4 := by
  have h24 : (2 * s)⁻¹ ≠ 0 := by simp [hs]
  have h1 : chartKlein a (mkE4 x s)
      = Work.HypModel.kleinOfHyp (chartMatR a *ᵥ uhsVec x s) := by
    simp only [chartKlein, chartMatR, hypOfUHS_mkE4 x s, Matrix.mulVec_smul,
      kleinOfHyp_smul h24]
  rw [h1, Work.HypModel.kleinOfHyp_apply_zero]
  simp only [chartVec]
  ring

theorem chartKlein_mkE4_1 (a : Fin 48) (x : CuspE3) (s : ℝ) (hs : s ≠ 0) :
    chartKlein a (mkE4 x s) 1 = chartVec a x s 1 / chartVec a x s 4 := by
  have h24 : (2 * s)⁻¹ ≠ 0 := by simp [hs]
  have h1 : chartKlein a (mkE4 x s)
      = Work.HypModel.kleinOfHyp (chartMatR a *ᵥ uhsVec x s) := by
    simp only [chartKlein, chartMatR, hypOfUHS_mkE4 x s, Matrix.mulVec_smul,
      kleinOfHyp_smul h24]
  rw [h1, Work.HypModel.kleinOfHyp_apply_one]
  simp only [chartVec]
  ring

theorem chartKlein_mkE4_2 (a : Fin 48) (x : CuspE3) (s : ℝ) (hs : s ≠ 0) :
    chartKlein a (mkE4 x s) 2 = chartVec a x s 2 / chartVec a x s 4 := by
  have h24 : (2 * s)⁻¹ ≠ 0 := by simp [hs]
  have h1 : chartKlein a (mkE4 x s)
      = Work.HypModel.kleinOfHyp (chartMatR a *ᵥ uhsVec x s) := by
    simp only [chartKlein, chartMatR, hypOfUHS_mkE4 x s, Matrix.mulVec_smul,
      kleinOfHyp_smul h24]
  rw [h1, Work.HypModel.kleinOfHyp_apply_two]
  simp only [chartVec]
  ring

theorem chartKlein_mkE4_3 (a : Fin 48) (x : CuspE3) (s : ℝ) (hs : s ≠ 0) :
    chartKlein a (mkE4 x s) 3 = chartVec a x s 3 / chartVec a x s 4 := by
  have h24 : (2 * s)⁻¹ ≠ 0 := by simp [hs]
  have h1 : chartKlein a (mkE4 x s)
      = Work.HypModel.kleinOfHyp (chartMatR a *ᵥ uhsVec x s) := by
    simp only [chartKlein, chartMatR, hypOfUHS_mkE4 x s, Matrix.mulVec_smul,
      kleinOfHyp_smul h24]
  rw [h1, Work.HypModel.kleinOfHyp_apply_three]
  simp only [chartVec]
  ring

/-- The integer coefficients of the quadratic form `V i = Cq i · q² + ∑ Cl i j x_j + Ck i` of the
chart vector. -/
def Cq (a : Fin 48) (i : Fin 5) : ℤ := chartMat a i 3 + chartMat a i 4
def Cl (a : Fin 48) (i : Fin 5) : Fin 3 → ℤ :=
  ![2 * chartMat a i 0, 2 * chartMat a i 1, 2 * chartMat a i 2]
def Ck (a : Fin 48) (i : Fin 5) : ℤ := chartMat a i 4 - chartMat a i 3

/-- **The components of the chart vector are quadratic forms with integer coefficients.** -/
theorem chartVec_eq (a : Fin 48) (x : CuspE3) (s : ℝ) (i : Fin 5) :
    chartVec a x s i = (Cq a i : ℝ) * qsq x s + ∑ j : Fin 3, (Cl a i j : ℝ) * x j + (Ck a i : ℝ) := by
  simp only [chartVec, chartMatR, Matrix.mulVec, dotProduct, qsq, uhsVec, Cq, Cl, Ck,
    Fin.sum_univ_five, Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.cons_val_two, Matrix.cons_val_three, Matrix.cons_val_four, Matrix.vecHead, Matrix.vecTail,
    Function.comp_apply, Matrix.map_apply, Int.coe_castRingHom]
  push_cast
  ring

/-! ## The numerators of the slack functions

`sideSlack S y = 1 - ∑ n_i y_i` and `truncSlack w y = (8 - 5 ∑ t_i y_i)/10`; the denominators are
`1` and `10` times the fourth chart coordinate `chartVec a x s 4`, which is a strictly positive
number on the region of interest, so the constraints are the numerators below. -/

/-- The numerator `V 4 - ∑_i n_{S,i} V i` of `sideSlack S` on the chart of the cube. -/
def Nside (a : Fin 48) (S : Fin 24) (x : CuspE3) (s : ℝ) : ℝ :=
  chartVec a x s 4 - ((Work.FoldInst.sideNormal S 0 : ℝ) * chartVec a x s 0
    + (Work.FoldInst.sideNormal S 1 : ℝ) * chartVec a x s 1
    + (Work.FoldInst.sideNormal S 2 : ℝ) * chartVec a x s 2
    + (Work.FoldInst.sideNormal S 3 : ℝ) * chartVec a x s 3)

/-- The numerator `8 V 4 - 5 ∑_i t_{w,i} V i` of `truncSlack w` on the chart of the cube. -/
def Ntrunc (a : Fin 48) (w : Fin 24) (x : CuspE3) (s : ℝ) : ℝ :=
  8 * chartVec a x s 4 - 5 * ((Work.FoldInst.truncNormal2 w 0 : ℝ) * chartVec a x s 0
    + (Work.FoldInst.truncNormal2 w 1 : ℝ) * chartVec a x s 1
    + (Work.FoldInst.truncNormal2 w 2 : ℝ) * chartVec a x s 2
    + (Work.FoldInst.truncNormal2 w 3 : ℝ) * chartVec a x s 3)

/-- **The side slack is the numerator over the fourth chart coordinate.** -/
theorem sideSlack_eq (a : Fin 48) (S : Fin 24) (x : CuspE3) (s : ℝ) (hs : s ≠ 0)
    (h4 : chartVec a x s 4 ≠ 0) :
    Work.FoldInst.sideSlack S (chartKlein a (mkE4 x s)) = Nside a S x s / chartVec a x s 4 := by
  have h0 := chartKlein_mkE4_0 a x s hs
  have h1 := chartKlein_mkE4_1 a x s hs
  have h2 := chartKlein_mkE4_2 a x s hs
  have h3 := chartKlein_mkE4_3 a x s hs
  simp only [Work.FoldInst.sideSlack, Nside, Fin.sum_univ_four, h0, h1, h2, h3]
  field_simp

/-- **The truncation slack is the numerator over ten times the fourth chart coordinate.** -/
theorem truncSlack_eq (a : Fin 48) (w : Fin 24) (x : CuspE3) (s : ℝ) (hs : s ≠ 0)
    (h4 : chartVec a x s 4 ≠ 0) :
    Work.FoldInst.truncSlack w (chartKlein a (mkE4 x s))
      = Ntrunc a w x s / (10 * chartVec a x s 4) := by
  have h0 := chartKlein_mkE4_0 a x s hs
  have h1 := chartKlein_mkE4_1 a x s hs
  have h2 := chartKlein_mkE4_2 a x s hs
  have h3 := chartKlein_mkE4_3 a x s hs
  simp only [Work.FoldInst.truncSlack, Ntrunc, Fin.sum_univ_four, h0, h1, h2, h3]
  field_simp

/-! ## The numerators as quadratic forms -/

/-- `∑_i n_{S,i} f i`. -/
def nSum (S : Fin 24) (f : Fin 4 → ℤ) : ℤ := ∑ i : Fin 4, Work.FoldInst.sideNormal S i * f i

/-- `∑_i t_{w,i} f i`. -/
def tSum (w : Fin 24) (f : Fin 4 → ℤ) : ℤ := ∑ i : Fin 4, Work.FoldInst.truncNormal2 w i * f i

/-- The quadratic coefficient of `Nside a S`. -/
def Qs (a : Fin 48) (S : Fin 24) : ℤ := Cq a 4 - nSum S (fun i => Cq a i.castSucc)

/-- The linear coefficients of `Nside a S`. -/
def Ls (a : Fin 48) (S : Fin 24) : Fin 3 → ℤ := fun j => Cl a 4 j - nSum S (fun i => Cl a i.castSucc j)

/-- The constant of `Nside a S`. -/
def Ks (a : Fin 48) (S : Fin 24) : ℤ := Ck a 4 - nSum S (fun i => Ck a i.castSucc)

/-- The quadratic coefficient of `Ntrunc a w`. -/
def Qt (a : Fin 48) (w : Fin 24) : ℤ := 8 * Cq a 4 - 5 * tSum w (fun i => Cq a i.castSucc)

/-- The linear coefficients of `Ntrunc a w`. -/
def Lt (a : Fin 48) (w : Fin 24) : Fin 3 → ℤ :=
  fun j => 8 * Cl a 4 j - 5 * tSum w (fun i => Cl a i.castSucc j)

/-- The constant of `Ntrunc a w`. -/
def Kt (a : Fin 48) (w : Fin 24) : ℤ := 8 * Ck a 4 - 5 * tSum w (fun i => Ck a i.castSucc)

/-- **`Nside` is the quadratic form of its integer coefficients.** -/
theorem Nside_eq (a : Fin 48) (S : Fin 24) (x : CuspE3) (s : ℝ) :
    Nside a S x s = (Qs a S : ℝ) * qsq x s + ∑ j : Fin 3, (Ls a S j : ℝ) * x j + (Ks a S : ℝ) := by
  simp only [Nside, chartVec_eq, Qs, Ls, Ks, nSum, Cl, Cq, Ck, Fin.sum_univ_four,
    Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  push_cast
  ring

/-- **`Ntrunc` is the quadratic form of its integer coefficients.** -/
theorem Ntrunc_eq (a : Fin 48) (w : Fin 24) (x : CuspE3) (s : ℝ) :
    Ntrunc a w x s = (Qt a w : ℝ) * qsq x s + ∑ j : Fin 3, (Lt a w j : ℝ) * x j + (Kt a w : ℝ) := by
  simp only [Ntrunc, chartVec_eq, Qt, Lt, Kt, tSum, Cl, Cq, Ck, Fin.sum_univ_four,
    Fin.sum_univ_three, Fin.isValue, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.vecHead, Matrix.vecTail, Function.comp_apply]
  push_cast
  ring

/-! ## The certificates

Each constraint is `H = c · q² + ∑ l_j x_j + e` with integer `c, l, e`; the sign of `c` decides
which of the three bounds below applies.  All three are integer expressions, so the finite
verification is a `decide` over `Fin 48 × Fin 24` (and `Fin 48`). -/

/-- `c > 0`: the certificate `121 c² + 100 c e - 25 ∑ l_j²` of the bound `c(11/10)² + e - ∑l²/(4c)`
(cleared of denominators). -/
def certPos (c e : ℤ) (l : Fin 3 → ℤ) : ℤ := 121 * c ^ 2 + 100 * c * e - 25 * (∑ j : Fin 3, l j ^ 2)

/-- `c = 0`: the minimum `e + ∑ min l_j 0 + ∑ l_j (corner a j)` of the affine function on the box. -/
def certZero (e : ℤ) (l : Fin 3 → ℤ) (lc : Fin 3 → ℤ) : ℤ :=
  e + ∑ j : Fin 3, min (l j) 0 + ∑ j : Fin 3, l j * lc j

/-- `c < 0`: twice the minimum `∑ min μ_j 0 + c ∑ lc_j² + ∑ l_j lc_j + 3c/2 + e` of the affine
value at the ceiling (`μ_j = 2c(lc_j + 1/2) + l_j`). -/
def certNeg (c e : ℤ) (l lc : Fin 3 → ℤ) : ℤ :=
  2 * (∑ j : Fin 3, min (2 * c * lc j + c + l j) 0) + 2 * c * (∑ j : Fin 3, lc j ^ 2)
    + 2 * (∑ j : Fin 3, l j * lc j) + 3 * c + 2 * e

/-- The certificate of a side constraint. -/
def certS (a : Fin 48) (S : Fin 24) : ℤ :=
  let c := Qs a S
  let l := Ls a S
  let e := Ks a S
  if 0 < c then certPos c e l
  else if c = 0 then certZero e l (Work.Cusp.cubeCorner a)
  else certNeg c e l (Work.Cusp.cubeCorner a)

/-- The certificate of a truncation constraint. -/
def certT (a : Fin 48) (w : Fin 24) : ℤ :=
  let c := Qt a w
  let l := Lt a w
  let e := Kt a w
  if 0 < c then certPos c e l
  else if c = 0 then certZero e l (Work.Cusp.cubeCorner a)
  else certNeg c e l (Work.Cusp.cubeCorner a)

/-- The certificate of the positivity of the fourth chart coordinate. -/
def cert4 (a : Fin 48) : ℤ := certPos (Cq a 4) (Ck a 4) (Cl a 4)

/-- The fourth chart coordinate is strictly positive: its certificate is. -/
theorem cert4_pos : ∀ a : Fin 48, 0 < cert4 a := by decide

/-- The quadratic coefficient of the fourth chart coordinate is positive. -/
theorem Cq4_pos : ∀ a : Fin 48, 0 < Cq a 4 := by decide

/-- Every side certificate is nonnegative. -/
theorem certS_nonneg : ∀ (a : Fin 48) (S : Fin 24), 0 ≤ certS a S := by decide

/-- Every truncation certificate is nonnegative. -/
theorem certT_nonneg : ∀ (a : Fin 48) (w : Fin 24), 0 ≤ certT a w := by decide

/-! ## The bounds -/

/-- The vertex bound of a one-variable quadratic with positive leading coefficient. -/
theorem quad_vertex {c l t : ℝ} (hc : 0 < c) : - (l ^ 2 / (4 * c)) ≤ c * t ^ 2 + l * t := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have h : c * t ^ 2 + l * t + l ^ 2 / (4 * c) = c * (t + l / (2 * c)) ^ 2 := by
    field_simp
    ring
  have h2 : 0 ≤ c * (t + l / (2 * c)) ^ 2 := mul_nonneg hc.le (sq_nonneg _)
  linarith [h, h2]

/-- **The `c > 0` bound.**  `H = c q² + ∑ l_j x_j + e ≥ c(11/10)² + e - ∑ l_j²/(4c)` for
`s ≥ 11/10`, written with the denominators cleared. -/
theorem quad_bound_pos {c e : ℝ} {l : Fin 3 → ℝ} (hc : 0 < c) (x : CuspE3) (s : ℝ)
    (hs : 11/10 ≤ s) :
    (4 * c * (c * (11/10)^2 + e) - ∑ j : Fin 3, (l j)^2) / (4 * c)
      ≤ c * qsq x s + ∑ j : Fin 3, l j * x j + e := by
  have hc0 : c ≠ 0 := ne_of_gt hc
  have h1 : (11/10 : ℝ)^2 ≤ s^2 := by nlinarith
  have hb : ∀ j : Fin 3, - ((l j)^2/(4*c)) ≤ c * x j^2 + l j * x j := fun j => quad_vertex hc
  have hs' : ∑ j : Fin 3, - ((l j)^2/(4*c)) ≤ ∑ j : Fin 3, (c * x j^2 + l j * x j) :=
    Finset.sum_le_sum fun j _ => hb j
  have h2 : c * (11/10)^2 ≤ c * s^2 := mul_le_mul_of_nonneg_left h1 hc.le
  have heq : c * (11/10)^2 + e - ∑ j : Fin 3, (l j)^2/(4*c)
      = (4 * c * (c * (11/10)^2 + e) - ∑ j : Fin 3, (l j)^2) / (4*c) := by
    simp only [Fin.sum_univ_three]
    field_simp
  simp only [qsq, Fin.sum_univ_three] at hs' heq ⊢
  linarith [hs', h2, heq]

/-- The `c > 0` bound, nonnegative form. -/
theorem quad_nonneg_of_pos {c e : ℝ} {l : Fin 3 → ℝ} (hc : 0 < c)
    (hcert : 0 ≤ 4 * c * (c * (11/10)^2 + e) - ∑ j : Fin 3, (l j)^2) :
    ∀ x : CuspE3, ∀ s : ℝ, 11/10 ≤ s → 0 ≤ c * qsq x s + ∑ j : Fin 3, l j * x j + e :=
  fun x s hs => le_trans (div_nonneg hcert (by linarith)) (quad_bound_pos hc x s hs)

/-- The `c > 0` bound, strictly positive form. -/
theorem quad_pos_of_pos {c e : ℝ} {l : Fin 3 → ℝ} (hc : 0 < c)
    (hcert : 0 < 4 * c * (c * (11/10)^2 + e) - ∑ j : Fin 3, (l j)^2) :
    ∀ x : CuspE3, ∀ s : ℝ, 11/10 ≤ s → 0 < c * qsq x s + ∑ j : Fin 3, l j * x j + e :=
  fun x s hs => lt_of_lt_of_le (div_pos hcert (by linarith)) (quad_bound_pos hc x s hs)

/-- `min lam 0 ≤ lam * t` for `t ∈ [0,1]`. -/
theorem min_le_mul (lam t : ℝ) (h0 : 0 ≤ t) (h1 : t ≤ 1) : min lam 0 ≤ lam * t := by
  rcases le_total lam 0 with h | h
  · rw [min_eq_left h]; nlinarith
  · rw [min_eq_right h]; exact mul_nonneg h h0

/-- **The `c = 0` bound.**  An affine function on the cube is bounded by its minimum
`e + ∑ min l_j 0 + ∑ l_j corner_j`. -/
theorem affine_nonneg {e : ℝ} {l : Fin 3 → ℝ} {lc : Fin 3 → ℝ}
    (hcert : 0 ≤ e + ∑ j : Fin 3, min (l j) 0 + ∑ j : Fin 3, l j * lc j) :
    ∀ x : CuspE3, (∀ j, lc j ≤ x j ∧ x j ≤ lc j + 1) →
      0 ≤ ∑ j : Fin 3, l j * x j + e := by
  intro x hx
  have hb : ∀ j : Fin 3, min (l j) 0 ≤ l j * (x j - lc j) :=
    fun j => min_le_mul _ _ (by linarith [(hx j).1]) (by linarith [(hx j).2])
  have hs' : ∑ j : Fin 3, min (l j) 0 ≤ ∑ j : Fin 3, l j * (x j - lc j) :=
    Finset.sum_le_sum fun j _ => hb j
  simp only [Fin.sum_univ_three] at hs' hcert ⊢
  linarith [hs', hcert]

/-- **The `c < 0` bound.**  On the region below the ceiling, `H ≥ H (x, ceilH a x)`, whose value is
affine in `x` and bounded by `certNeg`; this is the nonnegative form. -/
theorem ceiling_nonneg {c e : ℝ} {l : Fin 3 → ℝ} {lc : Fin 3 → ℝ} (hc : c ≤ 0)
    (hcert : 0 ≤ (∑ j : Fin 3, min (2*c*(lc j + 1/2) + l j) 0) + c * (∑ j : Fin 3, (lc j)^2)
        + (∑ j : Fin 3, l j * lc j) + 3*c/2 + e) :
    ∀ x : CuspE3, (∀ j, lc j ≤ x j ∧ x j ≤ lc j + 1) → ∀ s : ℝ,
      s^2 ≤ 9/4 - ∑ j : Fin 3, (x j - (lc j + 1/2))^2 →
      0 ≤ c * qsq x s + ∑ j : Fin 3, l j * x j + e := by
  intro x hx s hs
  have hcs : c * (9/4 - ∑ j : Fin 3, (x j - (lc j + 1/2))^2) ≤ c * s^2 := by nlinarith [hc]
  have hb : ∀ j : Fin 3, min (2*c*(lc j + 1/2) + l j) 0 ≤ (2*c*(lc j + 1/2) + l j) * (x j - lc j) :=
    fun j => min_le_mul _ _ (by linarith [(hx j).1]) (by linarith [(hx j).2])
  have hs' : ∑ j : Fin 3, min (2*c*(lc j + 1/2) + l j) 0
      ≤ ∑ j : Fin 3, (2*c*(lc j + 1/2) + l j) * (x j - lc j) :=
    Finset.sum_le_sum fun j _ => hb j
  have hid : c * (∑ j : Fin 3, x j^2 + (9/4 - ∑ j : Fin 3, (x j - (lc j + 1/2))^2)) + ∑ j : Fin 3, l j * x j + e
      = ∑ j : Fin 3, (2*c*(lc j + 1/2) + l j) * x j
        + (9*c/4 - c * ∑ j : Fin 3, (lc j + 1/2)^2 + e) := by
    simp only [Fin.sum_univ_three]
    ring
  have hid2 : ∑ j : Fin 3, (2*c*(lc j + 1/2) + l j) * lc j
      + (9*c/4 - c * ∑ j : Fin 3, (lc j + 1/2)^2 + e)
      = c * (∑ j : Fin 3, (lc j)^2) + (∑ j : Fin 3, l j * lc j) + 3*c/2 + e := by
    simp only [Fin.sum_univ_three]
    ring
  simp only [qsq, Fin.sum_univ_three] at hs' hid hid2 hcert hcs ⊢
  linarith [hs', hid, hid2, hcert, hcs]

/-! ### The certificates as real inequalities -/

/-- A nonnegative `certPos` is the `c > 0` certificate. -/
theorem certPos_bound {c e : ℤ} {l : Fin 3 → ℤ} (h : 0 ≤ certPos c e l) :
    0 ≤ 4 * (c:ℝ) * ((c:ℝ) * (11/10)^2 + (e:ℝ)) - ∑ j : Fin 3, ((l j : ℝ))^2 := by
  have heq : 4 * (c:ℝ) * ((c:ℝ) * (11/10)^2 + (e:ℝ)) - ∑ j : Fin 3, ((l j : ℝ))^2
      = ((certPos c e l : ℤ) : ℝ) / 25 := by
    simp only [certPos, Fin.sum_univ_three]
    push_cast
    ring
  rw [heq]
  exact div_nonneg (by exact_mod_cast h) (by norm_num)

/-- A positive `certPos` is the strict `c > 0` certificate. -/
theorem certPos_bound_pos {c e : ℤ} {l : Fin 3 → ℤ} (h : 0 < certPos c e l) :
    0 < 4 * (c:ℝ) * ((c:ℝ) * (11/10)^2 + (e:ℝ)) - ∑ j : Fin 3, ((l j : ℝ))^2 := by
  have heq : 4 * (c:ℝ) * ((c:ℝ) * (11/10)^2 + (e:ℝ)) - ∑ j : Fin 3, ((l j : ℝ))^2
      = ((certPos c e l : ℤ) : ℝ) / 25 := by
    simp only [certPos, Fin.sum_univ_three]
    push_cast
    ring
  rw [heq]
  exact div_pos (by exact_mod_cast h) (by norm_num)

/-- A nonnegative `certZero` is the `c = 0` certificate. -/
theorem certZero_bound {e : ℤ} {l lc : Fin 3 → ℤ} (h : 0 ≤ certZero e l lc) :
    0 ≤ (e:ℝ) + ∑ j : Fin 3, min ((l j : ℝ)) 0 + ∑ j : Fin 3, (l j : ℝ) * (lc j : ℝ) := by
  have heq : ((certZero e l lc : ℤ) : ℝ)
      = (e:ℝ) + ∑ j : Fin 3, min ((l j : ℝ)) 0 + ∑ j : Fin 3, (l j : ℝ) * (lc j : ℝ) := by
    simp only [certZero]
    push_cast
    ring
  rw [← heq]
  exact_mod_cast h

/-- A nonnegative `certNeg` is the `c < 0` certificate. -/
theorem certNeg_bound {c e : ℤ} {l lc : Fin 3 → ℤ} (h : 0 ≤ certNeg c e l lc) :
    0 ≤ (∑ j : Fin 3, min (2*(c:ℝ)*((lc j : ℝ) + 1/2) + (l j : ℝ)) 0)
        + (c:ℝ) * (∑ j : Fin 3, (lc j : ℝ)^2) + (∑ j : Fin 3, (l j : ℝ) * (lc j : ℝ))
        + 3*(c:ℝ)/2 + (e:ℝ) := by
  have heq : ((certNeg c e l lc : ℤ) : ℝ) / 2
      = (∑ j : Fin 3, min (2*(c:ℝ)*((lc j : ℝ) + 1/2) + (l j : ℝ)) 0)
        + (c:ℝ) * (∑ j : Fin 3, (lc j : ℝ)^2) + (∑ j : Fin 3, (l j : ℝ) * (lc j : ℝ))
        + 3*(c:ℝ)/2 + (e:ℝ) := by
    have harg : ∀ j : Fin 3, (2 * (c:ℝ) * (lc j : ℝ) + (c:ℝ) + (l j : ℝ))
        = 2*(c:ℝ)*((lc j : ℝ) + 1/2) + (l j : ℝ) := fun j => by ring
    simp only [certNeg, Fin.sum_univ_three]
    push_cast
    rw [harg 0, harg 1, harg 2]
    ring
  rw [← heq]
  exact div_nonneg (by exact_mod_cast h) (by norm_num)

/-! ## The ceiling relation -/

/-- The square of the ceiling is the hemisphere equation: `ceilH a x² = 9/4 - ∑ (x_j - c_j - 1/2)²`
where `c_j` is the lower corner of the cube. -/
theorem ceilH_sq (a : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) :
    ceilH a x ^ 2 = 9/4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1/2))^2 := by
  have hR : 0 ≤ 9/4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1/2))^2 := by
    have h : ∀ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1/2))^2 ≤ 1/4 := by
      intro j
      have hj := hx j
      nlinarith [hj.1, hj.2]
    have hs : ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1/2))^2 ≤ 3/4 := by
      calc ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1/2))^2
          ≤ ∑ _j : Fin 3, (1/4 : ℝ) := Finset.sum_le_sum fun j _ => h j
        _ = 3/4 := by norm_num [Fin.sum_univ_three]
    linarith
  rw [ceilH, Real.sq_sqrt hR]

/-- **The height bound below the ceiling**: `s ≤ ceilH a x` and `s ≥ 0` give
`s² ≤ 9/4 - ∑ (x_j - c_j - 1/2)²`. -/
theorem sq_le_ceiling (a : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) {s : ℝ}
    (hs1 : 11/10 ≤ s) (hs2 : s ≤ ceilH a x) :
    s^2 ≤ 9/4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1/2))^2 := by
  have hsq : ceilH a x ^ 2 = 9/4 - ∑ j : Fin 3, (x j - ((Work.Cusp.cubeCorner a j : ℝ) + 1/2))^2 :=
    ceilH_sq a hx
  have hnn : 0 ≤ ceilH a x := by rw [ceilH]; exact Real.sqrt_nonneg _
  have hs2' : s ^ 2 ≤ ceilH a x ^ 2 := by nlinarith [hs1, hs2, hnn]
  rwa [hsq] at hs2'

/-! ## The three positivity statements on the region -/

/-- **The fourth chart coordinate is positive on the region.** -/
theorem chartVec4_pos (a : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) {s : ℝ}
    (hs1 : 11/10 ≤ s) : 0 < chartVec a x s 4 := by
  rw [chartVec_eq]
  have hc : 0 < (Cq a 4 : ℝ) := by exact_mod_cast Cq4_pos a
  exact quad_pos_of_pos hc (certPos_bound_pos (cert4_pos a)) x s hs1

/-- **The side constraints hold.** -/
theorem Nside_nonneg (a : Fin 48) (S : Fin 24) {x : CuspE3} (hx : x ∈ cubeBox a) {s : ℝ}
    (hs1 : 11/10 ≤ s) (hs2 : s ≤ ceilH a x) : 0 ≤ Nside a S x s := by
  have hx' : ∀ j : Fin 3, ((Work.Cusp.cubeCorner a j : ℝ)) ≤ x j
      ∧ x j ≤ ((Work.Cusp.cubeCorner a j : ℝ)) + 1 := hx
  have hcert := certS_nonneg a S
  rw [Nside_eq]
  by_cases hc : 0 < Qs a S
  · have hcert' : 0 ≤ certPos (Qs a S) (Ks a S) (Ls a S) := by
      rw [certS] at hcert
      rw [if_pos hc] at hcert
      exact hcert
    exact quad_nonneg_of_pos (by exact_mod_cast hc) (certPos_bound hcert') x s hs1
  · by_cases hc0 : Qs a S = 0
    · have hcert' : 0 ≤ certZero (Ks a S) (Ls a S) (Work.Cusp.cubeCorner a) := by
        rw [certS] at hcert
        rw [if_neg hc, if_pos hc0] at hcert
        exact hcert
      have h0 : ((Qs a S : ℤ) : ℝ) = 0 := by rw [hc0]; norm_num
      rw [h0, zero_mul, zero_add]
      exact affine_nonneg (certZero_bound hcert') x hx'
    · have hclt : Qs a S < 0 := lt_of_le_of_ne (le_of_not_gt hc) hc0
      have hcert' : 0 ≤ certNeg (Qs a S) (Ks a S) (Ls a S) (Work.Cusp.cubeCorner a) := by
        rw [certS] at hcert
        rw [if_neg hc, if_neg hc0] at hcert
        exact hcert
      exact ceiling_nonneg (by exact_mod_cast hclt.le) (certNeg_bound hcert')
        x hx' s (sq_le_ceiling a hx hs1 hs2)

/-- **The truncation constraints hold.** -/
theorem Ntrunc_nonneg (a : Fin 48) (w : Fin 24) {x : CuspE3} (hx : x ∈ cubeBox a) {s : ℝ}
    (hs1 : 11/10 ≤ s) (hs2 : s ≤ ceilH a x) : 0 ≤ Ntrunc a w x s := by
  have hx' : ∀ j : Fin 3, ((Work.Cusp.cubeCorner a j : ℝ)) ≤ x j
      ∧ x j ≤ ((Work.Cusp.cubeCorner a j : ℝ)) + 1 := hx
  have hcert := certT_nonneg a w
  rw [Ntrunc_eq]
  by_cases hc : 0 < Qt a w
  · have hcert' : 0 ≤ certPos (Qt a w) (Kt a w) (Lt a w) := by
      rw [certT] at hcert
      rw [if_pos hc] at hcert
      exact hcert
    exact quad_nonneg_of_pos (by exact_mod_cast hc) (certPos_bound hcert') x s hs1
  · by_cases hc0 : Qt a w = 0
    · have hcert' : 0 ≤ certZero (Kt a w) (Lt a w) (Work.Cusp.cubeCorner a) := by
        rw [certT] at hcert
        rw [if_neg hc, if_pos hc0] at hcert
        exact hcert
      have h0 : ((Qt a w : ℤ) : ℝ) = 0 := by rw [hc0]; norm_num
      rw [h0, zero_mul, zero_add]
      exact affine_nonneg (certZero_bound hcert') x hx'
    · have hclt : Qt a w < 0 := lt_of_le_of_ne (le_of_not_gt hc) hc0
      have hcert' : 0 ≤ certNeg (Qt a w) (Kt a w) (Lt a w) (Work.Cusp.cubeCorner a) := by
        rw [certT] at hcert
        rw [if_neg hc, if_neg hc0] at hcert
        exact hcert
      exact ceiling_nonneg (by exact_mod_cast hclt.le) (certNeg_bound hcert')
        x hx' s (sq_le_ceiling a hx hs1 hs2)

/-! ## The theorem -/

end chartKleinMem

open chartKleinMem

theorem chartKlein_mem (a : Fin 48) {x : Work.RTOwed.CuspE3}
    (hx : x ∈ Work.RTOwed.cubeBox a) {s : ℝ} (hs1 : 11 / 10 ≤ s)
    (hs2 : s ≤ Work.RTOwed.ceilH a x) :
    Work.RTOwed.chartKlein a (Work.RTOwed.mkE4 x s) ∈ Work.FoldInst.Qbar := by
  have hs0 : s ≠ 0 := by linarith
  have h4 : 0 < chartVec a x s 4 := chartVec4_pos a hx hs1
  refine ⟨fun S => ?_, fun w => ?_⟩
  · rw [sideSlack_eq a S x s hs0 h4.ne']
    exact div_nonneg (Nside_nonneg a S hx hs1 hs2) h4.le
  · rw [truncSlack_eq a w x s hs0 h4.ne']
    exact div_nonneg (Ntrunc_nonneg a w hx hs1 hs2) (by linarith)

end Work.RTOwed
