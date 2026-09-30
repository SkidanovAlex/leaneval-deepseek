/-
# The self-facet certificate of a cusp cube (`Work.RTOwed.chartKlein_self_facet`)

For a cube `a : Fin 48` of the cusp development, a point `x` of its closed unit cube `cubeBox a` and
a height `s ≥ 11/10`, the *truncation* constraint of the ideal vertex `cubeVert a` holds at the
chart point `chartKlein a (mkE4 x s)` exactly when `s` is at most the ceiling `ceilH a x`:

  `0 ≤ truncSlack (cubeVert a) (chartKlein a (mkE4 x s)) ↔ s ≤ ceilH a x`.

## Method

Write `V = chartVec a x s = chartMat a *ᵥ uhsVec x s = 2 s · (chartMat a *ᵥ hypOfUHS (mkE4 x s))`.
The chart point is `kleinOfHyp` of `V`, so its coordinates are `V i / V 4` (`i < 4`), and the
truncation slack of `w` is

  `truncSlack w (chartKlein a (mkE4 x s)) = Ntrunc a w x s / (10 · V 4)`

(`truncSlack_eq`), the denominator `10 V 4` being positive for `s ≥ 11/10` (`chartVec4_pos`).  So
the constraint is the sign of the numerator

  `Ntrunc a w x s = c · q² + ∑_j l_j x_j + e`,  `q² = ∑_j x_j² + s²`,  `c = Qt a w`,
  `l = Lt a w`, `e = Kt a w`

with *integer* coefficients (`Ntrunc_eq`).

The three finite checks over the 48 cubes (`qtVert_neg`, `ltVert_eq`, `ktVert_eq`, proved by
`decide`) are the algebraic content of the certificate:

* `qtVert_neg`: the quadratic coefficient of the constraint of the cube's own ideal vertex is
  negative, i.e. the chart point leaves the truncation half space as `s` grows;
* `ltVert_eq`, `ktVert_eq`: the linear and constant coefficients are those of the hemisphere of
  radius `3/2` centred at the centre `cubeCorner a + (1/2,1/2,1/2)` of the cube:
  `l_j + c (2 lc_j + 1) = 0` and `4 e + 9 c - c ∑_j (2 lc_j + 1)² = 0` for `lc = cubeCorner a`.

By the polynomial identity `quadForm_ceiling_id` and the ceiling relation `ceilH_sq` this gives

  `Ntrunc a (cubeVert a) x s = Qt a (cubeVert a) · (s² - ceilH a x²)`

(`ntruncVert_eq`).  Since `Qt a (cubeVert a) < 0`, this numerator is nonnegative exactly when
`s² ≤ ceilH a x²`, which for `s ≥ 11/10 > 0` and `ceilH a x ≥ 0` is `s ≤ ceilH a x`.

## Why the chart-vector layer is copied here

The lemmas below are a verbatim copy of the chart-vector layer of
`Submission/Work/RTOwed/chartKlein_mem.lean` (`Work.RTOwed.chartKleinMem.*`), placed in the
private namespace `Work.RTOwed.SelfFacet` so that this file depends only on the *definition* layer
`Submission.Work.RTOwed.cuspChart` (the matrices `chartMat` of `cuspChartData.lean`, the cube data
of `Work.Cusp.Data`, and the maps `chartKlein`, `mkE4`, `ceilH`, `cubeBox`).  Nothing mathematical
is changed by the copy: the proofs are the same, only the ambient namespace differs.
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

noncomputable section

open scoped Matrix BigOperators
open Set Topology Function

namespace Work.RTOwed

/- The chart-vector layer of the certificate `chartKlein_self_facet` (a private copy of the
auxiliary lemmas of `Submission/Work/RTOwed/chartKlein_mem.lean`). -/
namespace SelfFacet

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

/-- The numerator `8 V 4 - 5 ∑_i t_{w,i} V i` of `truncSlack w` on the chart of the cube. -/
def Ntrunc (a : Fin 48) (w : Fin 24) (x : CuspE3) (s : ℝ) : ℝ :=
  8 * chartVec a x s 4 - 5 * ((Work.FoldInst.truncNormal2 w 0 : ℝ) * chartVec a x s 0
    + (Work.FoldInst.truncNormal2 w 1 : ℝ) * chartVec a x s 1
    + (Work.FoldInst.truncNormal2 w 2 : ℝ) * chartVec a x s 2
    + (Work.FoldInst.truncNormal2 w 3 : ℝ) * chartVec a x s 3)

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

/-- `∑_i t_{w,i} f i`. -/
def tSum (w : Fin 24) (f : Fin 4 → ℤ) : ℤ := ∑ i : Fin 4, Work.FoldInst.truncNormal2 w i * f i

/-- The quadratic coefficient of `Ntrunc a w`. -/
def Qt (a : Fin 48) (w : Fin 24) : ℤ := 8 * Cq a 4 - 5 * tSum w (fun i => Cq a i.castSucc)

/-- The linear coefficients of `Ntrunc a w`. -/
def Lt (a : Fin 48) (w : Fin 24) : Fin 3 → ℤ :=
  fun j => 8 * Cl a 4 j - 5 * tSum w (fun i => Cl a i.castSucc j)

/-- The constant of `Ntrunc a w`. -/
def Kt (a : Fin 48) (w : Fin 24) : ℤ := 8 * Ck a 4 - 5 * tSum w (fun i => Ck a i.castSucc)

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

/-- The certificate of the positivity of the fourth chart coordinate. -/
def cert4 (a : Fin 48) : ℤ := certPos (Cq a 4) (Ck a 4) (Cl a 4)

/-- The fourth chart coordinate is strictly positive: its certificate is. -/
theorem cert4_pos : ∀ a : Fin 48, 0 < cert4 a := by decide

/-- The quadratic coefficient of the fourth chart coordinate is positive. -/
theorem Cq4_pos : ∀ a : Fin 48, 0 < Cq a 4 := by decide

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

/-- The `c > 0` bound, strictly positive form. -/
theorem quad_pos_of_pos {c e : ℝ} {l : Fin 3 → ℝ} (hc : 0 < c)
    (hcert : 0 < 4 * c * (c * (11/10)^2 + e) - ∑ j : Fin 3, (l j)^2) :
    ∀ x : CuspE3, ∀ s : ℝ, 11/10 ≤ s → 0 < c * qsq x s + ∑ j : Fin 3, l j * x j + e :=
  fun x s hs => lt_of_lt_of_le (div_pos hcert (by linarith)) (quad_bound_pos hc x s hs)

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

/-! ## The three positivity statements on the region -/
/-- **The fourth chart coordinate is positive on the region.** -/
theorem chartVec4_pos (a : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) {s : ℝ}
    (hs1 : 11/10 ≤ s) : 0 < chartVec a x s 4 := by
  rw [chartVec_eq]
  have hc : 0 < (Cq a 4 : ℝ) := by exact_mod_cast Cq4_pos a
  exact quad_pos_of_pos hc (certPos_bound_pos (cert4_pos a)) x s hs1

/-! ## The finite checks on the integer data of the truncation constraint -/

/-- **The quadratic coefficient is negative** at the cube's own ideal vertex. -/
theorem qtVert_neg : ∀ a : Fin 48, Qt a (cubeVert a) < 0 := by
  decide

/-- **The linear coefficients vanish against the centre of the cube**: `l_j + c (2 lc_j + 1) = 0`. -/
theorem ltVert_eq : ∀ (a : Fin 48) (j : Fin 3),
    Lt a (cubeVert a) j + Qt a (cubeVert a) * (2 * Work.Cusp.cubeCorner a j + 1) = 0 := by
  decide

/-- **The constant coefficient is that of the hemisphere** (cleared of denominators):
`4 e + 9 c - c ∑_j (2 lc_j + 1)² = 0`. -/
theorem ktVert_eq : ∀ a : Fin 48,
    4 * Kt a (cubeVert a) + 9 * Qt a (cubeVert a)
      - Qt a (cubeVert a) * (∑ j : Fin 3, (2 * Work.Cusp.cubeCorner a j + 1) ^ 2) = 0 := by
  decide

/-! ## The factorisation through the ceiling -/

/-- **The polynomial identity behind the ceiling.**  If the linear and constant coefficients of a
quadratic form satisfy the two relations `l_j + c (2 lc_j + 1) = 0` and
`e + 9c/4 - c ∑_j (lc_j + 1/2)² = 0`, and if `ch² = 9/4 - ∑_j (x_j - (lc_j + 1/2))²` is the
hemisphere of radius `3/2` over the centre `lc + 1/2`, then the form factors through the ceiling:

  `c · (∑_j x_j² + s²) + ∑_j l_j x_j + e = c (s² - ch²)`. -/
theorem quadForm_ceiling_id {c e : ℝ} {l lc : Fin 3 → ℝ} {x : CuspE3} {s ch : ℝ}
    (hl : ∀ j : Fin 3, l j + c * (2 * lc j + 1) = 0)
    (he : e + 9 / 4 * c - c * (∑ j : Fin 3, (lc j + 1 / 2) ^ 2) = 0)
    (hch : ch ^ 2 = 9 / 4 - ∑ j : Fin 3, (x j - (lc j + 1 / 2)) ^ 2) :
    c * qsq x s + ∑ j : Fin 3, l j * x j + e = c * (s ^ 2 - ch ^ 2) := by
  have hl' : ∀ j : Fin 3, l j = -c * (2 * lc j + 1) := fun j => by linarith [hl j]
  have he' : e = -9 / 4 * c + c * (∑ j : Fin 3, (lc j + 1 / 2) ^ 2) := by linarith [he]
  rw [hch, he']
  simp only [qsq, Fin.sum_univ_three, hl']
  ring

/-- **The numerator of the truncation constraint of the cube's own ideal vertex factors through the
ceiling**: `Ntrunc a (cubeVert a) x s = Qt a (cubeVert a) · (s² - ceilH a x²)`. -/
theorem ntruncVert_eq (a : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) (s : ℝ) :
    Ntrunc a (cubeVert a) x s
      = (Qt a (cubeVert a) : ℝ) * (s ^ 2 - (ceilH a x) ^ 2) := by
  rw [Ntrunc_eq]
  refine quadForm_ceiling_id (c := (Qt a (cubeVert a) : ℝ)) (e := (Kt a (cubeVert a) : ℝ))
    (l := fun j => (Lt a (cubeVert a) j : ℝ)) (lc := fun j => (Work.Cusp.cubeCorner a j : ℝ))
    (x := x) (s := s) (ch := ceilH a x) ?_ ?_ (ceilH_sq a hx)
  · intro j
    have h := congrArg (fun z : ℤ => (z : ℝ)) (ltVert_eq a j)
    push_cast at h
    linarith
  · have h := congrArg (fun z : ℤ => (z : ℝ)) (ktVert_eq a)
    push_cast at h
    have hsq : (∑ j : Fin 3, (2 * (Work.Cusp.cubeCorner a j : ℝ) + 1) ^ 2)
        = 4 * ∑ j : Fin 3, ((Work.Cusp.cubeCorner a j : ℝ) + 1 / 2) ^ 2 := by
      simp only [Fin.sum_univ_three]
      ring
    have key : (Qt a (cubeVert a) : ℝ)
          * (∑ j : Fin 3, ((Work.Cusp.cubeCorner a j : ℝ) + 1 / 2) ^ 2)
        = (Qt a (cubeVert a) : ℝ)
          * (∑ j : Fin 3, (2 * (Work.Cusp.cubeCorner a j : ℝ) + 1) ^ 2) / 4 := by
      rw [hsq]
      ring
    rw [key]
    linarith

end SelfFacet

open SelfFacet

/-! ## The certificate -/

theorem chartKlein_self_facet (a : Fin 48) {x : Work.RTOwed.CuspE3}
    (hx : x ∈ Work.RTOwed.cubeBox a) {s : ℝ} (hs1 : 11 / 10 ≤ s) :
    0 ≤ Work.FoldInst.truncSlack (Work.RTOwed.cubeVert a)
        (Work.RTOwed.chartKlein a (Work.RTOwed.mkE4 x s)) ↔
      s ≤ Work.RTOwed.ceilH a x := by
  have hs0 : s ≠ 0 := by linarith
  have hV4 : 0 < chartVec a x s 4 := chartVec4_pos a hx hs1
  have hD : 0 < 10 * chartVec a x s 4 := by linarith
  have hsl : Work.FoldInst.truncSlack (cubeVert a) (chartKlein a (mkE4 x s))
      = Ntrunc a (cubeVert a) x s / (10 * chartVec a x s 4) :=
    truncSlack_eq a (cubeVert a) x s hs0 hV4.ne'
  have hQt : (Qt a (cubeVert a) : ℝ) < 0 := by exact_mod_cast qtVert_neg a
  have hfac : Ntrunc a (cubeVert a) x s
      = (Qt a (cubeVert a) : ℝ) * (s ^ 2 - (ceilH a x) ^ 2) := ntruncVert_eq a hx s
  have hch0 : 0 ≤ ceilH a x := Real.sqrt_nonneg _
  constructor
  · intro h
    rw [hsl] at h
    have hN : 0 ≤ Ntrunc a (cubeVert a) x s := by
      by_contra hlt
      rw [not_le] at hlt
      have := div_neg_of_neg_of_pos hlt hD
      linarith
    rw [hfac] at hN
    have h3 : s ^ 2 ≤ (ceilH a x) ^ 2 := by
      by_contra hlt
      rw [not_le] at hlt
      have hpos : 0 < s ^ 2 - (ceilH a x) ^ 2 := sub_pos.mpr hlt
      have := mul_neg_of_neg_of_pos hQt hpos
      linarith
    have habs : |s| ≤ |ceilH a x| := sq_le_sq.mp h3
    rw [abs_of_pos (by linarith : 0 < s), abs_of_nonneg hch0] at habs
    exact habs
  · intro hle
    have hsnn : 0 ≤ s := by linarith
    have h3 : s ^ 2 ≤ (ceilH a x) ^ 2 :=
      sq_le_sq.mpr (by rw [abs_of_nonneg hsnn, abs_of_nonneg hch0]; exact hle)
    have hle0 : s ^ 2 - (ceilH a x) ^ 2 ≤ 0 := by linarith
    have hprod : 0 ≤ (Qt a (cubeVert a) : ℝ) * (s ^ 2 - (ceilH a x) ^ 2) :=
      mul_nonneg_of_nonpos_of_nonpos hQt.le hle0
    rw [hsl, hfac]
    exact div_nonneg hprod (by linarith)

end Work.RTOwed
