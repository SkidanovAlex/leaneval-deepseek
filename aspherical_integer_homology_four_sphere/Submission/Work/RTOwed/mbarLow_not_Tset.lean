import Mathlib
import Submission.Work.RTOwed.cuspChartBeta
import Submission.Work.RTOwed.cuspChartRegion
import Submission.Work.RTOwed.chartKlein_strict
import Submission.Work.RTOwed.chartKlein_self_facet
import Submission.Work.RTOwed.mk_injOn_interior
import Submission.Work.RTOwed.chartKlein_wall
import Submission.Work.RTOwed.cuspCertWalls
import Submission.Work.FoldInst.Quotient
import Submission.Work.Cusp.Assembly
import Submission.Work.Cusp.TopBox

-- Lean v4.35.0-rc3 / Mathlib 5e0c4e5 made `isDefEq` respect transparency when unifying instances; with it,
-- `ZMod.instField` and `ZMod.commRing` (and `Neg (ZMod p)` via `SubtractionMonoid`) no longer unify, which
-- breaks `ring`/`rw`/module-instance search on `ZMod p`. Restore the v4.34 behaviour for this file.
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false


noncomputable section

open Set Topology Function
open scoped BigOperators

set_option maxHeartbeats 4000000

namespace Work.RTOwed

/-! ## The two finite certificates on the *closed* cube

`chartKlein_strict` proves the strict positivity of every slack of the cube chart for `x` in the
*open* cube (`ckK_one_pos`), and the non-negativity at the ceiling for `x` in the closed cube
(`ckBnd2_nonneg`).  The chart `mbarLow` however evaluates the cube chart at the *reduced* coordinate
`redV v (uhsXj q)`, which lies in the *half open* cube `[c, c+1)³`: the lower walls of the cube are
attained.  On the walls the slacks of the *sides* vanish (this is what makes the chart a chart), but
the truncation slacks stay strictly positive, as the two certificates below show:

* `ckBnd_trunc_pos`: at `σ = 1` the lower bound `ckBnd` of the truncation numerators is positive
  for *every* point of the closed cube — so the numerators are strictly positive there;
* `ckBnd2_trunc_pos`: at `σ = (ceilH a x)²` the lower bound `ckBnd2` is positive for every closed
  cube point and every truncation constraint *other than* the cube's own ideal vertex `cubeVert a`
  (for the own vertex the numerator vanishes exactly on the ceiling).

Both are finite verifications over `Fin 48 × Fin 24` by `decide` (integer arithmetic). -/

/-- **Certificate at `σ = 1` for the truncation constraints**: the lower bound is positive on the
closed cube. -/
theorem ckBnd_trunc_pos : ∀ (a : Fin 48) (w : Fin 24), 0 < ckBnd a (ckOfTrunc w) := by
  decide

/-- **Certificate at the ceiling for the truncation constraints**: for every constraint other than
the cube's own ideal vertex the affine lower bound at `σ = (ceilH a x)²` is positive. -/
theorem ckBnd2_trunc_pos :
    ∀ (a : Fin 48) (w : Fin 24), w ≠ cubeVert a → 0 < ckBnd2 a (ckOfTrunc w) := by
  decide

/-! ## Strict positivity of the truncation numerators -/

/-- **Strict positivity of the truncation numerator at `σ = 1`**, on the closed cube. -/
theorem ckK_one_pos_closed (a : Fin 48) (w : Fin 24) {x : CuspE3} (hx : x ∈ cubeBox a) :
    0 < ckK (ckOfTrunc w) (ckQ a x 1) := by
  have h := ckBnd_le_ten a (ckOfTrunc w) hx
  have hpos : (0 : ℝ) < (ckBnd a (ckOfTrunc w) : ℝ) := by
    exact_mod_cast ckBnd_trunc_pos a w
  linarith

/-- **Strict positivity of the truncation numerator at the ceiling**, on the closed cube, for every
constraint other than the cube's own ideal vertex. -/
theorem ckK_two_pos_closed (a : Fin 48) (w : Fin 24) (hw : w ≠ cubeVert a) {x : CuspE3}
    (hx : x ∈ cubeBox a) :
    0 < ckK (ckOfTrunc w) (ckQ a x (ckS2 a x)) := by
  have ht : ∀ j : Fin 3, 0 ≤ x j - (Work.Cusp.cubeCorner a j : ℝ)
      ∧ x j - (Work.Cusp.cubeCorner a j : ℝ) ≤ 1 := by
    intro j
    have h := hx j
    constructor <;> linarith [h.1, h.2]
  have hsum := sum_ckDc a (ckOfTrunc w) x (ckS2 a x)
  have htw := twenty_ckK_two a (ckOfTrunc w) x
  have hcast : (ckBnd2 a (ckOfTrunc w) : ℝ)
      = (ckK2 a (ckOfTrunc w) : ℝ)
        + ∑ j : Fin 3, ((min (ckE2 a (ckOfTrunc w) j) 0 : ℤ) : ℝ) := by
    rw [ckBnd2]
    push_cast
    ring
  have h2 : (0 : ℝ) < (ckBnd2 a (ckOfTrunc w) : ℝ) := by
    exact_mod_cast ckBnd2_trunc_pos a w hw
  have hmin : (0 : ℝ) < (ckK2 a (ckOfTrunc w) : ℝ)
      + ∑ j : Fin 3, ((min (ckE2 a (ckOfTrunc w) j) 0 : ℤ) : ℝ) := by
    rw [← hcast]
    exact h2
  have hsplit : (∑ j : Fin 3, ((min (ckE2 a (ckOfTrunc w) j) 0 : ℤ) : ℝ))
      ≤ ∑ j : Fin 3, (ckE2 a (ckOfTrunc w) j : ℝ)
          * (x j - (Work.Cusp.cubeCorner a j : ℝ)) :=
    Finset.sum_le_sum fun j _ => intMin_le_mul _ _ (ht j).1 (ht j).2
  have hmain : 0 < 20 * ckK (ckOfTrunc w) (ckQ a x (ckS2 a x)) := by
    rw [hsum] at htw
    linarith [hmin, hsplit]
  linarith

/-- **Strict positivity of the truncation numerator for every `σ` between `1` and the ceiling**,
on the closed cube, for every constraint other than the cube's own ideal vertex.

The numerator is *affine* in `σ` (with slope `ckQ0`), so its minimum on the interval of the line
through the two end points `σ = 1` and `σ = (ceilH a x)²` is attained at an end point; both end
points give a strictly positive value (`ckK_one_pos_closed`, `ckK_two_pos_closed`). -/
theorem ckK_pos_of_le (a : Fin 48) (w : Fin 24) (hw : w ≠ cubeVert a) {x : CuspE3}
    (hx : x ∈ cubeBox a) {σ : ℝ} (hσ1 : 1 ≤ σ) (hσ2 : σ ≤ ckS2 a x) :
    0 < ckK (ckOfTrunc w) (ckQ a x σ) := by
  rcases eq_or_lt_of_le hσ2 with h | h
  · rw [h]
    exact ckK_two_pos_closed a w hw hx
  · have hden : 0 < ckS2 a x - 1 := by linarith
    set α := (ckS2 a x - σ) / (ckS2 a x - 1) with hα
    set β := (σ - 1) / (ckS2 a x - 1) with hβ
    have hαpos : 0 < α := by
      rw [hα]
      exact div_pos (by linarith) hden
    have hβnn : 0 ≤ β := by
      rw [hβ]
      exact div_nonneg (by linarith) hden.le
    have hαβ : α + β = 1 := by
      rw [hα, hβ]; field_simp; ring
    have hσeq : σ = α * 1 + β * (ckS2 a x) := by
      rw [hα, hβ]; field_simp; ring
    have hconv := ckQ_convex a x σ 1 (ckS2 a x) α β hαβ hσeq
    have hlin := ckK_linear (ckOfTrunc w) α β (ckQ a x 1) (ckQ a x (ckS2 a x))
    rw [hconv, hlin]
    have h1 := ckK_one_pos_closed a w hx
    have h2 := ckK_two_pos_closed a w hw hx
    nlinarith [hαpos, hβnn, h1, h2]

/-! ## The truncation slacks of the cube chart are non-zero below the ceiling -/

/-- **The numerator of the own truncation constraint is positive strictly below the ceiling.** -/
theorem truncSlack_self_pos (a : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) {s : ℝ}
    (hs1 : 11 / 10 ≤ s) (hs2 : s < ceilH a x) :
    0 < Work.FoldInst.truncSlack (cubeVert a) (chartKlein a (mkE4 x s)) := by
  have hs0 : s ≠ 0 := by linarith
  have hV4 : 0 < SelfFacet.chartVec a x s 4 := SelfFacet.chartVec4_pos a hx hs1
  have hD : 0 < 10 * SelfFacet.chartVec a x s 4 := by linarith
  have hsl := SelfFacet.truncSlack_eq a (cubeVert a) x s hs0 hV4.ne'
  have hQt : (SelfFacet.Qt a (cubeVert a) : ℝ) < 0 := by
    exact_mod_cast SelfFacet.qtVert_neg a
  have hfac := SelfFacet.ntruncVert_eq a hx s
  have hch : 0 ≤ ceilH a x := Real.sqrt_nonneg _
  have hlt : s ^ 2 < (ceilH a x) ^ 2 := by nlinarith
  have hnum : 0 < (SelfFacet.Qt a (cubeVert a) : ℝ) * (s ^ 2 - (ceilH a x) ^ 2) :=
    mul_pos_of_neg_of_neg hQt (by linarith)
  rw [hsl, hfac]
  exact div_pos hnum hD

/-- **No truncation slack of the cube chart vanishes strictly below the ceiling**, for `x` in the
closed cube and `s ∈ [11/10, ceilH a x)`. -/
theorem truncSlack_pos (a : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) {s : ℝ}
    (hs1 : 11 / 10 ≤ s) (hs2 : s < ceilH a x) :
    ∀ w : Fin 24, 0 < Work.FoldInst.truncSlack w (chartKlein a (mkE4 x s)) := by
  intro w
  by_cases hw : w = cubeVert a
  · rw [hw]
    exact truncSlack_self_pos a hx hs1 hs2
  · have hspos : 0 < s := by linarith
    have hch2 : (ceilH a x) ^ 2 = ckS2 a x := SelfFacet.ceilH_sq a hx
    have hσ1 : 1 ≤ s ^ 2 := by nlinarith
    have hσ2 : s ^ 2 ≤ ckS2 a x := by rw [← hch2]; nlinarith
    have hnum : 0 < ckK (ckOfTrunc w) (ckQ a x (s ^ 2)) := ckK_pos_of_le a w hw hx hσ1 hσ2
    have hchart : chartKlein a (mkE4 x s) = Work.HypModel.kleinOfHyp (ckQ a x (s ^ 2)) :=
      chartKlein_mkE4 a x s (ne_of_gt hspos)
    have h4 : 0 < (ckQ a x (s ^ 2)) 4 := ckQ_pos a hx hσ1
    have hnum' : 0 < ckNT w (ckQ a x (s ^ 2)) := by
      rwa [ckK_ofTrunc] at hnum
    rw [hchart, truncSlack_kleinOfHyp w (ckQ a x (s ^ 2)) (ne_of_gt h4)]
    exact div_pos hnum' h4

/-! ## The point of `X̄` below the ceiling is not in the truncation set -/

/-- **The point of `X̄` over a point strictly below the ceiling is not on a truncation facet.** -/
theorem xbarOf_not_mem_Xtrunc (a : Fin 48) {x : CuspE3} (hx : x ∈ cubeBox a) {s : ℝ}
    (hs1 : 11 / 10 ≤ s) (hs2 : s < ceilH a x)
    (hQ : chartKlein a (mkE4 x s) ∈ Work.FoldInst.Qbar) :
    xbarOf a (chartKlein a (mkE4 x s)) hQ ∉ Work.FoldInst.Xtrunc := by
  intro h
  obtain ⟨w, hw⟩ := h
  exact absurd hw (ne_of_gt (truncSlack_pos a hx hs1 hs2 w))

/-- **The truncation set is exactly the saturation of the truncation facets**: a point of `X̄` whose
`mk`-class is on `Tset` is already on a truncation facet (the relation `~₁` acts by the group `Gg`,
which permutes the truncation constraints). -/
theorem mk_xbarOf_not_mem_Tset {a : Fin 48} {y : CuspE4} {hy : y ∈ Work.FoldInst.Qbar}
    (h : xbarOf a y hy ∉ Work.FoldInst.Xtrunc) :
    Work.FoldInst.mk (xbarOf a y hy) ∉ Work.FoldInst.Tset := by
  intro hT
  obtain ⟨x, hx, hxy⟩ := hT
  have hrel : Work.FoldInst.rel x (xbarOf a y hy) := Quotient.exact hxy
  obtain ⟨γ, _hγ, hγx⟩ := hrel
  exact h (by rw [← hγx]; exact Work.FoldInst.actX_mem_Xtrunc hx)

/-- **The cusp chart below the ceiling avoids the truncation torus** (in the coordinates of the
chart). -/
theorem mbarLow_not_Tset_aux (v : Fin 5) {q : CuspE4}
    (h1 : 11 / 10 ≤ q 3) (h2 : q 3 < Work.Cusp.beta (xOf4 q)) :
    mbarLow v q ∉ Work.FoldInst.Tset := by
  have hmem : redV v (uhsXj q) ∈ cubeBox (cubeOf v (uhsXj q)) := redV_mem_cubeBox v _
  have hceil_id : ceilH (cubeOf v (uhsXj q)) (redV v (uhsXj q)) = Work.Cusp.beta (xOf4 q) := by
    simpa only [chartCube, chartRed] using ceilH_chartRed v q
  have hceil : q 3 < ceilH (cubeOf v (uhsXj q)) (redV v (uhsXj q)) := by
    rw [hceil_id]
    exact h2
  have hQ : chartKlein (cubeOf v (uhsXj q)) (mkE4 (redV v (uhsXj q)) (q 3))
      ∈ Work.FoldInst.Qbar :=
    chartKlein_mem _ hmem h1 (le_of_lt hceil)
  have hnot := xbarOf_not_mem_Xtrunc (cubeOf v (uhsXj q)) hmem h1 hceil hQ
  have hmk : mbarLow v q = Work.FoldInst.mk (xbarOf (cubeOf v (uhsXj q))
      (chartKlein (cubeOf v (uhsXj q)) (mkE4 (redV v (uhsXj q)) (q 3))) hQ) := by
    rw [mbarLow_eq_beta v h1 (le_of_lt h2)]
    rfl
  rw [hmk]
  exact mk_xbarOf_not_mem_Tset hnot

/-- **The chimney below the ceiling avoids the truncation set** (the fields `mbarLow_not_Tset` and `mbarLow_not_TsetTop` of `Work.Cusp.CuspGlueData`, for the concrete `Work.RTOwed.mbarLow`).

The point of `M̄` with UHS coordinates `q` strictly below the ceiling `β (xOf q)` is not in `Tset`; in other words the chart of the hyperbolic piece meets the cusped boundary exactly at the ceiling (`Work.RTOwed.mbarLow_ceiling_mem` gives the other inclusion at the ceiling).

Route: `Work.RTOwed.mbarLow_eq_beta` gives `mbarLow v q = mk (cubeBit (chartCube v q), ⟨redChart v (chartCube v q) q, _⟩)` and `redChart v (chartCube v q) q = chartKlein a (mkE4 z s)` with `a = cubeOf v (uhsXj q)`, `z = redV v (uhsXj q)`, `s = q 3`.  Since `Tset = mk '' Xtrunc` and `Xtrunc` is saturated for `Work.FoldInst.rel` (`isClosed_XtruncSat : XtruncSat = Xtrunc` in `Work/FoldInst/Quotient.lean`), it suffices to prove `xbarOf a (chartKlein a (mkE4 z s)) ∉ Xtrunc`, i.e. that *no* truncation slack vanishes: `∀ w : Fin 24, truncSlack w (chartKlein a (mkE4 z s)) ≠ 0`.  For `z` in the **open** cube and `s < ceilH a z` this is `Work.RTOwed.chartKlein_strict` (all slacks are `> 0`).  When `z` lies on a wall of the cube (possible, since `redV` uses the half open cube), the value lies on a *side* facet; the corresponding truncation slacks are still strictly positive, by `Work.RTOwed.chartKlein_self_facet` for the own vertex `cubeVert a` and by a finite certificate (of the same nature as the ones in `chartKlein_mem`/`chartKlein_strict`, using the wall tables `Work.RTOwed.wallLo`/`wallHi` and `Work.RTOwed.cuspCertWalls`) for the other 23 vertices. -/
theorem mbarLow_not_Tset (v : Fin 5) (c : Work.Cusp.E3) (δ : ℝ) :
    (∀ {q : Work.Cusp.E4}, q ∈ Work.Cusp.cuspChartBox v c δ →
      q 3 < Work.Cusp.beta (Work.Cusp.xOf q) → Work.RTOwed.mbarLow v q ∉ Work.FoldInst.Tset) ∧
    (∀ {q : Work.Cusp.E4}, q ∈ Work.Cusp.cuspBoxTop v c δ →
      q 3 < Work.Cusp.beta (Work.Cusp.xOf q) → Work.RTOwed.mbarLow v q ∉ Work.FoldInst.Tset) := by
  constructor
  · intro q hq hb
    exact mbarLow_not_Tset_aux v (le_of_lt hq.2.1) hb
  · intro q hq hb
    exact mbarLow_not_Tset_aux v (le_of_lt hq.2.1) hb

end Work.RTOwed
