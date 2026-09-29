import Mathlib
import Submission.HvdH.Interfaces
import Submission.Work.Resample.pb2Defs
import Submission.Work.Resample.paCostD
import Submission.Work.Resample.paDRestLit

/-!
# `Work.Resample.pb2CostDefs`: the cost arithmetic of the `B̃` half (split of `PB2Br`)

`PB2Br` (the per-axis budget of the `B̃` pass, `Submission.Work.Resample.pb2Defs`) is a sum of nine
terms.  Exactly as for the `Ã` half (`Work.Resample.paCostD`), they are grouped as

* `paDZ Kb p ts j` — the `prep` table of the axis (`Kb * (t_j+1) * (p+1)^Kb`), absorbed by the
  `ts.sum * (p+1)^K` term of `resCost` (the group `Z` of `paCostD` can be reused verbatim: the
  `prep` term of `PB2Br` is *literally* `64 * paDZ`);
* `pb2DCm` — the `applyAlong` pass calling `self`, absorbed by the
  `ts.prod * (√p+1) * α * (Cm (K*p) + p)` term;
* `pb2DX` — the extra `Kb * (t_j+1) * (p+1)^2` term which the `B`-slice word carries (it is not
  present in the `Ã` half), absorbed by the `ts.prod * p^2` term;
* `pb2DRest` — the layout, `isz` and constant terms, absorbed by the `ts.prod * p^2` term.

The constants `pb2DCR Kb` (per axis, for `pb2DRest + 64 * pb2DX`) and `pb2DK Kb Kc1 Kc2 Kc3` (for
the whole budget) are the `B̃` analogues of `2^24 * D^3 * (D+5)` and `paDK`.
-/

namespace Work.Resample

open HvdH

set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

/-! ## Splitting the per-axis budget -/

/-- The `Cm`-carrying term of `PB2Br` at axis `j` (`A_j = (ss.take j).prod`,
`B_j = (ts.drop (j+1)).prod`). -/
def pb2DCm (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) : ℕ :=
  ((ss.take j).prod * (ts.drop (j + 1)).prod) *
    (Kb * (ts.getD j 0 + 1) * (Nat.sqrt p + 1) * (α + 1) * (Cm (Kb * p) + p + 1))

/-- The extra `Kb * (t_j + 1) * (p+1)^2` term of `PB2Br` at axis `j`. -/
def pb2DX (Kb p : ℕ) (ss ts : List ℕ) (j : ℕ) : ℕ :=
  ((ss.take j).prod * (ts.drop (j + 1)).prod) * (Kb * (ts.getD j 0 + 1) * (p + 1) ^ 2)

/-- The remaining terms of `PB2Br` at axis `j` (layout, `isz` and the `j`-independent
constants). -/
def pb2DRest (Kb p : ℕ) (ss ts : List ℕ) (j : ℕ) : ℕ :=
  64 * (((ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1) + 1) *
      ((2 * p + 8) +
        ((ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)).size + 1) *
      (((ss.take j).prod * (ts.drop (j + 1)).prod * (ss.getD j 0 + ts.getD j 0 + 1)).size + 1))
  + 64 * (HvdH.isz (((ss.take j).prod : ℕ) : ℤ) + HvdH.isz ((ss.getD j 0 : ℕ) : ℤ) +
      HvdH.isz ((ts.getD j 0 : ℕ) : ℤ) + HvdH.isz (((ts.drop (j + 1)).prod : ℕ) : ℤ))
  + 1048576 * (ts.prod * (2 * p + 8) + ts.prod + 2)
  + 1048576 * ((HvdH.D + 1) * (p + 2))
  + 1048576 * ((HvdH.D + 1) * (p + 2) * ((HvdH.D + 1) * (p + 2)))
  + 1048576 * ((p + 3) * (p + 3))
  + 1000000

/-- Per-axis bound constant for `pb2DRest + 64 * pb2DX`: the `p^2`-term constant
`2^24 * D^3 * (D+5)` of `Work.Resample.paDRestLit.paDL_arith` plus `1024 * Kb` for the extra
`Kb (t+1) (p+1)^2` term. -/
def pb2DCR (Kb : ℕ) : ℕ := 2 ^ 24 * HvdH.D ^ 3 * (HvdH.D + 5) + 1024 * Kb

/-- `PB2Br` is the sum of its four groups. -/
theorem pb2DBr_eq (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) :
    PB2Br Kb Cm p α ss ts j =
      64 * paDZ Kb p ts j + 64 * pb2DCm Kb Cm p α ss ts j + 64 * pb2DX Kb p ss ts j +
        pb2DRest Kb p ss ts j := by
  unfold PB2Br paDZ pb2DCm pb2DX pb2DRest
  ring

/-- The `p^2`-group of the `B̃` per-axis budget: the extra `Kb (t+1) (p+1)^2` term together with the
layout/`isz`/constant terms (those two are absorbed by the same `ts.prod * p^2` term of `resCost`,
through `pb2DXLe` + `pb2DRestLe`). -/
def pb2DY (Kb p : ℕ) (ss ts : List ℕ) (j : ℕ) : ℕ := 64 * pb2DX Kb p ss ts j + pb2DRest Kb p ss ts j

/-- Three-group form of `pb2DBr_eq`, matching the shape used by `paCostD` for the `Ã` half. -/
theorem pb2DBr_eq3 (Kb : ℕ) (Cm : ℕ → ℕ) (p α : ℕ) (ss ts : List ℕ) (j : ℕ) :
    PB2Br Kb Cm p α ss ts j = 64 * paDZ Kb p ts j + 64 * pb2DCm Kb Cm p α ss ts j +
      pb2DY Kb p ss ts j := by
  rw [pb2DBr_eq Kb Cm p α ss ts j]
  unfold pb2DY
  ring

/-- The explicit constant of `pb2CostD`.  It dominates `4096 * (Kc1 + Kc3) + Kc2 * (D * pb2DCR Kb + 1)`
(the `p^2`-group), `128 * Kc2 * Kb` (the `prep` group), `1024 * Kc2 * D * Kb` (the `Cm` group) and
each of `Kc1, Kc2, Kc3, Kb`. -/
def pb2DK (Kb Kc1 Kc2 Kc3 : ℕ) : ℕ :=
  4096 * (Kc1 + Kc3) + Kc2 * (HvdH.D * pb2DCR Kb + 1) + 128 * Kc2 * Kb +
    1024 * Kc2 * HvdH.D * Kb + Kb + Kc1 + Kc2 + Kc3

/-- The requirements on `pb2DK` used by the four group estimates of `pb2CostD`. -/
theorem pb2DK_facts (Kb Kc1 Kc2 Kc3 : ℕ) :
    Kc1 ≤ pb2DK Kb Kc1 Kc2 Kc3 ∧ Kc2 ≤ pb2DK Kb Kc1 Kc2 Kc3 ∧
    Kc3 ≤ pb2DK Kb Kc1 Kc2 Kc3 ∧ Kb ≤ pb2DK Kb Kc1 Kc2 Kc3 ∧
    128 * Kc2 * Kb ≤ pb2DK Kb Kc1 Kc2 Kc3 ∧
    1024 * Kc2 * HvdH.D * Kb ≤ pb2DK Kb Kc1 Kc2 Kc3 ∧
    4096 * (Kc1 + Kc3) + Kc2 * (HvdH.D * pb2DCR Kb + 1) ≤ pb2DK Kb Kc1 Kc2 Kc3 := by
  unfold pb2DK
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> omega

end Work.Resample
