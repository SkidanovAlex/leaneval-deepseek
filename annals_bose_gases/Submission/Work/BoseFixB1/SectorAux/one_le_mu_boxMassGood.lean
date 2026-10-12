import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet
import Submission.Work.BoseFixB1.corner_regime
import Submission.Work.BoseFixB1.regime_sideAt_ge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `1 ≤ μ·|B(u)|` on the sliding good set at FS's parameters

This is the standing hypothesis `μ|B(u)| ≥ 1` of the fixed-`n` small-box bound
`thm:smallbox`, at FS's parameter block `paramsAt μ a = fsParams (μa³)` and for
the sliding boxes `B(u)`, `u ∈ G`, where

    G = goodSet ℓ d μ = {u : ∀ j, |((ℓd)•u)_j| ≤ ½ℓ(1+d) − μ^{-1/3}} ,
    ℓ = sideAt μ a ,  d = (paramsAt μ a).d .

The geometry gives `boxMass ℓ d u ≥ (μ^{-1/3})³` for `u ∈ G` as soon as
`μ^{-1/3} ≤ ℓd` and `d ≤ 1`
(`Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet`, the shortest side of `B(u)`
being `≥ μ^{-1/3}`); multiplying by `μ`
and using `μ·(μ^{-1/3})³ = 1` yields the claim.

Both regime hypotheses are pure monomial bookkeeping in `t = μa³ ≤ 1`:

* `ℓd = a·t^{−157/323}` and `μ^{-1/3} = a·t^{−323/3}` with
  `−157 ≤ −323/3`, so `ℓd ≥ μ^{-1/3}` (`Work.BoseFixB1.sideAt_mul_d_ge`);
* `d = t^{6/323} ≤ 1` (`fsXp_le_one`).
-/

noncomputable section

namespace Work.BoseFixB1.SectorAux

open Work.BoseBox

theorem one_le_mu_boxMassGood {a μ : ℝ} (ha : 0 < a) (hμ : 0 < μ) (hε : μ * a ^ 3 ≤ 1)
    {u : EuclideanSpace ℝ (Fin 3)}
    (hu : u ∈ Work.SmallBoxSliding.goodSet (Work.BoseBox.sideAt μ a)
      ((Work.BoseBox.paramsAt μ a).d) μ) :
    1 ≤ μ * Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ a)
      ((Work.BoseBox.paramsAt μ a).d) u := by
  have ht0 : 0 < μ * a ^ 3 := mul_pos hμ (pow_pos ha 3)
  -- the box side is positive
  have hℓ : 0 < Work.BoseBox.sideAt μ a := by
    rw [Work.BoseFixB1.sideAt_eq_fsXp ha hμ]
    exact mul_pos ha (Work.BoseBox.fsXp_pos ht0)
  -- `d = t^{6/323} > 0`
  have hd : 0 < (Work.BoseBox.paramsAt μ a).d := by
    rw [Work.BoseFixB1.d_eq_fsXp]
    exact Work.BoseBox.fsXp_pos ht0
  -- `d = t^{6/323} ≤ 1` since `t ≤ 1`
  have hd1 : (Work.BoseBox.paramsAt μ a).d ≤ 1 := by
    rw [Work.BoseFixB1.d_eq_fsXp]
    exact Work.BoseBox.fsXp_le_one ht0 hε (by norm_num)
  -- the regime `μ^{-1/3} ≤ ℓ d` (FS's `t^{-1/3} ≤ t^{-157/323}` at `t = μa³ ≤ 1`)
  have hreg : μ ^ (-(1 / 3 : ℝ)) ≤ Work.BoseBox.sideAt μ a
      * (Work.BoseBox.paramsAt μ a).d :=
    Work.BoseFixB1.sideAt_mul_d_ge (A := a) (μ := μ) ha hμ hε
  -- the box has volume at least `(μ^{-1/3})³`
  have hvol : (μ ^ (-(1 / 3 : ℝ))) ^ 3
      ≤ Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ a)
          ((Work.BoseBox.paramsAt μ a).d) u :=
    Work.BoseFixB1.boxMass_ge_deltaScale_of_goodSet hℓ hd hd1 hμ hreg hu
  -- `μ (μ^{-1/3})³ = 1`
  have hcube : μ * (μ ^ (-(1 / 3 : ℝ))) ^ 3 = 1 := by
    rw [← Real.rpow_natCast (μ ^ (-(1 / 3 : ℝ))) 3,
      ← Real.rpow_mul (x := μ) hμ.le (-(1 / 3)) ((3 : ℕ) : ℝ),
      show (-(1 / 3 : ℝ) * ((3 : ℕ) : ℝ)) = -1 by norm_num, Real.rpow_neg_one]
    exact mul_inv_cancel₀ (ne_of_gt hμ)
  calc (1 : ℝ) = μ * (μ ^ (-(1 / 3 : ℝ))) ^ 3 := hcube.symm
    _ ≤ μ * Work.SmallBoxSliding.boxMass (Work.BoseBox.sideAt μ a)
          ((Work.BoseBox.paramsAt μ a).d) u := mul_le_mul_of_nonneg_left hvol hμ.le

end Work.BoseFixB1.SectorAux
