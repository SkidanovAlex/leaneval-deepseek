import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.honestFsCore
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.bulkETTLe` — the `ε_T·T` row of the bulk error

At the honest parameter block `paramsAt μ (a v) = fsParams (μ(a v)³)` the momentum cutoff
is (by definition)

  `T = bogT v R μ = 10⁶(1 + L)/ε`,   `L = bogL v μ = log D⁻¹`,   `D = dil v μ = μ(a v)³`,

while `ε = lhyEpsX v R μ` (the closed form of `hcore.hEeq`), and `ε_T = D^{23/1292}`.
The row proved here,

  `ε_T · T ≤ 2·10⁶·(323/156)·ε`,

is therefore *exactly* the scalar inequality

  `D^{23/1292}·(1 + L) ≤ (646/156)·ε²`.

It is proved from the single structural fact that `ε` is a *sum of four nonnegative
terms*, the last of which is `D^{1/1292}(1 + (156/323)L)`: hence

  `ε ≥ D^{1/1292}(1 + (156/323)L)`,

and everything reduces to the elementary `D ≤ 1` monomial comparison

  `D^{21/1292}·(1 + L) ≤ (323/78)·(1 + (156/323)L)²`,

i.e. `D^{21/1292} ≤ 1` together with `1 + L ≤ (323/78)(1 + (156/323)L)² = 323/78 + 4L + …`.

Note that `R` is *not* assumed positive: `Real.sqrt` of a negative number is `0`, so the
first summand of `ε` is nonnegative in any case (and the dominating fourth summand does
not involve `R` at all).  Nothing else from `Core` is used beyond `ε > 0`, `D ≤ 1`, `L ≥ 0`
and the two definitional identities `hTdef`, `hEeq`.
-/

noncomputable section

namespace Work.BoseBogFS

set_option linter.unusedVariables false

/-- **The monomial core.**  For `0 < D ≤ 1` and `0 ≤ L`,

  `D^{23/1292}·(1 + L) ≤ (323/78)·(D^{1/1292}·(1 + (156/323)L))²`.

Indeed `D^{23/1292} = D^{21/1292}·D^{2/1292} ≤ D^{2/1292}`, and
`(D^{1/1292})² = D^{2/1292}`, so it suffices that
`1 + L ≤ (323/78)(1 + (156/323)L)²`; expanding the square gives
`(323/78) + 4L + (323/78)(156/323)²L² ≥ 323/78 + 4L ≥ 1 + L`. -/
private lemma bulkETTLe_arith {D L : ℝ} (hD0 : 0 < D) (hD1 : D ≤ 1) (hL0 : 0 ≤ L) :
    D ^ ((23 : ℝ) / 1292) * (1 + L)
      ≤ (323 / 78) * (D ^ ((1 : ℝ) / 1292) * (1 + ((156 : ℝ) / 323) * L)) ^ 2 := by
  have hp : (0 : ℝ) < D ^ ((1 : ℝ) / 1292) := Real.rpow_pos_of_pos hD0 _
  have h2p : (0 : ℝ) < D ^ ((2 : ℝ) / 1292) := Real.rpow_pos_of_pos hD0 _
  have hsplit : D ^ ((23 : ℝ) / 1292)
      = D ^ ((21 : ℝ) / 1292) * D ^ ((2 : ℝ) / 1292) := by
    rw [← Real.rpow_add hD0]
    norm_num
  have hsq : (D ^ ((1 : ℝ) / 1292)) ^ 2 = D ^ ((2 : ℝ) / 1292) := by
    rw [sq, ← Real.rpow_add hD0]
    norm_num
  have h21 : D ^ ((21 : ℝ) / 1292) ≤ 1 := Real.rpow_le_one hD0.le hD1 (by norm_num)
  have h1mL : (0 : ℝ) ≤ 1 + L := by linarith
  have hLstep : (1 + L) ≤ (323 / 78) * (1 + ((156 : ℝ) / 323) * L) ^ 2 := by
    nlinarith [sq_nonneg (((156 : ℝ) / 323) * L), hL0]
  calc D ^ ((23 : ℝ) / 1292) * (1 + L)
      = D ^ ((21 : ℝ) / 1292) * (D ^ ((2 : ℝ) / 1292) * (1 + L)) := by
        rw [hsplit]; ring
    _ ≤ 1 * (D ^ ((2 : ℝ) / 1292) * (1 + L)) :=
        mul_le_mul_of_nonneg_right h21 (mul_nonneg h2p.le h1mL)
    _ ≤ D ^ ((2 : ℝ) / 1292) * ((323 / 78) * (1 + ((156 : ℝ) / 323) * L) ^ 2) := by
        rw [one_mul]
        exact mul_le_mul_of_nonneg_left hLstep h2p.le
    _ = (323 / 78) * (D ^ ((1 : ℝ) / 1292) * (1 + ((156 : ℝ) / 323) * L)) ^ 2 := by
        rw [mul_pow, hsq]; ring

theorem bulkETTLe {v : EuclideanSpace ℝ (Fin 3) → ℝ} {R ρ μ : ℝ}
    (hav : 0 < _root_.BoseGases.a v) (hcore : Work.BoseBogFS.Core v R μ ρ) :
    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT * Work.BoseBogFS.bogT v R μ
      ≤ 2 * 10 ^ 6 * (323 / 156) * Work.BoseB6.lhyEps (_root_.BoseGases.a v) R
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).Kl
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).s
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d μ := by
  have hD0 : 0 < Work.BoseFixR.dil v μ := hcore.hD0
  have hD1 : Work.BoseFixR.dil v μ ≤ 1 := hcore.hD1
  have hL0 : 0 ≤ bogL v μ := hcore.hL0
  have hpos : (0 : ℝ) < 1 + ((156 : ℝ) / 323) * bogL v μ := by
    have h : 0 ≤ ((156 : ℝ) / 323) * bogL v μ := mul_nonneg (by norm_num) hL0
    linarith
  have hbase : (0 : ℝ) < (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
      * (1 + ((156 : ℝ) / 323) * bogL v μ) :=
    mul_pos (Real.rpow_pos_of_pos hD0 _) hpos
  -- the closed form of `ε = lhyEpsX v R μ`, written with `bogL`
  have h4 : lhyEpsX v R μ
      = (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R
        + (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292)
        + (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646) * (1 + ((162 : ℝ) / 323) * bogL v μ)
        + (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
            * (1 + ((156 : ℝ) / 323) * bogL v μ) := by
    simp only [lhyEpsX, bogL]
  -- `ε` dominates its fourth summand
  have hXle : (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292) * (1 + ((156 : ℝ) / 323) * bogL v μ)
      ≤ lhyEpsX v R μ := by
    rw [h4]
    have h1 : 0 ≤ (μ * _root_.BoseGases.a v) ^ ((1 : ℝ) / 4) * Real.sqrt R :=
      mul_nonneg (Real.rpow_nonneg (le_of_lt (mul_pos hcore.hμ hav)) _) (Real.sqrt_nonneg R)
    have h2 : 0 ≤ (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292) := Real.rpow_nonneg hD0.le _
    have h3 : 0 ≤ (Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 646)
        * (1 + ((162 : ℝ) / 323) * bogL v μ) := by
      have h : 0 ≤ ((162 : ℝ) / 323) * bogL v μ := mul_nonneg (by norm_num) hL0
      exact mul_nonneg (Real.rpow_nonneg hD0.le _) (by linarith)
    linarith
  have hEp : 0 < lhyEpsX v R μ := lt_of_lt_of_le hbase hXle
  -- the key inequality `D^{23/1292}(1 + L) ≤ (323/78)ε²`
  have hkey : (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292) * (1 + bogL v μ)
      ≤ (323 / 78) * (lhyEpsX v R μ) ^ 2 := by
    have h := bulkETTLe_arith hD0 hD1 hL0
    have hsq : ((Work.BoseFixR.dil v μ) ^ ((1 : ℝ) / 1292)
        * (1 + ((156 : ℝ) / 323) * bogL v μ)) ^ 2 ≤ (lhyEpsX v R μ) ^ 2 :=
      pow_le_pow_left₀ hbase.le hXle 2
    nlinarith [h, hsq]
  rw [hcore.hTdef, hcore.hEeq, paramsAt_eT v μ]
  rw [show (Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292)
        * (10 ^ 6 * (1 + bogL v μ) / lhyEpsX v R μ)
      = 10 ^ 6 * ((Work.BoseFixR.dil v μ) ^ ((23 : ℝ) / 1292) * (1 + bogL v μ))
          / lhyEpsX v R μ by ring]
  rw [div_le_iff₀ hEp]
  nlinarith [hkey]

end Work.BoseBogFS
