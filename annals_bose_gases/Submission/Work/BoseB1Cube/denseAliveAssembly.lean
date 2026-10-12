import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.cubeHoleCapRow
import Submission.Work.BoseB1Cube.flatVar_eq_weightedVar
import Submission.Work.BoseB1Cube.perBoxFCube_of_ledgerDelta
import Submission.Work.BoseFixB1B.fibreDeviation_le_ae
import Submission.Work.BoseFixB1S.fibreDeviation_factor
import Submission.Work.BoseFixB1S.pairing_le_chiSq_mul_abs_integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB1Cube.denseAliveAssembly` — `PerBoxFCube` from the four concrete rows + `(bud)`

Read `Submission/Work/BoseB1Cube/FINDING_cubeBandArmDenseAliveRow_session2.md` §1.

`Work.BoseB1Cube.perBoxFCube_of_ledgerDelta` (PROVED) turns the five rows (F), (fib), (pair),
(kin), (bud) into `PerBoxFCube`.  Three of them are *free*:

* **(F)** is the PROVED `Work.BoseFixB1.Up.flatFterm_sharp_row` with `V := flatVar`;
* **(kin)** with `P := tbGapCoeff(ℓd, eT)·nPlusB` is `linarith` from `sbKinCube`'s definition
  (`sbKinCube = bGapCoeff·cnPlusBoxInd + cubeSpectral`), `nPlusB = cnPlusBoxInd` and
  `0 ≤ cubeSpectral` (`tBwordKinInd_nonneg`);
* **(fib)**, **(pair)** hold with the *equalities* `Efib := μ·flatFibSum − μ·w1MassB·τ·N`,
  `Epair := ½·flatPairMass·(τ²N + V) − flatPairSum`;
* **(bud)** is the residual `hbud` of this theorem — the only analytic input.

So the target `cubeBandArmDenseAliveRow` is *exactly* `hbud` (with the concrete `Efib`, `Epair`,
`P`), and `hbud`'s content is the ledger (R) of the FINDING §1.
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

local notation "E3" => EuclideanSpace ℝ (Fin 3)

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB
open Work.SmallBoxSliding Work.BoseFixB1

set_option autoImplicit false
set_option linter.unusedVariables false

/-- `sbKinCube ≥ tbGapCoeff(ℓd, eT)·n₊` — the `(kin)` row at `P := tbGapCoeff·nPlusB`. -/
theorem gap_le_sbKinCube {v : E3 → ℝ} {μ : ℝ} {n : ℕ}
    (Φ : Submission.BoseGases.X n → ℝ) (u : E3) :
    Work.SmallBoxTBWord.tbGapCoeff
        (Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
        (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
      * Work.BoseFixB1.Up.nPlusB v μ u n Φ
      ≤ Work.BoseFixB1B.sbKinCube v μ u Φ := by
  have hspec : 0 ≤ Work.UBBInputs8.tBwordKinInd (Work.BoseFixB1.bSide v μ)
      (Work.BoseFixB1.bA v μ u) (Work.BoseFixB1.bV v μ u)
      (Submission.BoseGases.chiSmallB (Work.BoseFixB1.bM v μ) (Work.BoseFixB1.bSide v μ)
        (Work.BoseFixB1.bD v μ) u)
      (Work.BoseFixB1.sbCut μ (_root_.BoseGases.a v)) Φ :=
    Work.BoseFixB1.tBwordKinInd_nonneg Φ
  simp only [Work.BoseFixB1B.sbKinCube, Work.BoseFixB1.Up.nPlusB]
  exact le_add_of_nonneg_right hspec

end Work.BoseB1Cube

namespace Work.BoseB1Cube

/-- **`PerBoxFCube` from the concrete `(bud)` row.**  The four other rows are supplied here:
`(F)` by `Work.BoseFixB1.Up.flatFterm_sharp_row` (at `V := Up.flatVar`), `(kin)` by
`gap_le_sbKinCube`, and `(fib)`, `(pair)` by the equalities `Efib = μ·fibSum − μ·w1MassB·τ·N`,
`Epair = ½·w₂·(τ²N+V) − pairSum`.  The hypothesis `hbud` is the residual of the target. -/
theorem perBoxFCube_of_bud {v : E3 → ℝ} (h : Work.UBB.ScatSol v) (hv : 0 ≤ v)
    (hv1 : MeasureTheory.MemLp v 1) (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) (hav : 0 < _root_.BoseGases.a v)
    {ε₀ μ c₁ C : ℝ} (hAdm : Work.BoseBoxFix.Adm v ε₀ μ) (hc₁ : 0 < c₁) (hc₁8 : c₁ ≤ 1 / 8)
    {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)))
    (u : E3)
    (hR16 : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d / 16)
    (hRχ : R ≤ Work.BoseBox.sideAt μ (_root_.BoseGases.a v) * Submission.BoseGases.chiR0)
    (hW12 : Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
        ≤ Work.BoseFixB1.flatPairMass v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
    (hbud : (μ * Work.BoseFixB1.flatFibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                (Φ : Submission.BoseGases.X n → ℝ)
              - μ * Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                * Work.BoseFixB1.flatTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                    (Φ : Submission.BoseGases.X n → ℝ)
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
            + ((1 / 2) * Work.BoseFixB1.flatPairMass v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                * (Work.BoseFixB1.flatTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                      (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                    * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                  + Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
              - Work.BoseFixB1.flatPairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                  (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                  (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  (Φ : Submission.BoseGases.X n → ℝ))
          ≤ C * (μ ^ 2 * (_root_.BoseGases.a v)
                * ((R / (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                      * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)) ^ 2
                    + (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).KB ^ 3
                      * (μ * (_root_.BoseGases.a v) ^ 3) ^ (1 / 2 : ℝ))
                * Work.SmallBoxSliding.chiMass (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
              + μ * (_root_.BoseGases.a v)
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ))
            + Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              * ((Work.BoseFixB1.flatTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                      (Φ : Submission.BoseGases.X n → ℝ) - μ) ^ 2
                  * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                  * (1 / 2 - c₁ * μ
                      / (Work.BoseFixB1.flatTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                          (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                          (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                          (Φ : Submission.BoseGases.X n → ℝ) + μ))
                + Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u
                    * (1 / 2 - 4 * c₁ * μ ^ 2
                        / (Work.BoseFixB1.flatTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                            (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                            (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                            (Φ : Submission.BoseGases.X n → ℝ) + μ) ^ 2))
            + (1 / 2)
                * (Work.BoseFixB1.flatPairMass v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                    (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                    (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                  - Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u)
                * (Work.BoseFixB1.flatTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
                      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
                      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
                      (Φ : Submission.BoseGases.X n → ℝ) ^ 2
                    * Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)
                  + Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u)
            + Work.SmallBoxTBWord.tbGapCoeff
                (Work.BoseBox.sideAt μ (_root_.BoseGases.a v)
                  * (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d)
                (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).eT
              * Work.BoseFixB1.Up.nPlusB v μ u n (Φ : Submission.BoseGases.X n → ℝ)) :
    Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u := by
  have hsplit : Work.BoseFixB1.sbPot h μ u (Φ : Submission.BoseGases.X n → ℝ)
      = - (μ * Work.BoseFixB1.flatFibSum h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ))
        + Work.BoseFixB1.flatPairSum v (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
              (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
              (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
              (Φ : Submission.BoseGases.X n → ℝ) := by
    simpa only [Work.BoseFixB1.pM, Work.BoseFixB1.pL, Work.BoseFixB1.pD,
      Work.BoseFixB1.fibSum, Work.BoseFixB1.pairSum, Work.BoseFixB1.flatFibSum,
      Work.BoseFixB1.flatPairSum] using
      (Work.BoseFixB1.sbPot_split (v := v) (h := h) (R := R) hv_supp hR hv hvrad hv1
        (ε₀ := ε₀) (μ := μ) hAdm (Φ := (Φ : Submission.BoseGases.X n → ℝ)) Φ.contDiff.continuous
        u hR16 hRχ)
  -- the four side conditions
  have hNnn : 0 ≤ Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Work.BoseBoxFix.normB, Work.BoseKinLoc.sqNormB]
    exact MeasureTheory.integral_nonneg (fun x => sq_nonneg _)
  have hW1nn : 0 ≤ Work.BoseFixB1.w1MassB h (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u :=
    Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp
      (Work.BoseFixB1.adm_ell_pos hAdm) (Work.BoseFixB1.adm_d_pos hAdm) u
  have hτnn : 0 ≤ Work.BoseFixB1.flatTau (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).M
      (Work.BoseBox.sideAt μ (_root_.BoseGases.a v))
      (Work.BoseBox.paramsAt μ (_root_.BoseGases.a v)).d u
      (Φ : Submission.BoseGases.X n → ℝ) := by
    rw [Work.BoseFixB1.flatTau]
    refine div_nonneg ?_ ?_
    · rw [Work.BoseFixB1.flatScountB]
      exact MeasureTheory.integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (by
        rw [Work.BoseFixB1.nCountB]
        exact Finset.sum_nonneg (fun i _ => sq_nonneg _)))
    · exact mul_nonneg (Work.SmallBoxSliding.chiMass_nonneg _ _ _ _) hNnn
  have hVnn : 0 ≤ Work.BoseFixB1.Up.flatVar v μ (Φ : Submission.BoseGases.X n → ℝ) u := by
    rcases eq_or_ne (Work.BoseBoxFix.normB v μ n (Φ : Submission.BoseGases.X n → ℝ)) 0 with h0 | h0
    · rw [Work.BoseFixB1.Up.flatVar, Work.BoseFixB1.Up.flatT2, h0, mul_zero, sub_zero]
      exact MeasureTheory.integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
    · rw [Work.BoseB1Cube.flatVar_eq_weightedVar (Φ := (Φ : Submission.BoseGases.X n → ℝ))
        Φ.contDiff.continuous u h0]
      exact MeasureTheory.integral_nonneg (fun x => mul_nonneg (sq_nonneg _) (sq_nonneg _))
  refine Work.BoseB1Cube.perBoxFCube_of_ledgerDelta (v := v) h (μ := μ) hAdm.1 hc₁ hc₁8
    hNnn hW1nn hW12 hτnn hVnn
    (Work.BoseFixB1.Up.flatFterm_sharp_row (v := v) h hAdm Φ u)
    (by linarith) (by linarith) hsplit
    (gap_le_sbKinCube (v := v) (μ := μ) (Φ := (Φ : Submission.BoseGases.X n → ℝ)) u)
    hbud

end Work.BoseB1Cube
