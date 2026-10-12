import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseB1Cube.CubeCrude
import Submission.Work.BoseFixB1.Cube.Assembly
import Submission.Work.BoseFixB1B.PerBoxSmoothHolds
import Submission.Work.BoseFixB1B.boxFormB_budgetAlt
import Submission.Work.BoseFixB1B.lowFlatnessB1
import Submission.Work.BoseFixB1B.oneBodyKineticHalfCube_of_mainWord
import Submission.Work.BoseFixB1B.perBoxIntegratedLow
import Submission.Work.BoseFixB1B.rPsi_eq_zero_of_normB_eq_zero
import Submission.Work.BoseFixB1B.thinShellBandCountHeld
import Submission.Work.BoseFixB1B.visCount_le_countAlt
import Submission.Work.BoseFixB1C.kineticHalfCubeLeMainWord
import Submission.Work.BoseFixB2.Assembly
import Submission.Work.BoseFixGlue.Ports.Small
import Submission.Work.BoseFixGlue.Ports.nodeB2gB_of_data
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB1Cube.PerBoxLHS` — the monotonicity API of the per-box row

`Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u` is the inequality
`perBoxCubeLHS(c₁, C) ≤ sbWordCube`, and its left-hand side is

    c₁·(W·A) − ½μ²·W·N − C·Z + μ(a v)·N ,
    W = w1MassB(…,u) ,  A = ∫Φ²F(n(u)/χ_M(u)) ,  N = ‖Φ‖² ,
    Z = μ²(a v)·Γ·χ_M(u)·N + μ(a v)·N ,  Γ = (R/(ℓd))² + K_B³(μa³)^{1/2} .

So the row is **monotone in the two constants**: decreasing `c₁` and increasing `C` both make it
*easier*.  That is what lets a proof split into regimes (`Work.BoseB1Cube.CubeGapBranchB1` and the
flat branch) at *different* constant triples and assemble a single one for `CubePerBox`, and any
prover who wants the row in the `∀ C ≥ C₀` shape needs it too.

This module supplies the two nonnegativity bricks (`perBoxCubeFWeight_nonneg`,
`perBoxCubeErr_nonneg`) and `perBoxFCube_mono` (taken in the two-sided form "the factors
`W·A` and `Z` are nonnegative", so that a consumer can supply them however it likes).
-/

noncomputable section

open MeasureTheory Metric Filter
open scoped Topology Real BigOperators ENNReal

namespace Work.BoseB1Cube

open _root_.BoseGases Submission.BoseGases Work.BoseBoxFix Work.BoseBox Work.UBB

local notation "E3" => EuclideanSpace ℝ (Fin 3)

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The `F`-weight of the per-box row is nonnegative**: `W = w1MassB ≥ 0` and
`A = ∫Φ²·psiWeight(n(u)/χ) ≥ 0` (`Φ² ≥ 0`, `nCountB ≥ 0`, `chiMass ≥ 0`, `μ > 0`). -/
theorem perBoxCubeFWeight_nonneg {v : E3 → ℝ} (h : ScatSol v) (hv : 0 ≤ v)
    (hvrad : _root_.BoseGases.IsRadial v) {R : ℝ} (hR : 0 < R)
    (hv_supp : tsupport v ⊆ Metric.ball (0 : E3) R) {ε₀ μ : ℝ} (hAdm : Adm v ε₀ μ) {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3) :
    0 ≤ Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), ((Φ : X n → ℝ) x) ^ 2 *
          Work.SmallBoxSliding.psiWeight 1 μ
            (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
              / Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                  (paramsAt μ (a v)).d u)) := by
  have hℓ : 0 < sideAt μ (a v) := Work.BoseFixB1.adm_ell_pos hAdm
  have hd : 0 < (paramsAt μ (a v)).d := Work.BoseFixB1.adm_d_pos hAdm
  have hμ : 0 < μ := Work.BoseFixB1.adm_mu_pos hAdm
  refine mul_nonneg
    (Work.BoseFixB1.w1MassB_nonneg (v := v) h hv hvrad hR hv_supp hℓ hd u) ?_
  refine integral_nonneg fun x => mul_nonneg (sq_nonneg _) ?_
  rw [Work.SmallBoxSliding.psiWeight]
  refine div_nonneg (mul_nonneg (by norm_num) (sq_nonneg _)) ?_
  have hχ : 0 ≤ Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u := Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hc : 0 ≤ Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u x := by
    rw [Work.BoseFixB1.nCountB]
    exact Finset.sum_nonneg fun i _ => sq_nonneg _
  exact add_nonneg one_pos.le
    (mul_nonneg (div_nonneg hc hχ) (inv_nonneg.mpr hμ.le))

/-- **The error bracket `Z` of the per-box row is nonnegative** — it is a sum of two products of
nonnegative factors. -/
theorem perBoxCubeErr_nonneg {v : E3 → ℝ} {R ε₀ μ : ℝ} (hAdm : Adm v ε₀ μ)
    (ha : 0 ≤ a v) {n : ℕ} (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3) :
    0 ≤ μ ^ 2 * (a v)
          * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u
          * normB v μ n (Φ : X n → ℝ)
        + μ * (a v) * normB v μ n (Φ : X n → ℝ) := by
  have hμ : 0 ≤ μ := (Work.BoseFixB1.adm_mu_pos hAdm).le
  have hΓ : 0 ≤ (R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
      + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ) :=
    add_nonneg (sq_nonneg _)
      (mul_nonneg (pow_nonneg (Work.BoseFixB1.paramsAt_KB_pos hAdm).le 3)
        (Real.rpow_nonneg (by positivity) _))
  have hχ : 0 ≤ Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
      (paramsAt μ (a v)).d u := Work.SmallBoxSliding.chiMass_nonneg _ _ _ _
  have hN : 0 ≤ normB v μ n (Φ : X n → ℝ) := Work.BoseFixB1.normB_nonneg _
  exact add_nonneg
    (mul_nonneg (mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) ha) hΓ) hχ) hN)
    (mul_nonneg (mul_nonneg hμ ha) hN)

/-- **Monotonicity of the per-box row in its two constants.**  Decreasing `c₁` and increasing `C`
both weaken the left-hand side of `PerBoxFCube`, so the inequality only gets easier.  The two
hypotheses are the nonnegativity of the row's two factors — supply them by
`perBoxCubeFWeight_nonneg` and `perBoxCubeErr_nonneg`. -/
theorem perBoxFCube_mono {v : E3 → ℝ} {h : ScatSol v} {R μ : ℝ} {n : ℕ}
    (Φ : Work.BoseKinLoc.BoxState n (sideAt μ (a v))) (u : E3) {c₁ c₁' C C' : ℝ}
    (hc₁ : c₁ ≤ c₁') (hC : C' ≤ C)
    (hA : 0 ≤ Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), ((Φ : X n → ℝ) x) ^ 2 *
          Work.SmallBoxSliding.psiWeight 1 μ
            (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
              / Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                  (paramsAt μ (a v)).d u)))
    (hZ : 0 ≤ μ ^ 2 * (a v)
          * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u
          * normB v μ n (Φ : X n → ℝ)
        + μ * (a v) * normB v μ n (Φ : X n → ℝ))
    (hrow : Work.BoseFixB1S.PerBoxFCube v h R c₁' C' μ n Φ u) :
    Work.BoseFixB1S.PerBoxFCube v h R c₁ C μ n Φ u := by
  rw [Work.BoseFixB1S.PerBoxFCube] at hrow ⊢
  have h1 : c₁ * (Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), ((Φ : X n → ℝ) x) ^ 2 *
          Work.SmallBoxSliding.psiWeight 1 μ
            (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
              / Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                  (paramsAt μ (a v)).d u)))
      ≤ c₁' * (Work.BoseFixB1.w1MassB h (paramsAt μ (a v)).M (sideAt μ (a v))
        (paramsAt μ (a v)).d u *
        (∫ x in abox n (sideAt μ (a v)), ((Φ : X n → ℝ) x) ^ 2 *
          Work.SmallBoxSliding.psiWeight 1 μ
            (Work.BoseFixB1.nCountB (paramsAt μ (a v)).M (sideAt μ (a v)) (paramsAt μ (a v)).d u x
              / Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
                  (paramsAt μ (a v)).d u))) :=
    mul_le_mul_of_nonneg_right hc₁ hA
  have h2 : C' * (μ ^ 2 * (a v)
          * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u
          * normB v μ n (Φ : X n → ℝ)
        + μ * (a v) * normB v μ n (Φ : X n → ℝ))
      ≤ C * (μ ^ 2 * (a v)
          * ((R / (sideAt μ (a v) * (paramsAt μ (a v)).d)) ^ 2
              + (paramsAt μ (a v)).KB ^ 3 * (μ * (a v) ^ 3) ^ (1 / 2 : ℝ))
          * Work.SmallBoxSliding.chiMass (paramsAt μ (a v)).M (sideAt μ (a v))
              (paramsAt μ (a v)).d u
          * normB v μ n (Φ : X n → ℝ)
        + μ * (a v) * normB v μ n (Φ : X n → ℝ)) :=
    mul_le_mul_of_nonneg_right hC hZ
  linarith

end Work.BoseB1Cube
