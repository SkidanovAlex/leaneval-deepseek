import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.bogParamsData
import Submission.Work.BoseBogFS.phiC_defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.CleanRiemScaled` — the per-cell (scaled) layer of the clean Riemann row

This module starts the *scaled* per-cell layer of `Work.BoseBogFS.cleanFun_tsum_le_integral`
(see `FINDING_cleanFun_tsum_session17.md`).  Everything here is pure bookkeeping:

* `psiSc_eq_phiC_of` — `psiSc = phiC (τ_s) (β_s) ‖t‖` on the branch `τ_s + 2β_s ≥ 0`,
  **without** assuming `β_s ≥ 0` (the existing `psiSc_eq_phiC` needs it);
* `tauScRad_mono` — the monotonicity of `r ↦ τ_s(r)` (the `u`-range of a cell).
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **`psiSc` is `phiC` on the branch `τ_s + 2 β_s ≥ 0`.**  Unlike `psiSc_eq_phiC` this does not
require `0 ≤ β_s`: the only thing the algebraic identity `A − √(A²−B²) = B²/(A+√(A²−B²))` needs is
that the discriminant `τ_s²+2τ_sβ_s = τ_s(τ_s+2β_s)` be nonnegative. -/
theorem psiSc_eq_phiC_of {v : E3 → ℝ} {h : Work.UBB.ScatSol v} {ρ μ : ℝ} {t : E3}
    (hu : 0 ≤ tauSc v ρ μ t)
    (h2 : 0 ≤ tauSc v ρ μ t + 2 * betaSc v h ρ μ t) :
    psiSc v h ρ μ t = phiC (tauSc v ρ μ t) (betaSc v h ρ μ t) ‖t‖ := by
  set u := tauSc v ρ μ t with hu'
  set b := betaSc v h ρ μ t with hb'
  have hsq : 0 ≤ u ^ 2 + 2 * u * b := by
    have : u * (u + 2 * b) = u ^ 2 + 2 * u * b := by ring
    rw [← this]
    exact mul_nonneg hu h2
  have key : (u + b) - Real.sqrt (u ^ 2 + 2 * u * b)
      = b ^ 2 / ((u + b) + Real.sqrt (u ^ 2 + 2 * u * b)) := by
    by_cases hden : (u + b) + Real.sqrt (u ^ 2 + 2 * u * b) = 0
    · have h1 := Real.sqrt_nonneg (u ^ 2 + 2 * u * b)
      have hub : u + b = 0 := by linarith
      have hs0 : Real.sqrt (u ^ 2 + 2 * u * b) = 0 := by linarith
      have hb0 : b = 0 := by linarith
      have hu0 : u = 0 := by linarith
      rw [hu0, hb0]
      have harg : (0 : ℝ) ^ 2 + 2 * 0 * 0 = 0 := by norm_num
      rw [harg, Real.sqrt_zero]
      norm_num
    · rw [eq_div_iff hden]
      have h3 : Real.sqrt (u ^ 2 + 2 * u * b) ^ 2 = u ^ 2 + 2 * u * b := Real.sq_sqrt hsq
      nlinarith [h3]
  have hmain : tauSc v ρ μ t + betaSc v h ρ μ t
        - Real.sqrt ((tauSc v ρ μ t + betaSc v h ρ μ t) ^ 2 - betaSc v h ρ μ t ^ 2)
      = betaSc v h ρ μ t ^ 2 / (tauSc v ρ μ t + betaSc v h ρ μ t
          + Real.sqrt (tauSc v ρ μ t ^ 2 + 2 * tauSc v ρ μ t * betaSc v h ρ μ t)) := by
    rw [← hu', ← hb']
    rw [show (u + b) ^ 2 - b ^ 2 = u ^ 2 + 2 * u * b by ring]
    exact key
  rw [psiSc, Work.BoseB6.bogZeroPoint, phiC, hmain]

/-- **The scaled kinetic symbol is monotone in the radius.** -/
theorem tauScRad_mono {v : E3 → ℝ} {ρ μ : ℝ} (hP : 0 < ρ * a v)
    (heT0 : 0 ≤ (paramsAt μ (a v)).eT) (heT1 : (paramsAt μ (a v)).eT ≤ 1)
    (hc1 : 0 < bogC1 v ρ μ) (hc2 : 0 < bogC2 v ρ μ) :
    Monotone (tauScRad v ρ μ) := by
  intro x y hxy
  rw [tauScRad_eq v hP x, tauScRad_eq v hP y]
  have h1 : Work.BoseBoxFock.tauProf (x / bogC1 v ρ μ) ≤
      Work.BoseBoxFock.tauProf (y / bogC1 v ρ μ) :=
    Work.BoseBoxFock.tauProf_mono (by gcongr)
  have h2 : Work.BoseBoxFock.tauProf (x / bogC2 v ρ μ) ≤
      Work.BoseBoxFock.tauProf (y / bogC2 v ρ μ) :=
    Work.BoseBoxFock.tauProf_mono (by gcongr)
  have hw1 : 0 ≤ (1 - (paramsAt μ (a v)).eT) * (bogC1 v ρ μ) ^ 2 :=
    mul_nonneg (by linarith) (sq_nonneg _)
  have hw2 : 0 ≤ (paramsAt μ (a v)).eT * (bogC2 v ρ μ) ^ 2 :=
    mul_nonneg heT0 (sq_nonneg _)
  nlinarith [mul_le_mul_of_nonneg_left h1 hw1, mul_le_mul_of_nonneg_left h2 hw2]

end Work.BoseBogFS
