import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.ZPTermNonnegLattice
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.CleanRowDefs` — the clean part of the zero-point row, as a function

`ZPCleanDeficitRow` (FS's `I₁` estimate transported to the honest data and to the full dual
lattice `(2π/ℓ)ℤ³`) is the second of the two analytic rows of `Work.BoseBogFS.ZPLatticeRow`.
Its left-hand side is the finite sum `Σ_{n∈S} (1/2)·cleanTerm v h ρ μ n` where `cleanTerm` is
defined on the *labels* `Fin 3 → ℤ` (`ZPLatticeAux.lean`).

This module lifts the same quantity to a function of the physical momentum `k ∈ ℝ³`, which is
what the three analytic ingredients of the clean row are stated for:

* **sign**: `cleanFun` is nonnegative once `‖k‖` exceeds an explicit threshold (so that a
  finite set `S` containing the low-momentum ball loses nothing), `CleanFunSign`;
* **Riemann**: the full-lattice sum of `cleanFun` is at most its integral plus a crude error
  (the integral is the `N`-free object FS's `lem:BogIntegral` bounds), `CleanFunRiemann`;
* **continuum**: `(2π)⁻³ℓ³` times the integral of `cleanFun` is at most FS's clean value
  `−4π·lhyC·ρ²aℓ³√(ρa³)` plus `C·errBracket` — this is FS's `lem:BogIntegral` in the honest
  scaling, obtained from the proved `Work.BoseB6Est.fsBogIntegral_display`, `CleanFunContinuum`.

The assembly `Work.BoseBogFS.ZPLatticeRowHolds` consumes those three rows plus the elementary
finite-sum-vs-`tsum` step (`CleanFunSum`).
-/

noncomputable section

open scoped Real Topology BigOperators

open MeasureTheory Filter Metric

namespace Work.BoseBogFS

open _root_.BoseGases Submission.BoseGases Work.UBB Work.BoseBox Work.BoseBoxFix Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

/-- **The clean part of the zero-point summand, as a function of the physical momentum.**
FS `eq:LHYIntegral1`: `𝒵(τ(k)+c(k), c(k)) − c(k)²/(2‖k‖²)` with `τ = tauAt`, `c = cAt`.
At `k = 0` the second term is junk `0` (`1/0 = 0` in `ℝ`). -/
def cleanFun (v : ℝ³ → ℝ) (h : ScatSol v) (ρ μ : ℝ) (k : ℝ³) : ℝ :=
  Work.BoseB6.bogZeroPoint (tauAt v μ k + cAt v h ρ μ k) (cAt v h ρ μ k)
    - (cAt v h ρ μ k) ^ 2 / (2 * ‖k‖ ^ 2)

/-- The label form of `cleanFun` is the chapter's `cleanTerm`. -/
lemma cleanTerm_eq_cleanFun (v : ℝ³ → ℝ) (h : ScatSol v) (ρ μ : ℝ) (n : Fin 3 → ℤ) :
    cleanTerm v h ρ μ n = cleanFun v h ρ μ (kAt v μ n) := rfl

/-- **The clean part is a *difference* whose sign is that of `2‖k‖² − (τ+c+√(τ²+2τc))`.**
This is the identity behind the sign row: with `t = τ(k)`, `c = c(k)` and `S = t+c+√(t²+2tc)`,
`cleanFun k = c²·(2‖k‖² − S)/(2‖k‖²·S)`. -/
lemma cleanFun_eq (v : ℝ³ → ℝ) (h : ScatSol v) (ρ μ : ℝ) {k : ℝ³}
    (hk : k ≠ 0) (hτ : 0 ≤ tauAt v μ k) (hc : 0 ≤ cAt v h ρ μ k)
    (hS : 0 < tauAt v μ k + cAt v h ρ μ k + Real.sqrt (tauAt v μ k ^ 2
      + 2 * tauAt v μ k * cAt v h ρ μ k)) :
    cleanFun v h ρ μ k
      = (cAt v h ρ μ k) ^ 2 * (2 * ‖k‖ ^ 2 - (tauAt v μ k + cAt v h ρ μ k
            + Real.sqrt (tauAt v μ k ^ 2 + 2 * tauAt v μ k * cAt v h ρ μ k)))
          / (2 * ‖k‖ ^ 2 * (tauAt v μ k + cAt v h ρ μ k
            + Real.sqrt (tauAt v μ k ^ 2 + 2 * tauAt v μ k * cAt v h ρ μ k))) := by
  set t := tauAt v μ k
  set c := cAt v h ρ μ k
  set S := t + c + Real.sqrt (t ^ 2 + 2 * t * c) with hSdef
  have hsq : (t + c) ^ 2 - c ^ 2 = t ^ 2 + 2 * t * c := by ring
  have htc : 0 ≤ t ^ 2 + 2 * t * c := by nlinarith [mul_nonneg hτ hc]
  have hprod : (t + c - Real.sqrt (t ^ 2 + 2 * t * c)) * S = c ^ 2 := by
    rw [hSdef]
    have h1 : (t + c - Real.sqrt (t ^ 2 + 2 * t * c)) * (t + c + Real.sqrt (t ^ 2 + 2 * t * c))
        = (t + c) ^ 2 - (Real.sqrt (t ^ 2 + 2 * t * c)) ^ 2 := by ring
    rw [h1, Real.sq_sqrt htc]
    ring
  have hR : (0 : ℝ) < ‖k‖ ^ 2 := pow_pos (norm_pos_iff.mpr hk) 2
  have hSne : S ≠ 0 := ne_of_gt hS
  have h1 : t + c - Real.sqrt (t ^ 2 + 2 * t * c) = c ^ 2 / S := (eq_div_iff hSne).mpr hprod
  rw [cleanFun, Work.BoseB6.bogZeroPoint, hsq, h1]
  have hRne : (2 : ℝ) * ‖k‖ ^ 2 ≠ 0 := by positivity
  field_simp
  ring

end Work.BoseBogFS
