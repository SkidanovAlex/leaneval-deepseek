import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBogFS.Final
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBogFS.ReserveArith` — the optimal Cauchy–Schwarz parameter

`reserveLoss` (`Final.lean`) is

  `Res(σ) = σ·Kbar + σ·S + (1+σ⁻¹)·G`,  `Kbar = winKbar E Dsup`,  `S = zpKapSum E ρ`,

the scalar cost of trading the corpus's *unshifted* `dNumOpR` for the shifted diagonal
(`normSq_bOp_le`: `‖b_kx‖² ≤ (1+σ)‖b̂_kx‖² + (1+σ⁻¹)γ_k²‖x‖²`).  The free parameter `σ > 0`
has to be chosen small compared with the §11 bracket but large compared with the
(super-polynomially small) `G = Σ_{RHi}𝒟_kγ_k²`.

This module makes the choice **explicit**: `σ = √(G/(Kbar+S))` is the exact minimiser of
`σ(Kbar+S) + σ⁻¹G`, and gives

  `Res(σ) = 2√(G(Kbar+S)) + G`.

So the `hResB` slot of `bogOpBoundFS_of_fsData`/`bogOpBoundFS_of_estimates` is
**equivalent to the single window condition**

  `2√(G·(winKbar E Dsup + zpKapSum E ρ)) + G ≤ C₅·errBracket v R μ`,

which is what FS's parameter choice has to meet (`G` is super-polynomially small on `RHi`,
so the window is enormous).  No `σ` remains in the interface.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open Work.BoseB7

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- The optimal Cauchy–Schwarz parameter of the reserve: `σ = √(G/(Kbar+S))`. -/
def sigmaChoice (E : Q3Env Mode) (ρ Dsup G : ℝ) : ℝ :=
  Real.sqrt (G / (winKbar E Dsup + zpKapSum E ρ))

/-- **The reserve cost at the optimal `σ`.**  If the geometric-mean window condition
`2√(G(Kbar+S)) + G ≤ B` holds, then `reserveLoss` at `σ = sigmaChoice` is at most `B`. -/
theorem reserveLoss_sigmaChoice_le (E : Q3Env Mode) (ρ Dsup G B : ℝ)
    (hG0 : 0 ≤ G) (hS : 0 < winKbar E Dsup + zpKapSum E ρ)
    (hB : 2 * Real.sqrt (G * (winKbar E Dsup + zpKapSum E ρ)) + G ≤ B) :
    reserveLoss E ρ Dsup G (sigmaChoice E ρ Dsup G) ≤ B := by
  have hSnn : 0 ≤ winKbar E Dsup + zpKapSum E ρ := hS.le
  have hSne : winKbar E Dsup + zpKapSum E ρ ≠ 0 := ne_of_gt hS
  have hGS : 0 ≤ G * (winKbar E Dsup + zpKapSum E ρ) := mul_nonneg hG0 hSnn
  have hGS' : 0 ≤ G / (winKbar E Dsup + zpKapSum E ρ) := div_nonneg hG0 hSnn
  -- `σ·(Kbar+S) = √(G(Kbar+S))`
  have hnn1 : 0 ≤ sigmaChoice E ρ Dsup G * (winKbar E Dsup + zpKapSum E ρ) :=
    mul_nonneg (Real.sqrt_nonneg _) hSnn
  have hsq1 : (sigmaChoice E ρ Dsup G * (winKbar E Dsup + zpKapSum E ρ)) ^ 2
      = G * (winKbar E Dsup + zpKapSum E ρ) := by
    rw [mul_pow, sigmaChoice, Real.sq_sqrt hGS']
    field_simp
  have h1 : sigmaChoice E ρ Dsup G * (winKbar E Dsup + zpKapSum E ρ)
      = Real.sqrt (G * (winKbar E Dsup + zpKapSum E ρ)) := by
    have h := Real.sqrt_sq hnn1
    rw [hsq1] at h
    exact h.symm
  -- `σ·√(G(Kbar+S)) = G`
  have hnn4 : 0 ≤ sigmaChoice E ρ Dsup G
      * Real.sqrt (G * (winKbar E Dsup + zpKapSum E ρ)) :=
    mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)
  have hsq4 : (sigmaChoice E ρ Dsup G
      * Real.sqrt (G * (winKbar E Dsup + zpKapSum E ρ))) ^ 2 = G ^ 2 := by
    rw [mul_pow, sigmaChoice, Real.sq_sqrt hGS', Real.sq_sqrt hGS]
    field_simp
  have h4 : sigmaChoice E ρ Dsup G * Real.sqrt (G * (winKbar E Dsup + zpKapSum E ρ)) = G := by
    have h := Real.sqrt_sq hnn4
    rw [hsq4, Real.sqrt_sq hG0] at h
    exact h.symm
  -- `σ⁻¹·G = √(G(Kbar+S))`
  have h2 : (sigmaChoice E ρ Dsup G)⁻¹ * G
      = Real.sqrt (G * (winKbar E Dsup + zpKapSum E ρ)) := by
    by_cases hG : G = 0
    · rw [hG]
      simp
    · have hGpos : 0 < G := lt_of_le_of_ne hG0 (Ne.symm hG)
      have hσpos : 0 < sigmaChoice E ρ Dsup G :=
        Real.sqrt_pos.mpr (div_pos hGpos hS)
      refine mul_left_cancel₀ (ne_of_gt hσpos) ?_
      rw [← mul_assoc, mul_inv_cancel₀ (ne_of_gt hσpos), one_mul, h4]
  rw [reserveLoss]
  have hfac : sigmaChoice E ρ Dsup G * winKbar E Dsup
      + sigmaChoice E ρ Dsup G * zpKapSum E ρ
      = sigmaChoice E ρ Dsup G * (winKbar E Dsup + zpKapSum E ρ) := by ring
  rw [hfac, h1]
  have hsplit : (1 + (sigmaChoice E ρ Dsup G)⁻¹) * G
      = G + (sigmaChoice E ρ Dsup G)⁻¹ * G := by ring
  rw [hsplit, h2]
  linarith [hB]

/-- **The `hResB` slot of the assembly, discharged.**  The window condition in the shape
`bogOpBoundFS_of_fsData` consumes it: with `σ := sigmaChoice E ρ Dsup G` the reserve cost is
within `C₅` times the §11 bracket. -/
theorem hResB_of_window (v : ℝ³ → ℝ) (R μ : ℝ) (E : Q3Env Mode) (ρ Dsup G C₅ : ℝ)
    (hG0 : 0 ≤ G) (hS : 0 < winKbar E Dsup + zpKapSum E ρ)
    (hwin : 2 * Real.sqrt (G * (winKbar E Dsup + zpKapSum E ρ)) + G
      ≤ C₅ * errBracket v R μ) :
    reserveLoss E ρ Dsup G (sigmaChoice E ρ Dsup G) ≤ C₅ * errBracket v R μ :=
  reserveLoss_sigmaChoice_le E ρ Dsup G (C₅ * errBracket v R μ) hG0 hS hwin

end Work.BoseBogFS
