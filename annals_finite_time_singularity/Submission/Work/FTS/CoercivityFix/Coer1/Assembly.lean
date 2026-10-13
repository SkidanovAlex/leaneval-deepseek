/-
# The numerical bookkeeping of the level-1 coercivity of `Lhat`

This file assembles the target

  `2 * |f|²_{ℋ¹} ≤ H1IP α (Lhat f) f`

from the four coercivity estimates of the clean operator `Lhat` and the identification
`|f|²_{ℋ¹} = E_{z,θ}¹(f)`.  The four estimates (`est_A` … `est_D` of `Estimates.lean`) are the
*only* inputs: the bookkeeping below is pure arithmetic, with the constants of `H1IP`
(`10, 10¹⁰, 10¹⁷, 10²¹`) absorbing the errors.

Writing `X = √E_η(D_zf)`, `Y = √E_η(f)`, `Z = √E_γ(D_θf)` for the square roots of the three
energies, the estimates are

* `A ≥ (47/100)X² − (3/4)(Y+Z)X`  (the `η`-weighted `D_z`-pairing; the subtraction is the
  `D_z`-commutator defect `Ê₂f`),
* `B ≥ (47/100)Y²`,
* `C ≥ (1/8)∫∫ f²w² − 6∫∫ (D_θf)²w²`,
* `D ≥ (17/40)Z²`,

and the target follows by AM–GM (`(a−b)² ≥ 0`) for the two cross terms `YX`, `ZX`:
`10·A` pays `4.7X²` against the `2X²` needed, and the (astronomically large) coefficients
`4.7·10⁹ Y²` and `4.25·10²⁰ Z²` absorb everything else.
-/
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.CoercivityFix.Coer1.Defs

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section
open scoped Real Topology
open MeasureTheory Set Filter

namespace Work.FTS.CoercivityFix.Coer1

open Work.FTS.Galerkin (Fn)

set_option autoImplicit false

/-- The four coercivity estimates of `Lhat` imply the level-1 coercivity, together with the
identification of the `ℋ¹`-energy and the domination of the plain `D_θ`-energy by the
`γ`-weighted one. -/
theorem assembly (α : ℝ) (hα : 0 < α) (hα1 : α ≤ 1 / 4) {f : Fn}
    (hHk : Work.Spaces.HkSq α 1 f
      = En Work.Spaces.eta (Work.Spaces.Dz f) + En Work.Spaces.eta f
        + En (Work.Spaces.gam α) (Work.Spaces.Dth f))
    (hW : Work.Coercivity.EDthW f ≤ En (Work.Spaces.gam α) (Work.Spaces.Dth f))
    (hA : (47 / 100) * En Work.Spaces.eta (Work.Spaces.Dz f)
      - (En Work.Spaces.eta f + 4 * En (Work.Spaces.gam α) (Work.Spaces.Dth f)
          + (1 / 8) * En Work.Spaces.eta (Work.Spaces.Dz f))
      ≤ Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f))
          (Work.Spaces.Dz f))
    (hB : (47 / 100) * En Work.Spaces.eta f
      ≤ Work.Coercivity.wip (Rho Work.Spaces.eta) (Work.FTS.CoercivityFix.Lhat f) f)
    (hC : (1 / 8) * EnOne f - 6 * Work.Coercivity.EDthW f
      ≤ Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2) (Work.FTS.CoercivityFix.Lhat f) f)
    (hD : (17 / 40) * En (Work.Spaces.gam α) (Work.Spaces.Dth f)
      ≤ Work.Coercivity.wip (Rho (Work.Spaces.gam α))
          (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f)) :
    2 * Work.Spaces.HkSq α 1 f
      ≤ Work.Coercivity.H1IP α (Work.FTS.CoercivityFix.Lhat f) f := by
  -- ## the `H1IP` is the sum of the four pairings
  have hH1 : Work.Coercivity.H1IP α (Work.FTS.CoercivityFix.Lhat f) f
      = 10 * Work.Coercivity.wip (Rho Work.Spaces.eta)
            (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f)
        + (10 : ℝ) ^ 10 * Work.Coercivity.wip (Rho Work.Spaces.eta)
            (Work.FTS.CoercivityFix.Lhat f) f
        + (10 : ℝ) ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
            (Work.FTS.CoercivityFix.Lhat f) f
        + (10 : ℝ) ^ 21 * Work.Coercivity.wip (Rho (Work.Spaces.gam α))
            (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f) := by
    rw [Work.Coercivity.H1IP]
    rfl
  rw [hH1, hHk]
  -- ## the three energies as squares of their square roots
  set X := Real.sqrt (En Work.Spaces.eta (Work.Spaces.Dz f)) with hXdef
  set Y := Real.sqrt (En Work.Spaces.eta f) with hYdef
  set Z := Real.sqrt (En (Work.Spaces.gam α) (Work.Spaces.Dth f)) with hZdef
  have hXn : 0 ≤ En Work.Spaces.eta (Work.Spaces.Dz f) := En_nonneg _ _
  have hYn : 0 ≤ En Work.Spaces.eta f := En_nonneg _ _
  have hZn : 0 ≤ En (Work.Spaces.gam α) (Work.Spaces.Dth f) := En_nonneg _ _
  have hX2 : X ^ 2 = En Work.Spaces.eta (Work.Spaces.Dz f) := Real.sq_sqrt hXn
  have hY2 : Y ^ 2 = En Work.Spaces.eta f := Real.sq_sqrt hYn
  have hZ2 : Z ^ 2 = En (Work.Spaces.gam α) (Work.Spaces.Dth f) := Real.sq_sqrt hZn
  have hXn' : 0 ≤ X := Real.sqrt_nonneg _
  have hYn' : 0 ≤ Y := Real.sqrt_nonneg _
  -- ## the scaled estimates
  have hA' : (47 / 10) * X ^ 2 - (10 * Y ^ 2 + 40 * Z ^ 2 + (5 / 4) * X ^ 2)
      ≤ 10 * Work.Coercivity.wip
      (Rho Work.Spaces.eta) (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f) := by
    have h := mul_le_mul_of_nonneg_left hA (show (0 : ℝ) ≤ 10 by norm_num)
    rw [← hX2, ← hY2, ← hZ2] at h
    linarith [h]
  have hB' : (47 / 100) * (10 : ℝ) ^ 10 * Y ^ 2 ≤ (10 : ℝ) ^ 10 * Work.Coercivity.wip
      (Rho Work.Spaces.eta) (Work.FTS.CoercivityFix.Lhat f) f := by
    have h := mul_le_mul_of_nonneg_left hB (show (0 : ℝ) ≤ (10 : ℝ) ^ 10 by norm_num)
    rw [hY2]
    linarith [h]
  have hC' : (1 / 8) * (10 : ℝ) ^ 17 * EnOne f - 6 * (10 : ℝ) ^ 17 * Work.Coercivity.EDthW f
      ≤ (10 : ℝ) ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
          (Work.FTS.CoercivityFix.Lhat f) f := by
    have h := mul_le_mul_of_nonneg_left hC (show (0 : ℝ) ≤ (10 : ℝ) ^ 17 by norm_num)
    linarith [h]
  have hD' : (17 / 40) * (10 : ℝ) ^ 21 * Z ^ 2 ≤ (10 : ℝ) ^ 21 * Work.Coercivity.wip
      (Rho (Work.Spaces.gam α)) (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f))
        (Work.Spaces.Dth f) := by
    have h := mul_le_mul_of_nonneg_left hD (show (0 : ℝ) ≤ (10 : ℝ) ^ 21 by norm_num)
    rw [hZ2]
    linarith [h]
  -- ## the two AM–GM steps

  have hWc : (6 : ℝ) * (10 : ℝ) ^ 17 * Work.Coercivity.EDthW f
      ≤ 6 * (10 : ℝ) ^ 17 * Z ^ 2 := by
    have h := mul_le_mul_of_nonneg_left hW (show (0 : ℝ) ≤ 6 * (10 : ℝ) ^ 17 by norm_num)
    linarith [h, hZ2]
  -- ## conclusion
  have hfin : 2 * X ^ 2 + 2 * Y ^ 2 + 2 * Z ^ 2
      ≤ 10 * Work.Coercivity.wip (Rho Work.Spaces.eta)
            (Work.Spaces.Dz (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dz f)
        + (10 : ℝ) ^ 10 * Work.Coercivity.wip (Rho Work.Spaces.eta)
            (Work.FTS.CoercivityFix.Lhat f) f
        + (10 : ℝ) ^ 17 * Work.Coercivity.wip (fun z _ => Work.Spaces.w z ^ 2)
            (Work.FTS.CoercivityFix.Lhat f) f
        + (10 : ℝ) ^ 21 * Work.Coercivity.wip (Rho (Work.Spaces.gam α))
            (Work.Spaces.Dth (Work.FTS.CoercivityFix.Lhat f)) (Work.Spaces.Dth f) := by
    have hEn : 0 ≤ EnOne f := EnOne_nonneg f
    nlinarith [hA', hB', hC', hD', hWc, hEn]
  rw [hX2, hY2, hZ2] at hfin
  linarith [hfin]

end Work.FTS.CoercivityFix.Coer1
