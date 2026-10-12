import ChallengeDeps
import Mathlib.Algebra.Order.Star.Real
import Submission.Work.BoseBogFS.honest_linHi
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBogFS.bogErrAux` — the budget side of the clean Riemann row

`errBracket v R μ = μ²·a·ℓ³·√(dil)·(X² + (R/a)²√(dil) + X^{1/5})`, so keeping only the
*last* term of the bracket and using `√(dil) = X^{161.5}`, `μℓ³ = X^{-166}` gives
`errBracket ≥ μ·a·X^{-4.3}`.  This is the inequality that turns the scaled lattice-sum
bounds (`Σ'bogSj ≤ 2000·X^{-4.3}`, see `FINDING_cleanFun_tsum_session20.md` §1) into the
physical bound `ρ·a·Σ'bogSj ≤ 6600·errBracket`.
-/

noncomputable section

open scoped Real Topology BigOperators

namespace Work.BoseBogFS

open _root_.BoseGases Work.BoseFixR

set_option autoImplicit false
set_option linter.unusedVariables false

local notation "E3" => EuclideanSpace ℝ (Fin 3)

/-- **`μ a v X^{-4.3} ≤ errBracket v R μ`** (`X = fsX v μ`). -/
theorem errBracket_ge_mu_a_X43 {v : E3 → ℝ} {μ R : ℝ} (hμ : 0 < μ) (hav : 0 < a v) :
    μ * a v * (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ) ≤ errBracket v R μ := by
  have ht0 : 0 < Work.BoseFixR.dil v μ := mul_pos hμ (pow_pos hav 3)
  have hXeq : (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ)
      = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) (-(43 / 10)) := by
    rw [Work.BoseFixR.fsX, Work.BoseBox.fsXp, ← Real.rpow_mul ht0.le]
    congr 1
    ring
  have hsqrt : Real.sqrt (Work.BoseFixR.dil v μ)
      = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) (323 / 2) := by
    rw [Real.sqrt_eq_rpow, Work.BoseBox.fsXp]
    congr 1
    norm_num
  have herrExp : Work.BoseFixR.errExp v μ
      = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) (1 / 5) := by
    rw [Work.BoseFixR.errExp, Work.BoseBox.fsXp]
    congr 1
    norm_num
  have hmue : μ * (Work.BoseFixR.ell v μ) ^ 3
      = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) (-166) := mu_ell_cube_eq hμ hav
  have hprod : Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) (-166)
      * (Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) (323 / 2)
        * Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) (1 / 5))
      = Work.BoseBox.fsXp (Work.BoseFixR.dil v μ) (-(43 / 10)) := by
    rw [Work.BoseBox.fsXp_mul ht0, Work.BoseBox.fsXp_mul ht0]
    congr 1
    norm_num
  have hkey : μ ^ 2 * a v * (Work.BoseFixR.ell v μ) ^ 3
        * Real.sqrt (Work.BoseFixR.dil v μ) * Work.BoseFixR.errExp v μ
      = μ * a v * (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ) := by
    have h1 : μ ^ 2 * a v * (Work.BoseFixR.ell v μ) ^ 3
          * Real.sqrt (Work.BoseFixR.dil v μ) * Work.BoseFixR.errExp v μ
        = (μ * a v) * ((μ * (Work.BoseFixR.ell v μ) ^ 3)
            * (Real.sqrt (Work.BoseFixR.dil v μ) * Work.BoseFixR.errExp v μ)) := by ring
    rw [h1, hmue, hsqrt, herrExp, hXeq, hprod]
  have hell : 0 < Work.BoseFixR.ell v μ := ell_pos_bog v hμ hav
  have hnn : 0 ≤ μ ^ 2 * a v * (Work.BoseFixR.ell v μ) ^ 3
      * Real.sqrt (Work.BoseFixR.dil v μ) :=
    mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg μ) hav.le) (pow_nonneg hell.le 3))
      (Real.sqrt_nonneg _)
  have hbracket : Work.BoseFixR.errExp v μ
      ≤ Work.BoseFixR.fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ)
        + Work.BoseFixR.errExp v μ := by
    have h1 : 0 ≤ Work.BoseFixR.fsX v μ ^ 2 := sq_nonneg _
    have h2 : 0 ≤ (R / a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ) :=
      mul_nonneg (sq_nonneg _) (Real.sqrt_nonneg _)
    linarith
  rw [errBracket, Work.BoseFixR.ell3]
  calc μ * a v * (Work.BoseFixR.fsX v μ) ^ (-(43 / 10) : ℝ)
      = μ ^ 2 * a v * (Work.BoseFixR.ell v μ) ^ 3
          * Real.sqrt (Work.BoseFixR.dil v μ) * Work.BoseFixR.errExp v μ := hkey.symm
    _ ≤ μ ^ 2 * a v * (Work.BoseFixR.ell v μ) ^ 3 * Real.sqrt (Work.BoseFixR.dil v μ)
          * (Work.BoseFixR.fsX v μ ^ 2 + (R / a v) ^ 2 * Real.sqrt (Work.BoseFixR.dil v μ)
            + Work.BoseFixR.errExp v μ) :=
        mul_le_mul_of_nonneg_left hbracket hnn

end Work.BoseBogFS
