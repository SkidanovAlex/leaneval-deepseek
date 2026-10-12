import ChallengeDeps
import Submission.Work.BoseBoxFock.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Adm` forces the diluteness `μ (a v)³ ≤ 1`

FS `sec:params` fixes the parameter block at the diluteness `t = μa³` through
`X = t^{1/323}`, `s = X`, `d = X⁶`, `ε_T = X^{23/4}`, `K_ℓ = X^{-3/2}`.  Among the
conditions they impose on the parameters is `con:eTdK`'s last clause

    ε_T ≤ s d K_ℓ ,

i.e. `t^{23/1292} ≤ t^{22/1292}` (since `s d K_ℓ = X^{1+6-3/2} = X^{11/2} =
t^{11/646} = t^{22/1292}`).  For `t > 1` the map `c ↦ t^c` is strictly increasing, so
`t^{22/1292} < t^{23/1292}` — a contradiction.  Hence every `ParamsOK` parameter block
(hence every `Adm` datum) carries the diluteness bound

    μ (a v)³ ≤ 1 .

This is the arithmetic fact that every consumer of `Work.BoseBoxFix.Adm` needs when it
upgrades a parameter comparison such as `d ≤ 1`, `ℓ ≥ a`, ... at small diluteness.

The same statement (with the same two-line proof) is available as
`Work.BoseBoxFock.paramsOK_fsParams_le_one` in `Submission/Work/BoseBoxFock/frkD4Aux.lean`
and as `Work.BoseB7.paramsOK_fsParams_le_one`; it is reproduced here so that this module
keeps its original, minimal import cone.
-/

namespace Work.BoseBoxFock.PCFU

set_option linter.unusedVariables false
set_option autoImplicit false

/-- **`ParamsOK (fsParams t) t` forces `t ≤ 1`.**  The conjunct `Con_eTdK` reads
`ε_T ≤ s · d · K_ℓ`, i.e. (at FS's power choice) `t^{23/1292} ≤ t^{22/1292}`; for `t > 1`
the map `c ↦ t^c` is increasing while `22/1292 < 23/1292`, a contradiction. -/
theorem paramsOK_fsParams_le_one' {t : ℝ}
    (h : Work.BoseBox.ParamsOK (Work.BoseBox.fsParams t) t) : t ≤ 1 := by
  by_contra hc
  rw [not_le] at hc
  have ht : 0 < t := lt_trans zero_lt_one hc
  have hle : (Work.BoseBox.fsParams t).eT
      ≤ (Work.BoseBox.fsParams t).s * (Work.BoseBox.fsParams t).d
        * (Work.BoseBox.fsParams t).Kl := h.eTdK.2.2
  simp only [Work.BoseBox.fsParams] at hle
  rw [Work.BoseBox.fsXp_mul ht, Work.BoseBox.fsXp_mul ht] at hle
  have hle' : t ^ ((23 : ℝ) / 1292) ≤ t ^ ((11 : ℝ) / 646) := by
    simpa only [Work.BoseBox.fsXp, show ((23 : ℝ) / 4) / 323 = 23 / 1292 by norm_num,
      show ((1 : ℝ) + 6 + -(3 / 2)) / 323 = 11 / 646 by norm_num] using hle
  have hlt : t ^ ((11 : ℝ) / 646) < t ^ ((23 : ℝ) / 1292) :=
    Real.rpow_lt_rpow_of_exponent_lt hc (by norm_num)
  linarith

theorem admDiluLeOne {v : EuclideanSpace ℝ (Fin 3) → ℝ} {ε₀ μ : ℝ}
    (hav : 0 < BoseGases.a v) (h : Work.BoseBoxFix.Adm v ε₀ μ) :
    μ * (BoseGases.a v) ^ 3 ≤ 1 := by
  obtain ⟨-, -, hOK⟩ := h
  have hP : Work.BoseBox.paramsAt μ (BoseGases.a v)
      = Work.BoseBox.fsParams (μ * (BoseGases.a v) ^ 3) := rfl
  rw [hP] at hOK
  exact paramsOK_fsParams_le_one' hOK

end Work.BoseBoxFock.PCFU
