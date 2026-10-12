import Mathlib.Algebra.Module.LinearMap.End
import Mathlib.Algebra.BigOperators.Group.Finset.Defs
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Submission.Work.BoseBoxFock.KzAll
import Submission.Work.BoseRowQ2.Rows
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseRowQ2.KzBridge` — `KzOpFSAll` is `KzOpFS` with `Q2ex` replaced by `Q2exAll`

The lead asked (23:50) for the bridge between

* `Work.BoseBoxFock.KzOpFSAll` — `KzOpFS` plus the adjoined label-`0` row
  `ρ_z(Ŵ₁ω(0)+Ŵ₁ω(0))·nOp 0` (`BoseBoxFock/KzAll.lean`, which builds), and
* `Work.BoseRowQ2`'s corrected `Q2exAll = Q2ex + (2ρŴ₁ω(0))·n₀` (`Defs.lean`),

namely that **`KzOpFSAll` is exactly `KzOpFS` with the `F.Q2ex (KzEnvAt E ρ)` slot
replaced by `F.Q2exAll (KzEnvAt E ρ)`**.  The proof is
`FockData.Q2exAll_eq_Q2ex_add`, i.e. the label-`0` row of `KzAll` *is* the
difference between `Q2exAll` and `Q2ex` — the two areas agree on the correction.

`KzOpFSWithQ` below reproduces `KzOpFS`'s body (`BoseBoxFock/Defs.lean:298`)
verbatim with the `Q₂^ex` slot abstracted, so that the "replacement" is a
statement of equality between two definitions rather than a description.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseRowQ2

open Work.BoseB7 Work.BoseB7A Work.BoseFixR Work.BoseBoxFock

set_option linter.unusedVariables false
set_option linter.unusedSectionVars false

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]

/-- **FS `eq:Kz` with an arbitrary `Q₂^ex` slot** — `Work.BoseBoxFock.KzOpFS`'s body
verbatim (`BoseBoxFock/Defs.lean:298`), with `F.Q2ex (KzEnvAt E ρ)` abstracted to
`Q`. -/
def KzOpFSWithQ (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 : ℝ) (ρ : ℝ) (Q : F.H →ₗ[ℝ] F.H) :
    F.H →ₗ[ℝ] F.H :=
  ((E.b / (2 * E.ell ^ 2)) • T.N)
    + ((E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • T.NH)
    + ((E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0 + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0
        + (1 / 2) * ρ ^ 2 * E.W1omega0)) • (1 : F.H →ₗ[ℝ] F.H))
    + KzBogFS F E ρ
    + (((ρ - E.mu) * E.W1 0) • ∑ k : Mode, F.nOp k)
    + T.linOpT (KzEnvAt E ρ)
    + Q
    + T.Q3T (KzEnvAt E ρ)

/-- `KzOpFS` is `KzOpFSWithQ` at its own `Q₂^ex`. -/
theorem KzOpFS_eq_withQ (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ) :
    KzOpFS F T E gHat0 ρ
      = KzOpFSWithQ F T E gHat0 ρ (F.Q2ex (KzEnvAt E ρ)) := rfl

/-- `KzOpFSWithQ` is additive in its `Q` slot (it is `const + Q`). -/
theorem KzOpFSWithQ_add (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ) (A B : F.H →ₗ[ℝ] F.H) :
    KzOpFSWithQ F T E gHat0 ρ (A + B) = KzOpFSWithQ F T E gHat0 ρ A + B := by
  simp only [KzOpFSWithQ]
  abel

/-- **The bridge, in `KzAll`'s vocabulary**: the adjoined row `KzRow0` is exactly
the difference `Q2exAll - Q2ex`. -/
theorem KzRow0_eq_Q2exAll_sub (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (ρ : ℝ) :
    KzRow0 F E ρ = F.Q2exAll (KzEnvAt E ρ) - F.Q2ex (KzEnvAt E ρ) := by
  rw [KzRow0, kz0Coef, ← FockData.Q2exAll_eq_Q2ex_add]
  abel

/-- **The bridge (lead's form)**: `KzOpFSAll` is `KzOpFS` with its `Q₂^ex` slot
replaced by `Q2exAll`. -/
theorem KzOpFSAll_eq_KzOpFS_withQ (F : Work.BoseB7.FockData Mode)
    (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ) :
    KzOpFSAll F T E gHat0 ρ
      = KzOpFSWithQ F T E gHat0 ρ (F.Q2exAll (KzEnvAt E ρ)) := by
  have hadd := KzOpFSWithQ_add F T E gHat0 ρ (F.Q2ex (KzEnvAt E ρ))
    (F.Q2exAll (KzEnvAt E ρ) - F.Q2ex (KzEnvAt E ρ))
  rw [KzOpFSAll, KzOpFS_eq_withQ, KzRow0_eq_Q2exAll_sub, ← hadd]
  congr 1
  abel

/-- The same as a difference: `KzOpFSAll = KzOpFS + (Q2exAll - Q2ex)`. -/
theorem KzOpFSAll_eq_KzOpFS_add_sub (F : Work.BoseB7.FockData Mode)
    (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ) :
    KzOpFSAll F T E gHat0 ρ
      = KzOpFS F T E gHat0 ρ + (F.Q2exAll (KzEnvAt E ρ) - F.Q2ex (KzEnvAt E ρ)) := by
  rw [KzOpFSAll, KzOpFS_eq_withQ, KzRow0_eq_Q2exAll_sub]

/-- The window infima agree as well. -/
theorem KzValFSAll_eq (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F)
    (E : Work.BoseB7.Q3Env Mode) (gHat0 ρ : ℝ) :
    KzValFSAll F T E gHat0 ρ
      = ⨅ (f : {f : F.H // T.NWindow E.bigM f ∧ f ≠ 0}),
          F.qw f.1 (KzOpFSWithQ F T E gHat0 ρ (F.Q2exAll (KzEnvAt E ρ))) / F.normSq f.1 := by
  simp only [KzValFSAll, KzOpFSAll_eq_KzOpFS_withQ]

end Work.BoseRowQ2
