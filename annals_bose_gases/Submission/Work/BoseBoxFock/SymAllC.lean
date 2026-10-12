import Mathlib.Analysis.CStarAlgebra.Classes
import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.Normed.Lp.lpSpace
import Submission.Work.BoseBoxFock.KzAllC
import Submission.Work.BoseBoxFock.symDiscrep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseBoxFock.SymAllC` — the discrepancy identity for `KzOpCAll`

`symDiscrep` (`symDiscrep.lean`) computes
`symR r − KzOpC (r²/ℓ³) = r²•D2F + r•D1F + D0F`.
Here the label-`0` row of `D2F` is *absorbed* into `KzOpCAll`, so the discrepancy
of the corrected operator is

    `symR r − KzOpCAll (r²/ℓ³) = r²•D2FAll + r•D1F + D0F`

at the honest environment (`Ŵ₁ω(0) = Ŵ₁ω(0)`, i.e. `E.W1omega 0 = E.W1omega0`).
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 8000000

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
variable {m : ℕ} [NeZero m]

/-- **The discrepancy identity for the corrected operator `KzOpCAll`.** -/
theorem symDiscrepAll (f g : Mode → Fin m → ℝ)
    (BNH : Work.BoseB4.cfock (Work.BoseB4.Excited m) →ₗ[ℂ] Work.BoseB4.cfock (Work.BoseB4.Excited m))
    (PHs : Finset Mode) (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode)
    (gHat0 : ℝ) (hℓ : 0 < E.ell)
    (hPH : PHs = F.PHset E)
    (hτ : ∀ k : Mode, E.tau (-k) = E.tau k)
    (hχ : ∀ k : Mode, E.hatChi (-k) = E.hatChi k)
    (hW : ∀ k : Mode, E.W1 (-k) = E.W1 k)
    (hWω : ∀ k : Mode, E.W1omega (-k) = E.W1omega k)
    (hωval : E.W1omega 0 = E.W1omega0)
    (r : ℝ) (hr : 0 ≤ r) :
    Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
        - Work.BoseBoxFock.KzOpCAll f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)
      = ((r ^ 2 : ℝ) : ℂ) • Work.BoseBoxFock.D2FAll f E gHat0
        + ((r : ℝ) : ℂ) • Work.BoseBoxFock.D1F f g E
        + Work.BoseBoxFock.D0F f E gHat0 := by
  have h1 := symDiscrep f g BNH PHs F E gHat0 hℓ hPH hτ hχ hW hWω hωval r hr
  have hρ : 0 ≤ r ^ 2 / E.ell ^ 3 := div_nonneg (sq_nonneg r) (by positivity)
  -- ## the scalar identity `r²·(2ℓ⁻³Ŵ₁ω(0)) = ρ(Ŵ₁ω(0) + Ŵ₁ω(0))` at `ρ = r²/ℓ³`
  have h3 : i3F E = (E.ell ^ 3)⁻¹ := by
    rw [i3F, Real.rpow_neg (le_of_lt hℓ)]
    exact congrArg Inv.inv (Real.rpow_natCast E.ell 3)
  have hscalR : r ^ 2 * (2 * i3F E * E.W1omega0)
      = (r ^ 2 / E.ell ^ 3) * (E.W1omega 0 + E.W1omega0) := by
    rw [hωval, h3, div_eq_mul_inv]
    ring
  have hscal : ((r ^ 2 : ℝ) : ℂ) * (((2 * i3F E * E.W1omega0 : ℝ)) : ℂ)
      = ((kz0Coef E (r ^ 2 / E.ell ^ 3) : ℝ) : ℂ) := by
    rw [kz0Coef_eq (E := E) hρ hℓ]
    exact_mod_cast hscalR
  -- ## the operator identities
  have hKz : Work.BoseBoxFock.KzOpCAll f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)
      = Work.BoseBoxFock.KzOpC f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)
        + ((kz0Coef E (r ^ 2 / E.ell ^ 3) : ℝ) : ℂ) • nOpC (f 0) :=
    KzOpCAll_def f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)
  have hkey : ((r ^ 2 : ℝ) : ℂ) • Work.BoseBoxFock.D2F f E gHat0
      = ((r ^ 2 : ℝ) : ℂ) • Work.BoseBoxFock.D2FAll f E gHat0
        + ((kz0Coef E (r ^ 2 / E.ell ^ 3) : ℝ) : ℂ) • nOpC (f 0) := by
    rw [D2F_eq_D2FAll, smul_add, smul_smul, hscal]
  have hsplit : Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
        - Work.BoseBoxFock.KzOpCAll f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)
      = (Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
          - Work.BoseBoxFock.KzOpC f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3))
        - ((kz0Coef E (r ^ 2 / E.ell ^ 3) : ℝ) : ℂ) • nOpC (f 0) := by
    rw [hKz]
    abel
  calc Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
        - Work.BoseBoxFock.KzOpCAll f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3)
      = (Work.BoseBoxFock.symR f g BNH PHs E gHat0 r
          - Work.BoseBoxFock.KzOpC f g BNH F E gHat0 (r ^ 2 / E.ell ^ 3))
        - ((kz0Coef E (r ^ 2 / E.ell ^ 3) : ℝ) : ℂ) • nOpC (f 0) := hsplit
    _ = (((r ^ 2 : ℝ) : ℂ) • Work.BoseBoxFock.D2F f E gHat0
          + ((r : ℝ) : ℂ) • Work.BoseBoxFock.D1F f g E
          + Work.BoseBoxFock.D0F f E gHat0)
        - ((kz0Coef E (r ^ 2 / E.ell ^ 3) : ℝ) : ℂ) • nOpC (f 0) := by rw [h1]
    _ = ((((r ^ 2 : ℝ) : ℂ) • Work.BoseBoxFock.D2FAll f E gHat0
            + ((kz0Coef E (r ^ 2 / E.ell ^ 3) : ℝ) : ℂ) • nOpC (f 0))
          + ((r : ℝ) : ℂ) • Work.BoseBoxFock.D1F f g E
          + Work.BoseBoxFock.D0F f E gHat0)
        - ((kz0Coef E (r ^ 2 / E.ell ^ 3) : ℝ) : ℂ) • nOpC (f 0) := by rw [hkey]
    _ = ((r ^ 2 : ℝ) : ℂ) • Work.BoseBoxFock.D2FAll f E gHat0
        + ((r : ℝ) : ℂ) • Work.BoseBoxFock.D1F f g E
        + Work.BoseBoxFock.D0F f E gHat0 := by abel

end Work.BoseBoxFock
