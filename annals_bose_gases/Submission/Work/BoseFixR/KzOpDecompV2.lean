import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseFixR.Defs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseFixR.KzOpDecompV2` — the `control3Q` glue for the corrected `KzOp`

`KzOp` carries FS `eq:SimplifyKz`'s full `c`-number term
`ℓ³(½ρ_z²ĝω(0) − μĝ(0)ρ_z + ½(ρ_z−μ)²ĝ(0))`, and its `§10` group is written
term-by-term (`T.N`, `T.NH`, `T.linOpT`, `F.Q2ex`, `T.Q3T`).  This file proves that
that operator is *exactly* the sum of the objects the children (`RB4box`, `RB5`,
`RB67`) trade in:

* the `c`-number term `ℓ³(−½μ²ĝ(0) + ½(ρ−μ)²ĝ(0) + ½ρ²Ŵ₁ω(0))·𝟙`,
* `KzBog − dNumOpR` (the Bogoliubov quadratic minus the `𝒟`-weighted number
  operator, FS `eq:BogHamDiag`),
* the `χ`-mode number term `((ρ−μ)Ŵ₁(0))·n₊`,
* **one** `T.controlWordT (KzEnvAt E ρ)` (FS `eq:Q3Cancels`: `dNumOpR + Q₃ + Q₂^ex
  + lin + (b/50)gap`),
* the extra gap reserve `(b/2 − b/50)·gapOpT`.

The content is the gap bookkeeping: `gapOpT E = ℓ⁻²·N + (ε_T(dℓ)⁻²)·NH` while
`KzOp`'s gap terms are `(b/2ℓ²)·N + (ε_T b/(2d²ℓ²))·NH`, and
`(b/2 − b/50) + b/50 = b/2` distributes the reserve of `controlWordT`.  The only
real input is `x^(-(2:ℝ)) = (x²)⁻¹` for `x = ℓ` and `x = d·ℓ` (with `ℓ, d ≠ 0`).

`KzEnvAt E ρ` only re-points `z`, `A`, `B`, so every parameter occurring in the gap
terms (`ell`, `d`, `eT`, `b`) is *definitionally* the one of the outer `E`.
-/

namespace Work.BoseFixR

set_option linter.unusedVariables false

/-- `x^(-(2:ℝ)) = (x²)⁻¹` for **every** real `x`: the exponent is an (even,
negative) integer, so `Real.rpow` is the usual integer power (`Real.rpow_intCast`)
and the claim is `zpow_neg`.  No sign hypothesis: this is why `KzOpDecompV2` only
needs `E.ell ≠ 0`, `E.d ≠ 0`. -/
lemma rpow_neg_two_eq_inv_sq (x : ℝ) : x ^ (-(2 : ℝ)) = (x ^ 2)⁻¹ := by
  rw [show (-(2 : ℝ)) = ((-2 : ℤ) : ℝ) by norm_num, Real.rpow_intCast]
  simp only [zpow_neg, zpow_ofNat]

theorem KzOpDecompV2 {Mode : Type} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (T : Work.BoseB7A.TildeData F) (E : Work.BoseB7.Q3Env Mode)
    (gHat0 ρ : ℝ) (hℓ : E.ell ≠ 0) (hd : E.d ≠ 0) :
    Work.BoseFixR.KzOp F T E gHat0 ρ
      = (E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0 + (1 / 2) * (ρ - E.mu) ^ 2 * gHat0
            + (1 / 2) * ρ ^ 2 * E.W1omega0)) • (1 : F.H →ₗ[ℝ] F.H)
        + (Work.BoseFixR.KzBog F E ρ
            - F.dNumOpR (Work.BoseFixR.KzEnvAt E ρ) (fun _ => True))
        + (((ρ - E.mu) * E.W1 0) • F.nPlus)
        + T.controlWordT (Work.BoseFixR.KzEnvAt E ρ)
        + (E.b / 2 - E.b / 50) • T.gapOpT (Work.BoseFixR.KzEnvAt E ρ) := by
  -- the `N`-coefficient of the gap: `b/2 · ℓ⁻² = b/(2ℓ²)`
  have hcoef1 : (E.b / 2) * E.ell ^ (-(2 : ℝ)) = E.b / (2 * E.ell ^ 2) := by
    rw [rpow_neg_two_eq_inv_sq]
    field_simp
  -- the `NH`-coefficient of the gap: `b/2 · ε_T (dℓ)⁻² = ε_T b/(2d²ℓ²)`
  have hcoef2 : (E.b / 2) * (E.eT * (E.d * E.ell) ^ (-(2 : ℝ)))
      = E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2) := by
    rw [rpow_neg_two_eq_inv_sq, mul_pow]
    field_simp
  -- the gap terms of `KzOp` are `b/2` times the gap operator of `KzEnvAt E ρ`
  have hgap : (E.b / (2 * E.ell ^ 2)) • T.N
        + (E.eT * E.b / (2 * E.d ^ 2 * E.ell ^ 2)) • T.NH
      = (E.b / 2) • T.gapOpT (KzEnvAt E ρ) := by
    simp only [KzEnvAt, Work.BoseB7A.TildeData.gapOpT, smul_add, smul_smul]
    rw [hcoef1, hcoef2]
  -- the `b/50` reserve sitting in `controlWordT` completes `b/2 - b/50` to `b/2`
  have hsplit : (E.b / 2 - E.b / 50) • T.gapOpT (KzEnvAt E ρ)
        + (E.b / 50) • T.gapOpT (KzEnvAt E ρ)
      = (E.b / 2) • T.gapOpT (KzEnvAt E ρ) := by
    rw [← add_smul]
    congr 1
    ring
  -- now unfold both sides and cancel `dNumOpR` against `− dNumOpR`
  simp only [KzOp, Work.BoseB7A.TildeData.controlWordT]
  rw [hgap, hsplit.symm]
  simp only [KzEnvAt]
  abel

end Work.BoseFixR
