import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseBoxFock.SymBlocks
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseBoxFock.SymScalar` — the scalar (`rpow`/`sqrt`) bookkeeping for `symDiscrep`

`symDiscrep` compares `symR r − KzOpC (r²/ℓ³)` with `r²•D2F + r•D1F + D0F`, so every
occurrence of the condensate density `ρ = r²/ℓ³` has to be rewritten as `r² * i3F E`
(with `i3F E = ℓ^{-3}` kept as an opaque atom), and the four places where `ℓ³` occurs
explicitly have to be disposed of:

* `KzBogC`'s linear coefficient contains `Real.sqrt (ρ ℓ³)`, which is `r` (here `r ≥ 0`);
* `KzOpC`'s `c`-number row is `ℓ³(−½μ²ĝ(0) + ½(ρ−μ)²ĝ(0) + ½ρ²Ŵ₁ω(0))`, which is
  `cHCF·r⁴ − μĝ(0)·r²`;
* the repointed environment `KzEnvAt E (r²i3F E)` has `.rho = r²i3F E` and `.z = r`;
* the cubic row `Q3TC` carries `z/ℓ³ = r i3F E`.

All identities are pure real arithmetic obtained by unfolding `i3F` (which is
`(ℓ³)⁻¹` for `ℓ > 0`) and `cHCF`, and clearing the (nonzero) powers of `ℓ`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseBoxFock

open Work.BoseB4

set_option autoImplicit false
set_option linter.unusedVariables false

variable {m : ℕ} [NeZero m]

/-- `i3F E = ℓ^{-3}` is the inverse of `ℓ³` (for `ℓ > 0`). -/
theorem i3F_eq_inv {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hℓ : 0 < E.ell) :
    i3F E = (E.ell ^ 3)⁻¹ := by
  rw [i3F, Real.rpow_neg (le_of_lt hℓ)]
  norm_num

/-- `i3F E * ℓ³ = 1`. -/
theorem i3F_mul_ell3 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hℓ : 0 < E.ell) : i3F E * E.ell ^ 3 = 1 := by
  rw [i3F_eq_inv E hℓ]
  exact inv_mul_cancel₀ (by positivity)

/-- `i3F E` is positive. -/
theorem i3F_pos {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hℓ : 0 < E.ell) : 0 < i3F E := by
  rw [i3F_eq_inv E hℓ]
  positivity

/-- Division by `ℓ³` is multiplication by `i3F E`. -/
theorem div_ell3_eq_mul_i3 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hℓ : 0 < E.ell) (x : ℝ) :
    x / E.ell ^ 3 = x * i3F E := by
  rw [i3F_eq_inv E hℓ, div_eq_mul_inv]

/-- The Kafz substitution `ρ = r²/ℓ³` written with `i3F E`. -/
theorem rho_eq_mul_i3 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hℓ : 0 < E.ell) (r : ℝ) :
    r ^ 2 / E.ell ^ 3 = r ^ 2 * i3F E :=
  div_ell3_eq_mul_i3 E hℓ (r ^ 2)

/-- `Real.sqrt (ρ ℓ³) = r` at `ρ = r² i3F E` and `r ≥ 0`. -/
theorem sqrt_rho_ell3 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hℓ : 0 < E.ell) (r : ℝ) (hr : 0 ≤ r) :
    Real.sqrt (r ^ 2 * i3F E * E.ell ^ 3) = r := by
  rw [show r ^ 2 * i3F E * E.ell ^ 3 = r ^ 2 by
    rw [mul_assoc, i3F_mul_ell3 E hℓ, mul_one], Real.sqrt_sq hr]

/-- The repointed environment at `ρ = r²i3F E` has `.z = r`. -/
theorem KzEnvAt_z_i3 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hℓ : 0 < E.ell) (r : ℝ) (hr : 0 ≤ r) :
    (Work.BoseFixR.KzEnvAt E (r ^ 2 * i3F E)).z = r := by
  show Real.sqrt (r ^ 2 * i3F E * E.ell ^ 3) = r
  exact sqrt_rho_ell3 E hℓ r hr

/-- The repointed environment at `ρ = r²i3F E` has `.rho = r²i3F E`. -/
theorem KzEnvAt_rho_i3 {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (hℓ : 0 < E.ell) (r : ℝ) :
    (Work.BoseFixR.KzEnvAt E (r ^ 2 * i3F E)).rho = r ^ 2 * i3F E := by
  rw [Work.BoseB7.Q3Env.rho, Work.BoseB7.rhoZ]
  show (Real.sqrt (r ^ 2 * i3F E * E.ell ^ 3)) ^ 2 / E.ell ^ 3 = r ^ 2 * i3F E
  rw [show r ^ 2 * i3F E * E.ell ^ 3 = r ^ 2 by
      rw [mul_assoc, i3F_mul_ell3 E hℓ, mul_one],
    Real.sq_sqrt (by positivity), div_ell3_eq_mul_i3 E hℓ (r ^ 2)]

/-- The repointed environment does not change the `P_H` region. -/
theorem PHset_KzEnvAt {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] [DecidableEq Mode]
    (F : Work.BoseB7.FockData Mode) (E : Work.BoseB7.Q3Env Mode) (ρ : ℝ) :
    F.PHset (Work.BoseFixR.KzEnvAt E ρ) = F.PHset E := rfl

/-- The `c`-number row of `KzOpC` at `ρ = r²i3F E` is `cHCF r⁴ − μĝ(0) r²`. -/
theorem KzOpC_scalar_row {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (E : Work.BoseB7.Q3Env Mode) (gHat0 r : ℝ) (hℓ : 0 < E.ell) :
    E.ell ^ 3 * (-(1 / 2) * E.mu ^ 2 * gHat0 + (1 / 2) * (r ^ 2 * i3F E - E.mu) ^ 2 * gHat0
        + (1 / 2) * (r ^ 2 * i3F E) ^ 2 * E.W1omega0)
      = cHCF E gHat0 * r ^ 4 - E.mu * gHat0 * r ^ 2 := by
  rw [cHCF, i3F_eq_inv E hℓ]
  field_simp
  ring

end Work.BoseBoxFock
