import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7.FSEnvDefs
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.fsEnv_rho_val` — the substituted density of the concrete environment

`Work.BoseB7.fsEnv t` (`Submission/Work/BoseB7/FSEnvDefs.lean`) is FS's parameter
point at `μ = t`, `a = 1`, with the `c`-number `z := √(μℓ³) = √(t·ℓ³)` and box
side `ℓ = K_ℓ(μa)^{-1/2} = X^{-3/2}·t^{-1/2} > 0`.  Since `ρ_z = z²/ℓ³`
(`Q3Env.rho`, FS `thm:Kafz`), this is *exactly* the value for which FS `eq:Close`
holds with no error at all:

  `rho = z²/ℓ³ = t·ℓ³/ℓ³ = t`.

This is the arithmetic input of `Work.BoseB7.FSParamsView_inhabited`, where
`rho_close` becomes `|t - t| ≤ t/2`.

The proof is the trivial one: `ℓ > 0` (both factors of `fsKlVal t · t^{-1/2}`
are positive), hence `t·ℓ³ ≥ 0` and `Real.sq_sqrt` applies; the rest is the
cancellation `t·ℓ³/ℓ³ = t` with `ℓ³ ≠ 0`.
-/

namespace Work.BoseB7

open Work.BoseBox

/-- The box side `ℓ = K_ℓ(μa)^{-1/2}` of §10's parameter point is positive. -/
private lemma fsEllVal_pos_aux {t : ℝ} (h0 : 0 < t) : 0 < fsEllVal t := by
  rw [fsEllVal, side, fsKlVal]
  exact mul_pos (fsXp_pos h0) (Real.rpow_pos_of_pos (by simpa using h0) _)

theorem fsEnv_rho_val {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] {t : ℝ} (h0 : 0 < t) :
    (Work.BoseB7.fsEnv (Mode := Mode) t).rho = t := by
  have hℓpos : 0 < fsEllVal t := fsEllVal_pos_aux h0
  rw [Q3Env.rho, rhoZ]
  show (fsZVal t) ^ 2 / (fsEllVal t) ^ 3 = t
  have harg : 0 ≤ t * (fsEllVal t) ^ 3 := by positivity
  rw [fsZVal, Real.sq_sqrt harg]
  field_simp

end Work.BoseB7
