import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7.fsEnv_lille_val
import Submission.Work.BoseB7.fsEnv_rho_val
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.fsEnv_closed` — the scalars of `fsEnv` in `fsXp` normal form

`Work.BoseB7.fsEnv t` (`Submission/Work/BoseB7/FSEnvDefs.lean`) is the concrete
`Q3Env` at FS's parameter point `μ = t`, `a = 1`.  Every scalar it carries is a
monomial in `t`, hence a bare power `X^c` of `X = (μa³)^{1/323}` in the `fsXp`
normal form of `Work.BoseBox.Basic` (`fsXp t c = t^{c/323}`).  This module
records those six closed forms, which is what makes `FSParamsView (fsEnv t)`
(`Submission/Work/BoseB7/FSParamsView_inhabited.lean`) a finite exponent
computation:

| scalar | value |
|---|---|
| `ℓ = fsEnv.ell = side K_ℓ t 1` | `X^{-163}` |
| `K_H = fsEnv.KH` | `X^{-549/4}` |
| `K_L = fsEnv.KL = (K_ℓd²)^{-1}` | `X^{-21/2}` |
| `𝓜 = fsEnv.bigM` | `X^{-327/4}` |
| `𝓁 = fsEnv.lille = (μa³)K_H²` | `X^{97/2}` |
| `ρ_z = fsEnv.rho = z²/ℓ³` | `t` |

The last two rows (the derived scalars `lille` and `rho`) are delegated
(`Submission/Work/BoseB7/fsEnv_lille_val.lean`,
`Submission/Work/BoseB7/fsEnv_rho_val.lean`); the four direct monomials
(`ell`, `KH`, `KL`, `bigM`) are exponent arithmetic proved here, in the
`fsXp`-calculus of `Work.BoseBox.Basic`
(`fsXp_mul`, `fsXp_pow`, `fsXp_inv`, `fsXp_rpow`, `delta_eq_fsXp`).
-/

namespace Work.BoseB7

open Work.BoseBox

/-! ## 1. The four direct monomials

Each is `X^{...}` with exponent obtained by adding the exponents of its factors
(`t^c = X^{323c}` for the bare `t`-powers). -/

/-- The box side `ℓ = K_ℓ(μa)^{-1/2} = X^{-3/2}·X^{-323/2} = X^{-163}`. -/
theorem fsEllVal_eq {t : ℝ} (h0 : 0 < t) : fsEllVal t = fsXp t (-163) := by
  rw [fsEllVal, side, fsKlVal, mul_one, rpow_eq_fsXp h0.le, fsXp_mul h0]
  norm_num

/-- `K_H = K̃_H(μa³)^{-5/12} = X^{-8/3}·X^{-1615/12} = X^{-549/4}`. -/
theorem fsKHVal_eq {t : ℝ} (h0 : 0 < t) : fsKHVal t = fsXp t (-(549 / 4)) := by
  rw [fsKHVal, KH, one_pow, mul_one, rpow_eq_fsXp h0.le, fsXp_mul h0]
  norm_num

/-- `K_L = (K_ℓd²)^{-1} = (X^{-3/2}X^{12})^{-1} = X^{-21/2}`. -/
theorem fsKLVal_eq {t : ℝ} (h0 : 0 < t) : fsKLVal t = fsXp t (-(21 / 2)) := by
  rw [fsKLVal, KL, Real.rpow_neg_one, fsKlVal, fsDVal, fsXp_pow h0.le, fsXp_mul h0, fsXp_inv h0]
  norm_num

/-- `𝓜 = K_M(μa³)^{-1/4} = X^{-1}·X^{-323/4} = X^{-327/4}`. -/
theorem fsBigMVal_eq {t : ℝ} (h0 : 0 < t) : fsBigMVal t = fsXp t (-(327 / 4)) := by
  rw [fsBigMVal, rpow_eq_fsXp h0.le, fsXp_mul h0]
  norm_num

/-! ## 2. The field projections of `fsEnv` used below -/

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

@[simp] lemma fsEnv_KH_field (t : ℝ) : (fsEnv (Mode := Mode) t).KH = fsKHVal t := rfl

@[simp] lemma fsEnv_KL_field (t : ℝ) : (fsEnv (Mode := Mode) t).KL = fsKLVal t := rfl

/-! ## 3. The six closed forms -/

theorem fsEnv_closed {Mode : Type*} [AddCommGroup Mode] [Fintype Mode] {t : ℝ} (h0 : 0 < t) :
    (Work.BoseB7.fsEnv (Mode := Mode) t).ell = Work.BoseBox.fsXp t (-163) ∧
      (Work.BoseB7.fsEnv (Mode := Mode) t).KH = Work.BoseBox.fsXp t (-(549 / 4)) ∧
      (Work.BoseB7.fsEnv (Mode := Mode) t).KL = Work.BoseBox.fsXp t (-(21 / 2)) ∧
      (Work.BoseB7.fsEnv (Mode := Mode) t).bigM = Work.BoseBox.fsXp t (-(327 / 4)) ∧
      (Work.BoseB7.fsEnv (Mode := Mode) t).lille = Work.BoseBox.fsXp t (97 / 2) ∧
      (Work.BoseB7.fsEnv (Mode := Mode) t).rho = t := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [fsEnv_ell]
    exact fsEllVal_eq h0
  · rw [fsEnv_KH_field]
    exact fsKHVal_eq h0
  · rw [fsEnv_KL_field]
    exact fsKLVal_eq h0
  · rw [fsEnv_bigM]
    exact fsBigMVal_eq h0
  · exact fsEnv_lille_val h0
  · exact fsEnv_rho_val h0

end Work.BoseB7
