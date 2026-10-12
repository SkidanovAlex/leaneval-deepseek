import Mathlib.Algebra.Order.Star.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7A.Statements
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Submission.Work.BoseB7A.errA_pre` — monomial normal form for the `N1` arithmetic

At a parameter point `FSParamsView E`, with `X = (μa³)^{1/323} = fsXp h.t 1`, every
scalar of `Q3Env` is a monomial in `X`, and every error bracket of §10 (`e1A`,
`e23A`, `e4A`, `controlErrA`) is a sum of monomials `X^c` (times `E.b`-powers and
the fixed constants `√2`, `ρ`-bounds).  This module records that normal form
(exponents read off from `FSParamsVals`), together with the two scalar bounds
that the domination `N1` uses (`√(𝓜/z²) ≤ √2·X^{337/8}` and `ρ_z² ≤ (9/4)μ²`).

The values (with `X = (μa³)^{1/323}`), as used by `e1A`, `e23A`, `e4A`:

| quantity | value |
|---|---|
| `E.Kl` | `X^{-3/2}` |
| `E.KL` | `X^{-21/2}` |
| `E.KH` | `X^{-549/4}` |
| `E.d` | `X⁶` |
| `E.lille` | `X^{97/2}` |
| `E.bigM` | `X^{-327/4}` |
| `dil E c` | `X^{323c}` |
| `E.μℓ³` | `X^{-166}` |
| `M̃ = Mt E` | `24` |
| `η` | `X^{1236}` |
| `E0 E` | `μ·X^{-166}` |
| `controlErrA` | `E0·X^{325/2}` |

The bracket bounds themselves (`e1A_le`, `e23A_le`, `e4A_le`, in decomposition
exponent form) are delegated to `Submission/Work/BoseB7A/errA_e1{,23,4}.lean`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7A

open Work.BoseB7
open Work.BoseBox

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-- `K_ℓ = X^{-3/2}`. -/
theorem errA_Kl (E : Q3Env Mode) (h : FSParamsView E) : E.Kl = fsXp h.t (-(3 / 2)) := Kl_val E h

/-- `K_L = X^{-21/2}`. -/
theorem errA_KL (E : Q3Env Mode) (h : FSParamsView E) : E.KL = fsXp h.t (-(21 / 2)) := KL_val E h

/-- `K_H = X^{-549/4}`. -/
theorem errA_KH (E : Q3Env Mode) (h : FSParamsView E) : E.KH = fsXp h.t (-(549 / 4)) := KH_val E h

/-- `d = X⁶`. -/
theorem errA_d (E : Q3Env Mode) (h : FSParamsView E) : E.d = fsXp h.t 6 := d_val E h

/-- `𝓁 = X^{97/2}`. -/
theorem errA_lille (E : Q3Env Mode) (h : FSParamsView E) : E.lille = fsXp h.t (97 / 2) := lille_val E h

/-- `𝓜 = X^{-327/4}`. -/
theorem errA_bigM (E : Q3Env Mode) (h : FSParamsView E) : E.bigM = fsXp h.t (-(327 / 4)) := bigM_val E h

/-- `s = X`. -/
theorem errA_s (E : Q3Env Mode) (h : FSParamsView E) : E.s = fsXp h.t 1 := h.s_eq

/-- `(μa³)^c = X^{323c}`. -/
theorem errA_dil (E : Q3Env Mode) (h : FSParamsView E) (c : ℝ) : dil E c = fsXp h.t (323 * c) :=
  dil_val E h c

/-- `μℓ³ = X^{-166}`. -/
theorem errA_mue (E : Q3Env Mode) (h : FSParamsView E) : E.mu * E.ell ^ 3 = fsXp h.t (-166) := mue_val E h

/-- FS's `M̃ = ⌊M/2⌋ = 24`. -/
theorem errA_Mt (E : Q3Env Mode) (h : FSParamsView E) : Mt E = 24 := by
  rw [Mt, h.intM_eq, mValue]
  norm_num

/-- `η = (K_ℓ^{-2}𝓁)^{M̃} = X^{1236}`. -/
theorem errA_eta (E : Q3Env Mode) (h : FSParamsView E) : eta E = fsXp h.t 1236 := by
  rw [eta, errA_Kl E h, errA_lille E h, errA_Mt E h]
  have h0 : 0 < h.t := h.t_pos
  rw [fsXp_rpow h0.le]
  have h1 : fsXp h.t (-(3 / 2) * -2) = fsXp h.t 3 := by norm_num
  rw [h1, fsXp_mul h0, fsXp_rpow h0.le]
  norm_num

/-- `η² = X^{2472}`. -/
theorem errA_eta_sq (E : Q3Env Mode) (h : FSParamsView E) : eta E ^ 2 = fsXp h.t 2472 := by
  rw [errA_eta E h, fsXp_pow h.t_pos.le]
  norm_num

/-- `E0 = μ²aℓ³ > 0`. -/
theorem errA_E0_pos (E : Q3Env Mode) (h : FSParamsView E) : 0 < E0 E := by
  rw [E0]
  have := h.t_pos
  have := mu_pos E h
  have := a_pos E h
  have := ell_pos E h
  positivity

/-- `E0 ≥ 0`. -/
theorem errA_E0_nonneg (E : Q3Env Mode) (h : FSParamsView E) : 0 ≤ E0 E := (errA_E0_pos E h).le

/-- `E0 = a·μ·(μℓ³) = a·μ·X^{-166}`. -/
theorem errA_E0_eq (E : Q3Env Mode) (h : FSParamsView E) : E0 E = E.aScat * E.mu * fsXp h.t (-166) := by
  rw [E0, ← errA_mue E h]
  ring

/-- The target bracket: `controlErrA = E0·X^{325/2}`. -/
theorem errA_controlErr (E : Q3Env Mode) (h : FSParamsView E) : controlErrA E = E0 E * fsXp h.t (325 / 2) := by
  rw [controlErrA, errA_dil E h]
  norm_num

/-- `ρ_z² a ℓ³ ≤ (9/4)E0` (FS `eq:Close`: `ρ_z ≤ (3/2)μ`). -/
theorem errA_rho_sq_le (E : Q3Env Mode) (h : FSParamsView E) : E.rho ^ 2 * E.aScat * E.ell ^ 3 ≤ (9 / 4) * E0 E := by
  have h1 : E.rho ^ 2 ≤ (9 / 4) * E.mu ^ 2 := by
    nlinarith [rho_le E h, rho_pos E h, mu_pos E h]
  have h2 : 0 < E.aScat * E.ell ^ 3 := mul_pos (a_pos E h) (pow_pos (ell_pos E h) 3)
  calc E.rho ^ 2 * E.aScat * E.ell ^ 3 = E.rho ^ 2 * (E.aScat * E.ell ^ 3) := by ring
    _ ≤ (9 / 4) * E.mu ^ 2 * (E.aScat * E.ell ^ 3) := mul_le_mul_of_nonneg_right h1 h2.le
    _ = (9 / 4) * E0 E := by rw [E0]; ring

/-- `√(𝓜/z²) ≤ √2·X^{337/8}`: `𝓜/z² = 𝓜/(ρ_zℓ³) ≤ 2𝓜/(μℓ³) = 2X^{337/4}` and `ρ_z ≥ μ/2`. -/
theorem errA_sqrt_le (E : Q3Env Mode) (h : FSParamsView E) : Real.sqrt (E.bigM / E.z ^ 2) ≤ Real.sqrt 2 * fsXp h.t (337 / 8) := by
  have h0 : 0 < h.t := h.t_pos
  have hz : E.z ^ 2 = E.rho * E.ell ^ 3 := zsq_eq E h
  have hbM : 0 ≤ E.bigM := bigM_nonneg E h
  have hr : E.mu / 2 ≤ E.rho := rho_ge E h
  have hmu : 0 < E.mu := mu_pos E h
  have hell : 0 < E.ell := ell_pos E h
  have hden : 0 < E.mu / 2 * E.ell ^ 3 := mul_pos (by linarith) (pow_pos hell 3)
  have hle1 : E.mu / 2 * E.ell ^ 3 ≤ E.rho * E.ell ^ 3 :=
    mul_le_mul_of_nonneg_right hr (pow_pos hell 3).le
  have hle : E.bigM / (E.rho * E.ell ^ 3) ≤ E.bigM / (E.mu / 2 * E.ell ^ 3) :=
    div_le_div_of_nonneg_left hbM hden hle1
  have h2 : E.bigM / (E.mu / 2 * E.ell ^ 3) = 2 * fsXp h.t (337 / 4) := by
    rw [← bigM_div_mue E h]
    field_simp
  have key : E.bigM / E.z ^ 2 ≤ 2 * fsXp h.t (337 / 4) := by
    rw [hz]; rw [h2] at hle; exact hle
  have hsq : fsXp h.t (337 / 4) = (fsXp h.t (337 / 8)) ^ 2 := by
    rw [fsXp_pow h0.le]; norm_num
  have hroot : Real.sqrt (fsXp h.t (337 / 4)) = fsXp h.t (337 / 8) := by
    rw [hsq, Real.sqrt_sq (fsXp_nonneg h0.le)]
  calc Real.sqrt (E.bigM / E.z ^ 2) ≤ Real.sqrt (2 * fsXp h.t (337 / 4)) :=
        Real.sqrt_le_sqrt key
    _ = Real.sqrt 2 * Real.sqrt (fsXp h.t (337 / 4)) := Real.sqrt_mul (by norm_num) _
    _ = Real.sqrt 2 * fsXp h.t (337 / 8) := by rw [hroot]

end Work.BoseB7A
