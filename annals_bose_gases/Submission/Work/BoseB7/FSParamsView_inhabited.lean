import Mathlib.Algebra.Ring.IsFormallyReal
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7.FSEnvDefs
import Submission.Work.BoseB7.paramsOK_fsParams_le_one
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.FSParamsView_inhabited` — the parameter point `FSParamsView` is inhabited

`FSParamsView E` (`Submission/Work/BoseB7/ParamsView.lean`) is the hypothesis
bundle under which the whole node-`B7` chapter is stated: FS §10's parameter
point at a diluteness `t = μa³ ∈ (0,1]`.  This module proves that the bundle is
inhabited for **every** diluteness `t ∈ (0,1]`:

  `∃ E : Q3Env Mode, Nonempty (FSParamsView E)`.

The witness is the explicit environment `Work.BoseB7.fsEnv t`
(`Submission/Work/BoseB7/FSEnvDefs.lean`), in which `μ = t`, `a = 1` and every
scalar is FS's own power of `X = (μa³)^{1/323}`:

| `E` | value |
|---|---|
| `Kl` | `X^{-3/2}` |
| `KH` | `X^{-549/4}` |
| `KL` | `X^{-21/2}` |
| `d` | `X⁶`, `s = X`, `ε_T = X^{23/4}`, `M = 48` |
| `ell` | `X^{-163}` |
| `𝓜` | `X^{-327/4}` |
| `z` | `√(μℓ³)` |
| `δ` | `1` |

so that `𝓁 = (μa³)K_H² = X^{97/2} ≤ 1 = δ` (the `K`'s are `≥ 1` exactly when
their exponents are `≤ 0`, and `𝓁 ≤ 1` exactly when its exponent `97/2` is
`≥ 0`), `ρ_z = z²/ℓ³ = μ` (FS `eq:Close` holds *with equality*), and the box
side is the healing length.

## Contents

* `fsEllVal_val`, `fsKHVal_val`, `fsKLVal_val`, `fsBigMVal_val`, `fsEnv_lille_val`,
  `fsEnv_rho_val` — the closed forms of the witness's scalars (all pure exponent
  arithmetic, `t^c = fsXp t (323c)`).
* `FSParamsView_fsEnv` — the `FSParamsView` structure at `fsEnv t`, assembled
  from those closed forms and FS's `sec:params` conditions (`ParamsOK (fsParams t) t`,
  delegated to `Submission/Work/BoseB7/paramsOK_fsParams_le_one.lean`).
* `FSParamsView_inhabited` — the target.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

open Work.BoseBox

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-- `1 ≤ fsXp t c` for `c ≤ 0` and `0 < t ≤ 1`: `fsXp` is antitone in the
exponent and `fsXp t 0 = 1`. -/
lemma one_le_fsXp_of_nonpos {t c : ℝ} (h0 : 0 < t) (h1 : t ≤ 1) (hc : c ≤ 0) :
    1 ≤ fsXp t c := by
  have h := fsXp_le_fsXp (t := t) (a := 0) (b := c) h0 h1 hc
  have h0' : fsXp t (0 : ℝ) = 1 := by norm_num [fsXp]
  rwa [h0'] at h

/-! ## 1. The closed forms of the witness's scalars

Every scalar of `fsEnv t` is a monomial `fsXp t c = t^{c/323}`; the arithmetic is
`t^c = X^{323c}` (`rpow_eq_fsXp`) and `X^a·X^b = X^{a+b}` (`fsXp_mul`). -/

/-- The box side: `ℓ = K_ℓ(μa)^{-1/2} = X^{-3/2}·X^{-323/2} = X^{-163}`. -/
private lemma fsEllVal_val {t : ℝ} (h0 : 0 < t) : fsEllVal t = fsXp t (-163) := by
  rw [fsEllVal, side, fsKlVal, mul_one, rpow_eq_fsXp h0.le, fsXp_mul h0]
  congr 1
  norm_num

/-- FS's full `K_H`: `X^{-8/3}(μa³)^{-5/12} = X^{-8/3}X^{-323·5/12} = X^{-549/4}`. -/
private lemma fsKHVal_val {t : ℝ} (h0 : 0 < t) : fsKHVal t = fsXp t (-(549 / 4)) := by
  rw [fsKHVal, KH, one_pow, mul_one, rpow_eq_fsXp h0.le, fsXp_mul h0]
  congr 1
  norm_num

/-- The low-momentum cutoff: `K_L = (K_ℓd²)^{-1} = (X^{21/2})^{-1} = X^{-21/2}`. -/
private lemma fsKLVal_val {t : ℝ} (h0 : 0 < t) : fsKLVal t = fsXp t (-(21 / 2)) := by
  rw [fsKLVal, KL, fsKlVal, fsDVal, ← Real.rpow_natCast, fsXp_rpow h0.le, fsXp_mul h0,
    fsXp_rpow h0.le]
  congr 1
  norm_num

/-- The window: `𝓜 = X^{-1}(μa³)^{-1/4} = X^{-1}X^{-323/4} = X^{-327/4}`. -/
private lemma fsBigMVal_val {t : ℝ} (h0 : 0 < t) : fsBigMVal t = fsXp t (-(327 / 4)) := by
  rw [fsBigMVal, rpow_eq_fsXp h0.le, fsXp_mul h0]
  congr 1
  norm_num

/-- `𝓁 = (μa³)K_H² = X^{323}X^{-549/2} = X^{97/2}` (FS `eq:DefLille`). -/
private lemma fsEnv_lille_val {t : ℝ} (h0 : 0 < t) :
    (fsEnv (Mode := Mode) t).lille = fsXp t (97 / 2) := by
  have hKH : fsKHVal t = fsXp t (-(549 / 4)) := fsKHVal_val h0
  have h2 : (fsXp t (-(549 / 4))) ^ 2 = fsXp t (-(549 / 2)) := by
    rw [← Real.rpow_natCast, fsXp_rpow h0.le]
    congr 1
    norm_num
  have ht : t = fsXp t 323 := delta_eq_fsXp h0.le
  rw [Q3Env.lille, lille]
  change (t * 1 ^ 3) * (fsKHVal t) ^ 2 = fsXp t (97 / 2)
  rw [one_pow, mul_one, hKH, h2]
  nth_rewrite 1 [ht]
  rw [fsXp_mul h0]
  congr 1
  norm_num

/-- `ρ_z = z²/ℓ³ = μ` for the `c`-number `z = √(μℓ³)` (FS `eq:Close` with
equality). -/
private lemma fsEnv_rho_val {t : ℝ} (h0 : 0 < t) :
    (fsEnv (Mode := Mode) t).rho = t := by
  have hell : fsEllVal t = fsXp t (-163) := fsEllVal_val h0
  have hellpos : 0 < fsEllVal t := by rw [hell]; exact fsXp_pos h0
  have hz : fsZVal t ^ 2 = t * fsEllVal t ^ 3 :=
    Real.sq_sqrt (le_of_lt (mul_pos h0 (pow_pos hellpos 3)))
  rw [Q3Env.rho, rhoZ]
  change (fsZVal t) ^ 2 / (fsEllVal t) ^ 3 = t
  rw [hz, mul_div_assoc, div_self (pow_ne_zero 3 (ne_of_gt hellpos)), mul_one]

/-- **The `FSParamsView` structure at the concrete environment `fsEnv t`.**  The
five `one_le_*`/`𝓁 ≤ δ ≤ 1` fields and `eq:Close` are read off the closed forms
of the scalars (`fsEllVal_val`, `fsKHVal_val`, ...); `μa³ = t`,
`ℓ = side K_ℓ μ a`, `K_L = (K_ℓd²)^{-1}`, `K_H = K̃_H(μa³)^{-5/12}` and the
remaining equations are the definitions. -/
noncomputable def FSParamsView_fsEnv {t : ℝ} (h0 : 0 < t) (h1 : t ≤ 1)
    (hOK : ParamsOK (fsParams t) t) :
    FSParamsView (fsEnv (Mode := Mode) t) where
  t := t
  t_pos := h0
  t_le_one := h1
  mu_eq := by simp [fsEnv]
  a_pos := by simp [fsEnv]
  Kl_eq := rfl
  KH_eq := rfl
  d_eq := rfl
  s_eq := rfl
  eT_eq := rfl
  KL_eq := rfl
  ell_eq := rfl
  bigM_eq := rfl
  intM_eq := rfl
  paramsOK := hOK
  z_ne := by
    have hellpos : 0 < fsEllVal t := by
      rw [fsEllVal_val h0]; exact fsXp_pos (c := -163) h0
    have hz : 0 < (fsEnv (Mode := Mode) t).z :=
      Real.sqrt_pos.mpr (mul_pos h0 (pow_pos hellpos 3))
    exact ne_of_gt hz
  rho_close := by
    rw [fsEnv_rho_val h0, fsEnv_mu, sub_self, abs_zero]
    linarith
  one_le_Kl := by
    rw [fsEnv_Kl]
    exact one_le_fsXp_of_nonpos h0 h1 (by norm_num)
  one_le_KL := by
    rw [fsEnv_KL, fsKLVal_val h0]
    exact one_le_fsXp_of_nonpos h0 h1 (by norm_num)
  one_le_KH := by
    rw [fsEnv_KH, fsKHVal_val h0]
    exact one_le_fsXp_of_nonpos h0 h1 (by norm_num)
  one_le_bigM := by
    rw [fsEnv_bigM, fsBigMVal_val h0]
    exact one_le_fsXp_of_nonpos h0 h1 (by norm_num)
  lille_le_delta := by
    rw [fsEnv_lille_val h0, fsEnv_delta]
    exact fsXp_le_one h0 h1 (by norm_num)
  delta_le_one := by
    rw [fsEnv_delta]

theorem FSParamsView_inhabited {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]
    (t : ℝ) (h0 : 0 < t) (h1 : t ≤ 1) :
    ∃ E : Work.BoseB7.Q3Env Mode, Nonempty (Work.BoseB7.FSParamsView E) :=
  ⟨fsEnv t, ⟨FSParamsView_fsEnv h0 h1 (paramsOK_fsParams_le_one h0 h1)⟩⟩

end Work.BoseB7
