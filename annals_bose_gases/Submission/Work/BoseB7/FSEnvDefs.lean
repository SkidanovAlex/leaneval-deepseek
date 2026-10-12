import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7.FSParamsVals
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.FSEnvDefs` — a concrete `Q3Env` at FS's parameter point

`FSParamsView E` (`Work.BoseB7.ParamsView`) is a *hypothesis* bundle: it says
that the scalars of the `Q3Env` `E` are Fournais–Solovej's choices at the
diluteness `t = μa³ ∈ (0,1]` (`sec:params`, `eq:Xparameter`, `eq:Xchoice`),
that `ℓ` is the healing length, that `ρ_z` satisfies `eq:Close`, that the `K`'s
are `≥ 1` and that `𝓁 ≤ δ ≤ 1`.

This module *exhibits* such an `E`, so that `FSParamsView` is not vacuous:

* `μ := t`, `a := 1` (so `μa³ = t`),
* `K_ℓ := X^{-3/2} = fsXp t (-3/2)`, `d := X⁶`, `s := X`, `ε_T := X^{23/4}`,
* `K_H := KH (fsXp t (-8/3)) t 1 = K̃_H(μa³)^{-5/12}` (FS's **full** `K_H`),
* `K_L := KL K_ℓ d = (K_ℓd²)^{-1}`, `ℓ := side K_ℓ μ a = K_ℓ(μa)^{-1/2}`,
* `𝓜 := K_M(μa³)^{-1/4} = fsXp t (-1)·t^{-1/4}`, `M := mValue = 48`,
* `δ := 1` (so `𝓁 ≤ δ ≤ 1`; `𝓁 = X^{97/2} ≤ 1` for `t ≤ 1`),
* `z := √(μℓ³)` — this is the `c`-number for which `eq:Close` holds *exactly*,
  `ρ_z = z²/ℓ³ = μ`,
* the kernels are chosen harmless (`Ŵ₁ ≡ 0`, `τ ≡ 1`, `𝒜 ≡ 1`, `ℬ ≡ 0`, so
  `α ≡ 0` and `𝒟 ≡ 1`).

Every scalar of this `E` is a monomial `fsXp t c = t^{c/323}`, so every side
condition of `FSParamsView` is exponent arithmetic; the closed forms are
recorded in the companion lemmas of `Submission/Work/BoseB7/fsEnv_closed.lean`
(delegated) and the `ParamsOK` input in
`Submission/Work/BoseB7/ParamsOK_le_one.lean` (delegated).

## Contents

* `fsKlVal, fsDVal, fsSVal, fsETVal, fsKHVal, fsKLVal, fsEllVal, fsBigMVal,
  fsZVal` — FS's scalars at `μ = t`, `a = 1`.
* `fsEnv` — the concrete `Q3Env`.
* `fsEnv_mu`, `fsEnv_aScat`, ... — the fields of `fsEnv` (all `rfl`).
* `fsEllVal_pos`, `fsEllVal_ne_zero` — positivity of the box side.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

open Work.BoseBox

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-! ## 1. FS's scalars at `μ = t`, `a = 1` -/

/-- FS's `K_ℓ = X^{-3/2}` (`sec:params`). -/
noncomputable def fsKlVal (t : ℝ) : ℝ := fsXp t (-(3 / 2 : ℝ))

/-- FS's `d = X⁶`. -/
noncomputable def fsDVal (t : ℝ) : ℝ := fsXp t 6

/-- FS's `s = X`. -/
noncomputable def fsSVal (t : ℝ) : ℝ := fsXp t 1

/-- FS's `ε_T = X^{23/4}`. -/
noncomputable def fsETVal (t : ℝ) : ℝ := fsXp t (23 / 4)

/-- FS's **full** `K_H = K̃_H(μa³)^{-5/12}` at `K̃_H = X^{-8/3}`, `μ = t`, `a = 1`. -/
noncomputable def fsKHVal (t : ℝ) : ℝ := KH (fsXp t (-(8 / 3 : ℝ))) t 1

/-- FS's `K_L = (K_ℓd²)^{-1}` (`eq:KL_d`). -/
noncomputable def fsKLVal (t : ℝ) : ℝ := KL (fsKlVal t) (fsDVal t)

/-- FS's box side `ℓ = K_ℓ(μa)^{-1/2}` (`eq:def_ell`) at `μ = t`, `a = 1`. -/
noncomputable def fsEllVal (t : ℝ) : ℝ := side (fsKlVal t) t 1

/-- FS's `𝓜 = K_M(μa³)^{-1/4}` (`eq:DefM`), i.e. `fsXp t (-1)·t^{-1/4}`. -/
noncomputable def fsBigMVal (t : ℝ) : ℝ := fsXp t (-(1 : ℝ)) * t ^ (-(1 / 4 : ℝ))

/-- The `c`-number `z := √(μℓ³)`, for which FS `eq:Close` holds exactly
(`ρ_z = z²/ℓ³ = μ`). -/
noncomputable def fsZVal (t : ℝ) : ℝ := Real.sqrt (t * (fsEllVal t) ^ 3)

/-! ## 2. The concrete environment -/

/-- **The concrete `Q3Env` at the diluteness `t`.**  Its scalars are FS's choices
at `μ = t`, `a = 1` (see the module docstring); its kernels are the harmless
`Ŵ₁ ≡ 0`, `τ ≡ 1`, `𝒜 ≡ 1`, `ℬ ≡ 0`, `χ̂ ≡ 1`, `χ̂² ≡ 0`, `f_L ≡ 0`. -/
noncomputable def fsEnv (t : ℝ) : Q3Env Mode where
  z := fsZVal t
  ell := fsEllVal t
  mu := t
  aScat := 1
  KH := fsKHVal t
  Kl := fsKlVal t
  KL := fsKLVal t
  d := fsDVal t
  s := fsSVal t
  eT := fsETVal t
  b := bValue
  intM := mValue
  bigM := fsBigMVal t
  delta := 1
  fL := fun _ => 0
  W1 := fun _ => 0
  W1omega := fun _ => 0
  W1omega0 := 0
  hatChi := fun _ => 1
  hatChiSq := fun _ => 0
  tau := fun _ => 1
  A := fun _ => 1
  B := fun _ => 0

/-! ## 3. The fields of `fsEnv` (all definitional) -/

@[simp] lemma fsEnv_mu (t : ℝ) : (fsEnv (Mode := Mode) t).mu = t := rfl

@[simp] lemma fsEnv_aScat (t : ℝ) : (fsEnv (Mode := Mode) t).aScat = 1 := rfl

@[simp] lemma fsEnv_Kl (t : ℝ) : (fsEnv (Mode := Mode) t).Kl = fsKlVal t := rfl

@[simp] lemma fsEnv_d (t : ℝ) : (fsEnv (Mode := Mode) t).d = fsDVal t := rfl

@[simp] lemma fsEnv_s (t : ℝ) : (fsEnv (Mode := Mode) t).s = fsSVal t := rfl

@[simp] lemma fsEnv_eT (t : ℝ) : (fsEnv (Mode := Mode) t).eT = fsETVal t := rfl

@[simp] lemma fsEnv_intM (t : ℝ) : (fsEnv (Mode := Mode) t).intM = mValue := rfl

@[simp] lemma fsEnv_ell (t : ℝ) : (fsEnv (Mode := Mode) t).ell = fsEllVal t := rfl

@[simp] lemma fsEnv_bigM (t : ℝ) : (fsEnv (Mode := Mode) t).bigM = fsBigMVal t := rfl

@[simp] lemma fsEnv_delta (t : ℝ) : (fsEnv (Mode := Mode) t).delta = 1 := rfl

@[simp] lemma fsEnv_KH (t : ℝ) : (fsEnv (Mode := Mode) t).KH = fsKHVal t := rfl

@[simp] lemma fsEnv_KL (t : ℝ) : (fsEnv (Mode := Mode) t).KL = fsKLVal t := rfl

@[simp] lemma fsEnv_z (t : ℝ) : (fsEnv (Mode := Mode) t).z = fsZVal t := rfl

/-! ## 4. Positivity of the box side -/

/-- `f_L ≡ 0` for the concrete environment. -/
@[simp] lemma fsEnv_fL (t : ℝ) (k : Mode) : (fsEnv (Mode := Mode) t).fL k = 0 := rfl

/-- The concrete environment has `𝒜 ≡ 1`. -/
@[simp] lemma fsEnv_A (t : ℝ) (k : Mode) : (fsEnv (Mode := Mode) t).A k = 1 := rfl

/-- The concrete environment has `ℬ ≡ 0`. -/
@[simp] lemma fsEnv_B (t : ℝ) (k : Mode) : (fsEnv (Mode := Mode) t).B k = 0 := rfl

/-- `X^{-3/2} > 0`. -/
lemma fsKlVal_pos {t : ℝ} (h0 : 0 < t) : 0 < fsKlVal t := fsXp_pos h0

end Work.BoseB7
