import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.BoseB7.Integral
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.ParamsView` — FS's parameter point, and the `ErrDominated` arithmetic

`thm:Control3Q` is the statement that the *sum of the three estimates* of
`lem:EstimatesOnQ3-js` dominates the `3Q` word, with a remainder of the shape
`C μ²aℓ³[√(𝓜/|z|²)(K_H^{-1}(μa³)^{5/12} + (K_ℓK_L)^{-M} + K_ℓ³K_L³(K_ℓ^{-2}𝓁)^{(M-1)/2})
+ 𝓁⁴a/ℓ + (μa³)^{1/2}K_ℓ^{-3}d^{-12}δ²(K_ℓ^{-2}δ)^{M-1}]` (FS `eq:Q3Cancels`).

The assembly itself (`Work.BoseB7.Control3Q_of_estimates`) is pure linear
algebra; what remains is the *arithmetic* comparison
`err1 + err23 + err4 ≤ controlErr`, i.e. `Work.BoseB7.ErrDominated`.  FS:
"We have used that the `K`'s are larger than `1` and `con:KBellKM` to simplify
the total remainder."

This module fixes the parameter point at which that comparison is a theorem:
`FSParamsView E` says that the scalars of the `Q3Env` `E` are FS's choices at the
diluteness `t = μa³` (eq. `eq:Xparameter`, `eq:Xchoice`), that the parameter block
satisfies `sec:params` (`Work.BoseBox.paramsOK_fsParams` instantiates it), that
`ρ_z` is close to `μ` (FS `eq:Close`, proved in §9) and that the §9 error
parameter `δ` is at least the Landau ratio `𝓁` (which is what makes the *last*
error bracket of `eq:EstimateQ3Tilde1` dominated by the last bracket of
`eq:Q3Cancels`: both inner factors are `(K_ℓ^{-2}·(something))^{M-1}` and
`(K_ℓ^{-2}𝓁)^{M-1} ≤ (K_ℓ^{-2}δ)^{M-1} ⟺ 𝓁 ≤ δ`).

## Contents

* `FSParamsView` — the parameter point.
* `ErrDominated_fsParams` — delegated: at that point `ErrDominated` holds.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

open Work.BoseBox

section

variable {Mode : Type*} [AddCommGroup Mode] [Fintype Mode]

/-- **FS's parameter point of §10.**  The `Q3Env`'s scalars are FS's choices at
the diluteness `t = μa³` (so that `X = (μa³)^{1/323}`, `K_ℓ = X^{-3/2}`,
`K_B = X^{-6}`, `K_M = X^{-1}`, `K̃_H = X^{-8/3}`, `s = X`, `d = X⁶`,
`ε_T = X^{23/4}`, `M = 48`), the box side is the healing length
`ℓ = K_ℓ(μa)^{-1/2}`, the window is `𝓜 = K_M(μa³)^{-1/4}`, `ρ_z` satisfies FS
`eq:Close` in the crudest form `|ρ_z - μ| ≤ μ/2`, and `δ` is FS's §9 error
parameter, which is at most `1` and at least the Landau ratio `𝓁`.

The structure is `Type`-valued (it carries the *data* `t`), so it is used as a
hypothesis `(h : FSParamsView E)` — never as a `Prop` in an `∃`-statement. -/
structure FSParamsView (E : Q3Env Mode) where
  /-- The diluteness `t = μa³`. -/
  t : ℝ
  /-- `0 < t`: the physical range. -/
  t_pos : 0 < t
  /-- `t ≤ 1`: dilute. -/
  t_le_one : t ≤ 1
  /-- `t = μa³`. -/
  mu_eq : E.mu * E.aScat ^ 3 = t
  /-- `a > 0`. -/
  a_pos : 0 < E.aScat
  /-- `X = (μa³)^{1/323}` and FS `eq:Xparameter`. -/
  Kl_eq : E.Kl = fsXp t (-(3 / 2 : ℝ))
  /-- FS's `K̃_H = X^{-8/3}`, rescaled: `E.KH` is the full `K_H = K̃_H(μa³)^{-5/12}`. -/
  KH_eq : E.KH = KH (fsXp t (-(8 / 3 : ℝ))) E.mu E.aScat
  /-- `d = X⁶`. -/
  d_eq : E.d = fsXp t 6
  /-- `s = X`. -/
  s_eq : E.s = fsXp t 1
  /-- `ε_T = X^{23/4}`. -/
  eT_eq : E.eT = fsXp t (23 / 4 : ℝ)
  /-- FS `eq:KL_d`: `K_L = (K_ℓd²)^{-1}`. -/
  KL_eq : E.KL = KL E.Kl E.d
  /-- FS `eq:def_ell`: `ℓ = K_ℓ(μa)^{-1/2}`. -/
  ell_eq : E.ell = side E.Kl E.mu E.aScat
  /-- FS `eq:DefM`: `𝓜 = K_M(μa³)^{-1/4}`. -/
  bigM_eq : E.bigM = fsXp t (-(1 : ℝ)) * t ^ (-(1 / 4 : ℝ))
  /-- FS's regularity integer `M = 48` (`Basic.mValue`). -/
  intM_eq : E.intM = mValue
  /-- The parameter block satisfies every condition of FS `sec:params`. -/
  paramsOK : ParamsOK (fsParams t) t
  /-- `z ≠ 0` (the `c`-number of `thm:Kafz`). -/
  z_ne : E.z ≠ 0
  /-- FS `eq:Close`, in the crudest form: `|ρ_z - μ| ≤ μ/2`.  (FS have
  `|ρ_z - μ| ≤ CμK_ℓ^{-2}` with all the §9 parameters; `ρ_z² ≤ 4μ²` is the only
  consequence used here.) -/
  rho_close : |E.rho - E.mu| ≤ E.mu / 2
  /-- The `K`'s are larger than `1` (FS's remark in the proof of
  `thm:Control3Q`). -/
  one_le_Kl : 1 ≤ E.Kl
  /-- The `K`'s are larger than `1`. -/
  one_le_KL : 1 ≤ E.KL
  /-- The `K`'s are larger than `1`. -/
  one_le_KH : 1 ≤ E.KH
  /-- The `K`'s are larger than `1`. -/
  one_le_bigM : 1 ≤ E.bigM
  /-- The §9 error parameter `δ` is at least the Landau ratio `𝓁` (see the
  module docstring: this is exactly what makes the last error bracket of
  `eq:EstimateQ3Tilde1` dominated by the last bracket of `eq:Q3Cancels`). -/
  lille_le_delta : E.lille ≤ E.delta
  /-- `δ ≤ 1`. -/
  delta_le_one : E.delta ≤ 1

end

/-! ## The arithmetic theorem (delegated)

`Work.BoseB7.ErrDominated_fsParams` is delegated to
`Submission/Work/BoseB7/ErrDominated_fsParams.lean`, so that this module (and the
whole chapter) stays `sorry`-free.  The constant `C` of `eq:Q3Cancels` is
*pinned* as a function of the three estimate constants (`C = 4(C1+C23+C4)+1`):
with `C` existentially quantified the claim would be vacuous (`C1=C23=C4=C=0`
always works), so the arithmetic content is exactly the bracket-wise domination

  `br1 + br23 + br4 ≤ 4·brC`  (where `err_i E C = C·br_i`),

which is what FS mean by "simplify the total remainder", and which uses the
`K`'s `≥ 1`, `ρ_z² ≤ 4μ²` and `𝓁 ≤ δ`.

-/

end Work.BoseB7
