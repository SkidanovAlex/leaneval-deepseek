import Mathlib.Analysis.InnerProductSpace.PiL2
import Submission.Work.BoseBox.Basic
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `Work.BoseB7.Params` — FS §10's parameters at the diluteness scale

FS §10 works at the parameters of `sec:params` (`X = (μa³)^{1/323}`, `s = X`,
`d = X⁶`, `ε_T = X^{23/4}`, `K_ℓ = X^{-3/2}`, `K_B = X^{-6}`,
`K_M = X^{-1}`, `K_H = X^{-8/3}`), with the box side `ℓ = K_ℓ(μa)^{-1/2}`, the
`c`-number `z ∈ ℝ` and the substituted density `ρ_z = z²/ℓ³` (`thm:Kafz`).

This module fixes the *dictionary*, importing the parameter block of
`Work.BoseBox.Basic` (the `B8` bookkeeping module of the box chapter) so that
the two chapters share one parameter vocabulary; the conditions `con:*` of
`sec:params` are those of that module (`Work.BoseBox.ParamsOK`, instantiated by
`Work.BoseBox.paramsOK_fsParams`).

## Contents

* `side`, `rhoZ`, `lille`, `KL`, `KH` — FS's `ℓ`, `ρ_z`, `𝓁`, `K_L`, `K_H`.
* `tau` — FS `def:tau`, the localised kinetic symbol.
* `nPlusHRegion` — the high-momentum region of `n₊^H`.
-/

noncomputable section

open scoped BigOperators

namespace Work.BoseB7

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- FS `eq:def_ell`: the healing-length box side `ℓ = K_ℓ(μa)^{-1/2}`. -/
noncomputable def side (Kl μ a : ℝ) : ℝ := Kl * (μ * a) ^ (-(1 / 2 : ℝ))

/-- FS `thm:Kafz`: the substituted condensate density `ρ_z = z²/ℓ³`. -/
noncomputable def rhoZ (z ell : ℝ) : ℝ := z ^ 2 / ell ^ 3

/-- FS `eq:DefLille` in the form used throughout §10,
`𝓁 = (μa³)K_H²`, where `KH` is FS's **full** `K_H = K̃_H(μa³)^{-5/12}` (the
parameter whose inverse is the `P_H` cutoff `eq:KHtilde-cutoff`).  Equivalently
`𝓁 = (μa³)^{1/6}K̃_H²` (FS's own display); see `lille_eq_lilleTilde`. -/
noncomputable def lille (μ a KH : ℝ) : ℝ := (μ * a ^ 3) * KH ^ 2

/-- FS `eq:DefLille` in the form FS display it: `𝓁 = (μa³)^{1/6}K̃_H²`, from the
*tilde* parameter `K̃_H` (the field `KH` of `Work.BoseBox.FSParams`). -/
noncomputable def lilleTilde (μ a KHt : ℝ) : ℝ := (μ * a ^ 3) ^ (1 / 6 : ℝ) * KHt ^ 2

/-- The region of `n₊^H` (FS §7): the modes with `|k| ≥ (d²ℓ)⁻¹`. -/
def nPlusHRegion (ell d : ℝ) (k : ℝ³) : Prop := 1 / (d ^ 2 * ell) ≤ ‖k‖

/-! ## The two forms of `𝓁` agree -/

/-- FS `eq:KL_d`: `K_L = (K_ℓd²)^{-1}` (FS's choice of the low-momentum cutoff;
it is not an independent parameter). -/
noncomputable def KL (Kl d : ℝ) : ℝ := (Kl * d ^ 2) ^ (-(1 : ℝ))

/-- FS's `K_H = K̃_H(μa³)^{-5/12}` (`sec:params`), whose inverse `K_H^{-1}a^{-1}`
is the `P_H` cutoff `eq:KHtilde-cutoff`.  (The parameter block
`Work.BoseBox.FSParams` records `K̃_H` as its field `KH`.) -/
noncomputable def KH (KHt μ a : ℝ) : ℝ := KHt * (μ * a ^ 3) ^ (-(5 / 12 : ℝ))

/-- The two forms of `𝓁` agree (`μa³ > 0`): `(μa³)K_H² = (μa³)^{1/6}K̃_H²`
with `K_H = K̃_H(μa³)^{-5/12}`. -/
theorem lille_eq_lilleTilde {μ a KHt : ℝ} (ht : 0 < μ * a ^ 3) :
    lille μ a (KH KHt μ a) = lilleTilde μ a KHt := by
  set T := μ * a ^ 3 with hT
  have hTpos : 0 < T := ht
  have h1 : (T ^ (-(5 / 12 : ℝ))) ^ 2 = T ^ (-(5 / 6 : ℝ)) := by
    rw [sq, ← Real.rpow_add hTpos]; norm_num
  have h2 : T * T ^ (-(5 / 6 : ℝ)) = T ^ (1 / 6 : ℝ) := by
    have h := Real.rpow_add hTpos (x := T) (y := (1 : ℝ)) (z := -(5 / 6 : ℝ))
    rw [show (1 : ℝ) + -(5 / 6) = 1 / 6 by norm_num, Real.rpow_one] at h
    exact h.symm
  rw [lille, KH, lilleTilde, ← hT, mul_pow, h1]
  calc T * (KHt ^ 2 * T ^ (-(5 / 6 : ℝ))) = (T * T ^ (-(5 / 6 : ℝ))) * KHt ^ 2 := by ring
    _ = T ^ (1 / 6 : ℝ) * KHt ^ 2 := by rw [h2]

end Work.BoseB7
