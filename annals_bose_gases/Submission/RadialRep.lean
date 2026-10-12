import ChallengeDeps
import Submission.Bridge
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Radial representation of `IsRadial` functions on `EuclideanSpace ℝ (Fin 3)`

`ChallengeDeps.IsRadial w` says `w` depends only on the norm.  This module
builds the concrete representation of such a function as a profile of the
radius: with `radU0` a fixed unit vector, `w x = radialProfile w ‖x‖` where
`radialProfile w r := w (r • radU0)` for `r ≥ 0` (we only ever evaluate at
`r = ‖x‖ ≥ 0`).

This is the first brick of the Layer-3 (scattering) analysis: the radial
scattering solution `ω` of `ChallengeDeps.IsScatteringSolution` is an
`IsRadial` function, and the scattering equation will be reduced to a 1D
ODE for its profile.
-/

noncomputable section

open _root_.BoseGases
set_option autoImplicit false

namespace Submission.BoseGases

open scoped Real

local notation "ℝ³" => EuclideanSpace ℝ (Fin 3)

/-- The canonical unit vector of `ℝ³` (the first vector of the standard
orthonormal basis built in `Submission.Bridge`). -/
noncomputable def radU0 : ℝ³ := euclBasis3 0

/-- `radU0` has norm one (it is a member of an orthonormal basis). -/
lemma radU0_norm : ‖radU0‖ = 1 := by
  unfold radU0
  exact euclBasis3.orthonormal.1 0

/-- The radial profile of `w` along the axis of `radU0`:
`radialProfile w r := w (r • radU0)`. -/
noncomputable def radialProfile (w : ℝ³ → ℝ) (r : ℝ) : ℝ := w (r • radU0)

/-- The norm of `r • radU0` is `|r|`. -/
lemma norm_smul_radU0 (r : ℝ) : ‖r • radU0‖ = |r| := by
  rw [norm_smul, radU0_norm, mul_one, Real.norm_eq_abs]

/-- A radial function evaluated at `x` equals its radial profile at `‖x‖`. -/
lemma radial_eq_profile {w : ℝ³ → ℝ} (hw : IsRadial w) (x : ℝ³) :
    w x = radialProfile w ‖x‖ := by
  unfold radialProfile
  apply hw
  rw [norm_smul_radU0, abs_of_nonneg (norm_nonneg x)]

/-- Two radial functions agree everywhere iff their profiles agree on
`{r | 0 ≤ r}` (the range of `‖·‖`).  The forward direction is free; the
backward direction uses that every `x` has `‖x‖ ≥ 0` and `x = y` when
profiles agree at `‖x‖` is not needed — rather both sides reduce through
`radial_eq_profile`.) -/
lemma radial_ext {w₁ w₂ : ℝ³ → ℝ} (hw₁ : IsRadial w₁) (hw₂ : IsRadial w₂) :
    (∀ r : ℝ, 0 ≤ r → radialProfile w₁ r = radialProfile w₂ r) → w₁ = w₂ := by
  intro h
  funext x
  rw [radial_eq_profile hw₁ x, radial_eq_profile hw₂ x]
  exact h ‖x‖ (norm_nonneg x)

/-- The radial profile is even in the sense that only the value at the
nonnegative radius matters when evaluated at a norm: `radialProfile w ‖x‖`
is what appears, and here we record that evaluating at `|r|` equals the
value at `r` when `w` is radial (auxiliary, for later use). -/
lemma radialProfile_abs {w : ℝ³ → ℝ} (hw : IsRadial w) (r : ℝ) :
    radialProfile w |r| = radialProfile w r := by
  unfold radialProfile
  apply hw
  rw [norm_smul_radU0, norm_smul_radU0]
  rw [abs_of_nonneg (abs_nonneg r)]

end Submission.BoseGases
