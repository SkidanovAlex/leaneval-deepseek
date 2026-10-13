/-
# `Work.FTS.RegPkgGal.Der.C1JetFstar` — the static profile `F_*` is a `C1Jet`

`Work.FTS.RegPkgGal.C1Jet α S N h` (`Der.Defs`) bundles the two facts needed to differentiate the
constituents of the right-hand side of the fake-time equation in `z`:

* the joint `Jet` data of `Work.FTS.Regularity` (a uniform bound `N` and a joint `α`-Hölder modulus
  for the metric `|Δz| + |Δθ| + |Δτ|` on the strip `z ≥ 0`, `θ ∈ Iθ`, `τ ∈ [0,S]`), and
* the `z`-differentiability of every slice `z ↦ h z θ τ` on `z > 0`, with derivative bounded by
  `N` uniformly in `(θ,τ)`.

This file supplies the **base case** of the closure induction of node `Var`: the *static profile*

  `(z,θ,τ) ↦ F_*(z,θ) = pExp α·(Γ(θ)/c(pExp α))·2z/(1+z)²`

(`Work.Construction.Fstar (pExp α)`, `pExp α = 3α`) is a `C1Jet` with the constant
`100 + 20·pExp α`.

The two halves are the two already-proved quantitative facts about the static profile:

* the `Jet` half is `Work.FTS.Regularity.gammaFstarModuli` / `fstar_joint_modulus`:
  `|F_*(z,θ)| ≤ 20·Γ(θ) ≤ 20` and
  `|F_*(z,θ) - F_*(z',θ')| ≤ 100·(|z-z'| + |θ-θ'|)^α`, the latter upgraded to the metric that
  includes `|τ - τ'|` by monotonicity of `x ↦ x^α` (the profile does not depend on `τ` at all, so
  the `τ`-modulus is free);
* the `z`-derivative half is `Work.FTS.Regularity.fstarDzUniform` / `fstarDz_abs_le`:
  `∂_zF_*(z,θ) = (pExp α·(Γ(θ)/c))·deriv F_*(z)` with
  `|∂_zF_*(z,θ)| ≤ 20·pExp α`, the `z`-slice being differentiable by
  `Work.ConstructionInstance.hasDerivAt_Fstar_z` (which is `Work.FM.hasDerivAt_Fstar` times the
  `θ`-dependent constant, `z > -1`).

Both constants are well below `100 + 20·pExp α`, which is the box used downstream.
-/
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Submission.Work.FTS.RegPkgGal.Der.Defs
import Submission.Work.FTS.Regularity.gammaFstarModuli
import Submission.Work.FTS.Regularity.fstarDzUniform
import Submission.Work.FM.Core
import Submission.Work.ConstructionInstance.profile_add_z_pz_abs_le

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

noncomputable section

set_option autoImplicit false

namespace Work.FTS.RegPkgGal.Der

open Work.FTS.Regularity

/-! ## The `z`-derivative of the static profile slice -/

/-- The `z`-derivative of the slice `z' ↦ F_*(z',θ)` of the static profile: the profile factors as
`(p·(Γ(θ)/c(p)))·F_*(z')` with a `z`-independent coefficient, so its `z`-derivative is the
coefficient times `deriv F_*`. -/
theorem pz_Fstar_eq (p z θ : ℝ) :
    Work.Spaces.pz (Work.Construction.Fstar p) z θ
      = (p * (Work.Spaces.Gam p θ / Work.Spaces.c p)) * deriv Work.FM.Fstar z := by
  change deriv (fun z' => Work.Construction.Fstar p z' θ) z = _
  have hfun : (fun z' => Work.Construction.Fstar p z' θ)
      = fun z' => (p * (Work.Spaces.Gam p θ / Work.Spaces.c p)) * Work.FM.Fstar z' := by
    funext z'; simp only [Work.Construction.Fstar]
  rw [hfun, deriv_const_mul_field]

/-- The uniform `z`-derivative box of the static profile: `|∂_zF_*(z,θ)| ≤ 20·pExp α` for
`z ≥ 0` and `θ ∈ Iθ` (this is `Work.FTS.Regularity.fstarDz_abs_le`, transported across the
definitional unfolding of `pz`). -/
theorem pz_Fstar_pExp_abs_le {α z θ : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3)
    (hz : 0 ≤ z) (hθ : θ ∈ Work.Spaces.Iθ) :
    |Work.Spaces.pz (Work.Construction.Fstar (pExp α)) z θ| ≤ 20 * pExp α := by
  rw [pz_Fstar_eq]
  exact Work.FTS.Regularity.fstarDz_abs_le hα hα13 hz hθ

/-! ## The target -/

theorem C1JetFstar {α S : ℝ} (hα : 0 < α) (hα13 : α ≤ 1 / 3) :
    Work.FTS.RegPkgGal.C1Jet α S (100 + 20 * Work.FTS.Regularity.pExp α)
      (fun z θ _ => Work.Construction.Fstar (Work.FTS.Regularity.pExp α) z θ) := by
  have hp0 : 0 < pExp α := pExp_pos hα
  have hN : 0 ≤ 100 + 20 * pExp α := by linarith
  refine ⟨⟨hN, ?_, ?_⟩, ?_⟩
  · -- the uniform (`C⁰`) bound: `|F_*| ≤ 20Γ ≤ 20`
    intro z θ τ hz hθ _hτ
    calc |Work.Construction.Fstar (pExp α) z θ|
        ≤ 20 * Work.FTS.Regularity.Gamma α θ :=
          Work.FTS.Regularity.fstar_abs_le_gamma hα hα13 hz hθ
      _ ≤ 20 * 1 :=
          mul_le_mul_of_nonneg_left (Work.ConstructionInstance.Gamma_le_one hα.le hθ)
            (by norm_num)
      _ ≤ 100 + 20 * pExp α := by linarith
  · -- the joint `α`-Hölder modulus for the metric `|Δz| + |Δθ| + |Δτ|`
    intro z z' θ θ' τ τ' hz hz' hθ hθ' _hτ _hτ'
    have hD : 0 ≤ |z - z'| + |θ - θ'| := add_nonneg (abs_nonneg _) (abs_nonneg _)
    have hD' : 0 ≤ |z - z'| + |θ - θ'| + |τ - τ'| :=
      add_nonneg hD (abs_nonneg _)
    have hmono : (|z - z'| + |θ - θ'|) ^ α ≤ (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
      Real.rpow_le_rpow hD (le_add_of_nonneg_right (abs_nonneg _)) hα.le
    calc |Work.Construction.Fstar (pExp α) z θ - Work.Construction.Fstar (pExp α) z' θ'|
        ≤ 100 * (|z - z'| + |θ - θ'|) ^ α :=
          Work.FTS.Regularity.fstar_joint_modulus hα hα13 hz hz' hθ hθ'
      _ ≤ 100 * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
          mul_le_mul_of_nonneg_left hmono (by norm_num)
      _ ≤ (100 + 20 * pExp α) * (|z - z'| + |θ - θ'| + |τ - τ'|) ^ α :=
          mul_le_mul_of_nonneg_right (by linarith) (Real.rpow_nonneg hD' α)
  · -- the `z`-derivative box on `z > 0`
    intro τ _hτ θ hθ z hz
    have hz0 : 0 < z := hz
    refine ⟨Work.Spaces.pz (Work.Construction.Fstar (pExp α)) z θ,
      Work.ConstructionInstance.hasDerivAt_Fstar_z (p := pExp α) z θ (by linarith), ?_⟩
    calc |Work.Spaces.pz (Work.Construction.Fstar (pExp α)) z θ| ≤ 20 * pExp α :=
          pz_Fstar_pExp_abs_le hα hα13 hz0.le hθ
      _ ≤ 100 + 20 * pExp α := by linarith

end Work.FTS.RegPkgGal.Der
