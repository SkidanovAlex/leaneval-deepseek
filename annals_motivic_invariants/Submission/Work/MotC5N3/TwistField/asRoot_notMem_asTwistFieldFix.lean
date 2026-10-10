import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV5.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotK.KleinData

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

/-!
# `asRoot g ∉ asTwistFieldFix D τ σS`

The Artin–Schreier root `W = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (asRoot g)` does **not** lie in the
*corrected* AS twist field `asTwistFieldFix D τ σS` — the fixed field of the twisted action
`σ' = τ.trans (σS.restrictScalars _)` (i.e. `x ↦ σS (τ x)`).

This is the sanity check that distinguishes the corrected definition from the interpolation
model `asTwistField D g`, which *does* contain `asRoot g` (see
`Submission/Work/MotV5/asTwistField_contains_asRoot.lean`).

The argument is one line of Galois bookkeeping.  Write `W := algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (asRoot g)`.

* `W` is `Work.MotC5N3.KbA K`-rational, hence fixed by the `Work.MotC5N3.KbA K`-linear shift `σS`
  (`AlgEquiv.commutes`).
* `τ W = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (σ (asRoot g)) = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (asRoot g + 1) = W + 1`
  by `hτ` and `hσ`.

Hence `σ' W = σS (τ W) = σS (W + 1) = W + 1 ≠ W`: the generator `σ'` of the cyclic group does not
fix `W`, so `W` is not in the fixed field `asTwistFieldFix D τ σS`.

Nothing about `σS` beyond `Work.MotC5N3.KbA K`-linearity is used: no `ShiftCompat`, no `Nonconstant`, no
smoothness of the Klein data.
-/

namespace Work.MotC5N3
open Work.MotV5
theorem asRoot_notMem_asTwistFieldFix (𝕜 : Type) [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜)
    (g : K) (σ : Work.MotC5N3.KbA K ≃ₐ[K] Work.MotC5N3.KbA K)
    (hσ : σ (Work.MotC5N3.asRoot g) = Work.MotC5N3.asRoot g + 1)
    (τ : Work.MotC5N3.OmA K D ≃ₐ[K] Work.MotC5N3.OmA K D)
    (hτ : ∀ c : Work.MotC5N3.KbA K,
      τ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
        = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (σ c))
    (σS : Work.MotC5N3.OmA K D ≃ₐ[Work.MotC5N3.KbA K] Work.MotC5N3.OmA K D) :
    algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot g)
      ∉ Work.MotC5N3.asTwistFieldFix D τ σS := by
  intro hx
  -- membership in the fixed field means: fixed by every element of `zpowers σ'`, in particular by
  -- the generator `σ' = asTwistAction D τ σS`.
  rw [Work.MotC5N3.asTwistFieldFix, IntermediateField.mem_fixedField_iff] at hx
  have hgen := hx _ (Subgroup.mem_zpowers _)
  -- `τ` sends the AS root to `asRoot g + 1`.
  have hτW : τ (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot g))
      = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot g) + 1 := by
    rw [hτ (Work.MotC5N3.asRoot g), hσ, map_add, map_one]
  -- the twisted action sends it to `W + 1`, because `σS` is `Work.MotC5N3.KbA K`-linear.
  have hkey : Work.MotC5N3.asTwistAction D τ σS
        (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot g))
      = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot g) + 1 := by
    rw [Work.MotC5N3.asTwistAction, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
      hτW, map_add, map_one, σS.commutes]
  rw [hkey] at hgen
  -- `W + 1 = W` forces `1 = 0` in the field `Work.MotC5N3.OmA K D`.
  have h2 : algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot g) + 1
      = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (Work.MotC5N3.asRoot g) + 0 := by
    rw [add_zero]
    exact hgen
  exact one_ne_zero (add_left_cancel h2)

end Work.MotC5N3