import Mathlib
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

The Artin–Schreier root `W = algebraMap (Kb 𝕜) (Om D) (asRoot g)` does **not** lie in the
*corrected* AS twist field `asTwistFieldFix D τ σS` — the fixed field of the twisted action
`σ' = τ.trans (σS.restrictScalars _)` (i.e. `x ↦ σS (τ x)`).

This is the sanity check that distinguishes the corrected definition from the interpolation
model `asTwistField D g`, which *does* contain `asRoot g` (see
`Submission/Work/MotV5/asTwistField_contains_asRoot.lean`).

The argument is one line of Galois bookkeeping.  Write `W := algebraMap (Kb 𝕜) (Om D) (asRoot g)`.

* `W` is `Kb 𝕜`-rational, hence fixed by the `Kb 𝕜`-linear shift `σS`
  (`AlgEquiv.commutes`).
* `τ W = algebraMap (Kb 𝕜) (Om D) (σ (asRoot g)) = algebraMap (Kb 𝕜) (Om D) (asRoot g + 1) = W + 1`
  by `hτ` and `hσ`.

Hence `σ' W = σS (τ W) = σS (W + 1) = W + 1 ≠ W`: the generator `σ'` of the cyclic group does not
fix `W`, so `W` is not in the fixed field `asTwistFieldFix D τ σS`.

Nothing about `σS` beyond `Kb 𝕜`-linearity is used: no `ShiftCompat`, no `Nonconstant`, no
smoothness of the Klein data.
-/

namespace Work.MotV5

theorem asRoot_notMem_asTwistFieldFix (𝕜 : Type) [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (g : RatFunc 𝕜) (σ : Work.MotV.Kb 𝕜 ≃ₐ[RatFunc 𝕜] Work.MotV.Kb 𝕜)
    (hσ : σ (Work.MotV5.asRoot g) = Work.MotV5.asRoot g + 1)
    (τ : Work.MotV.Om D ≃ₐ[RatFunc 𝕜] Work.MotV.Om D)
    (hτ : ∀ c : Work.MotV.Kb 𝕜,
      τ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (σ c))
    (σS : Work.MotV.Om D ≃ₐ[Work.MotV.Kb 𝕜] Work.MotV.Om D) :
    algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g)
      ∉ Work.MotV5.asTwistFieldFix D τ σS := by
  intro hx
  -- membership in the fixed field means: fixed by every element of `zpowers σ'`, in particular by
  -- the generator `σ' = asTwistAction D τ σS`.
  rw [Work.MotV5.asTwistFieldFix, IntermediateField.mem_fixedField_iff] at hx
  have hgen := hx _ (Subgroup.mem_zpowers _)
  -- `τ` sends the AS root to `asRoot g + 1`.
  have hτW : τ (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g))
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g) + 1 := by
    rw [hτ (Work.MotV5.asRoot g), hσ, map_add, map_one]
  -- the twisted action sends it to `W + 1`, because `σS` is `Kb 𝕜`-linear.
  have hkey : Work.MotV5.asTwistAction D τ σS
        (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g))
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g) + 1 := by
    rw [Work.MotV5.asTwistAction, AlgEquiv.trans_apply, AlgEquiv.restrictScalars_apply,
      hτW, map_add, map_one, σS.commutes]
  rw [hkey] at hgen
  -- `W + 1 = W` forces `1 = 0` in the field `Om D`.
  have h2 : algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g) + 1
      = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (Work.MotV5.asRoot g) + 0 := by
    rw [add_zero]
    exact hgen
  exact one_ne_zero (add_left_cancel h2)

end Work.MotV5
