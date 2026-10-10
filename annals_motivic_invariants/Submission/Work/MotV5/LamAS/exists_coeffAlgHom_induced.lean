import Mathlib
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotV5.LamAS

/-- **The map induced by an `𝕜`-algebra automorphism of `Om D` on the constants `Kb 𝕜`.**  If `g`
carries the image of `Kb 𝕜` into itself, then it acts there as an `𝕜`-algebra endomorphism `ψ`
(automatically injective).  Route (bookkeeping) in
`Submission/Work/MotV5/LamAS/GUIDE_induced_coeffAlgHom.md`. -/
theorem exists_coeffAlgHom_induced {𝕜 : Type} [Field 𝕜] (D : Work.MotV.KleinData 𝕜)
    (g : Work.MotV.Om D ≃ₐ[𝕜] Work.MotV.Om D)
    (hgKb : ∀ c : Work.MotV.Kb 𝕜, ∃ c' : Work.MotV.Kb 𝕜,
      g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c') :
    ∃ ψ : Work.MotV.Kb 𝕜 →ₐ[𝕜] Work.MotV.Kb 𝕜, Function.Injective ψ ∧
      ∀ c : Work.MotV.Kb 𝕜,
        g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
          = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (ψ c) := by
  classical
  -- `algebraMap` from the constants into the function field is injective (a ring map of fields),
  -- so the witness for `g (algebraMap c)` is unique and `ψ` is well defined.
  have hinj : Function.Injective (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)) :=
    RingHom.injective _
  -- The value of `ψ` on `c`: the (chosen) preimage witness of `g (algebraMap c)`.
  let ψfun : Work.MotV.Kb 𝕜 → Work.MotV.Kb 𝕜 := fun c => Classical.choose (hgKb c)
  have hψ : ∀ c : Work.MotV.Kb 𝕜,
      g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c)
        = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (ψfun c) :=
    fun c => Classical.choose_spec (hgKb c)
  -- The defining property, read the other way round.
  have key : ∀ c : Work.MotV.Kb 𝕜,
      algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (ψfun c)
        = g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) c) :=
    fun c => (hψ c).symm
  -- `ψfun` is a ring homomorphism because `g` is one and `algebraMap` is injective.
  let ψ : Work.MotV.Kb 𝕜 →ₐ[𝕜] Work.MotV.Kb 𝕜 :=
    { toFun := ψfun
      map_one' := hinj (by
        rw [key 1, map_one (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)), map_one g])
      map_mul' := fun a b => hinj (calc
        algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (ψfun (a * b))
            = g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (a * b)) := key (a * b)
        _ = g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) a
                * algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) b) :=
              congrArg g (map_mul (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)) a b)
        _ = g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) a)
                * g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) b) :=
              map_mul g _ _
        _ = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (ψfun a)
                * algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (ψfun b) := by
              rw [key a, key b]
        _ = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (ψfun a * ψfun b) :=
              (map_mul (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)) (ψfun a) (ψfun b)).symm)
      map_zero' := hinj (by
        rw [key 0, map_zero (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)), map_zero g])
      map_add' := fun a b => hinj (calc
        algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (ψfun (a + b))
            = g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (a + b)) := key (a + b)
        _ = g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) a
                + algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) b) :=
              congrArg g (map_add (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)) a b)
        _ = g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) a)
                + g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) b) :=
              map_add g _ _
        _ = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (ψfun a)
                + algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (ψfun b) := by
              rw [key a, key b]
        _ = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (ψfun a + ψfun b) :=
              (map_add (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)) (ψfun a) (ψfun b)).symm)
      commutes' := fun a => hinj (calc
        algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (ψfun (algebraMap 𝕜 (Work.MotV.Kb 𝕜) a))
            = g (algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D)
                  (algebraMap 𝕜 (Work.MotV.Kb 𝕜) a)) := key _
        _ = g (algebraMap 𝕜 (Work.MotV.Om D) a) :=
              congrArg g (IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) a).symm
        _ = algebraMap 𝕜 (Work.MotV.Om D) a := AlgEquiv.commutes g a
        _ = algebraMap (Work.MotV.Kb 𝕜) (Work.MotV.Om D) (algebraMap 𝕜 (Work.MotV.Kb 𝕜) a) :=
              IsScalarTower.algebraMap_apply 𝕜 (Work.MotV.Kb 𝕜) (Work.MotV.Om D) a) }
  exact ⟨ψ, RingHom.injective (ψ : Work.MotV.Kb 𝕜 →+* Work.MotV.Kb 𝕜), fun c => hψ c⟩

end Work.MotV5.LamAS
