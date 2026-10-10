import Mathlib
import Submission.Work.MotC5N3.Defs
import Submission.Work.MotV.Defs
import Submission.Work.MotV5.Defs

set_option linter.unusedVariables false -- v435-speed

-- v435-port: begin
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- v435-port: end

namespace Work.MotC5N3.LamAS
/-- **The map induced by an `𝕜`-algebra automorphism of `Work.MotC5N3.OmA K D` on the constants `Work.MotC5N3.KbA K`.**  If `g`
carries the image of `Work.MotC5N3.KbA K` into itself, then it acts there as an `𝕜`-algebra endomorphism `ψ`
(automatically injective).  Route (bookkeeping) in
`Submission/Work/MotV5/LamAS/GUIDE_induced_coeffAlgHom.md`. -/
theorem exists_coeffAlgHom_induced {𝕜 : Type} [Field 𝕜] {K : Type} [Field K] [Algebra 𝕜 K] (D : Work.MotV.KleinData 𝕜)
    (g : Work.MotC5N3.OmA K D ≃ₐ[𝕜] Work.MotC5N3.OmA K D)
    (hgKb : ∀ c : Work.MotC5N3.KbA K, ∃ c' : Work.MotC5N3.KbA K,
      g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
        = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c') :
    ∃ ψ : Work.MotC5N3.KbA K →ₐ[𝕜] Work.MotC5N3.KbA K, Function.Injective ψ ∧
      ∀ c : Work.MotC5N3.KbA K,
        g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
          = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψ c) := by
  classical
  -- `algebraMap` from the constants into the function field is injective (a ring map of fields),
  -- so the witness for `g (algebraMap c)` is unique and `ψ` is well defined.
  have hinj : Function.Injective (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)) :=
    RingHom.injective _
  -- The value of `ψ` on `c`: the (chosen) preimage witness of `g (algebraMap c)`.
  let ψfun : Work.MotC5N3.KbA K → Work.MotC5N3.KbA K := fun c => Classical.choose (hgKb c)
  have hψ : ∀ c : Work.MotC5N3.KbA K,
      g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c)
        = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun c) :=
    fun c => Classical.choose_spec (hgKb c)
  -- The defining property, read the other way round.
  have key : ∀ c : Work.MotC5N3.KbA K,
      algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun c)
        = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) c) :=
    fun c => (hψ c).symm
  -- `ψfun` is a ring homomorphism because `g` is one and `algebraMap` is injective.
  let ψ : Work.MotC5N3.KbA K →ₐ[𝕜] Work.MotC5N3.KbA K :=
    { toFun := ψfun
      map_one' := hinj (by
        rw [key 1, map_one (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)), map_one g])
      map_mul' := fun a b => hinj (calc
        algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun (a * b))
            = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (a * b)) := key (a * b)
        _ = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) a
                * algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) b) :=
              congrArg g (map_mul (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)) a b)
        _ = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) a)
                * g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) b) :=
              map_mul g _ _
        _ = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun a)
                * algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun b) := by
              rw [key a, key b]
        _ = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun a * ψfun b) :=
              (map_mul (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)) (ψfun a) (ψfun b)).symm)
      map_zero' := hinj (by
        rw [key 0, map_zero (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)), map_zero g])
      map_add' := fun a b => hinj (calc
        algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun (a + b))
            = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (a + b)) := key (a + b)
        _ = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) a
                + algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) b) :=
              congrArg g (map_add (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)) a b)
        _ = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) a)
                + g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) b) :=
              map_add g _ _
        _ = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun a)
                + algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun b) := by
              rw [key a, key b]
        _ = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun a + ψfun b) :=
              (map_add (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)) (ψfun a) (ψfun b)).symm)
      commutes' := fun a => hinj (calc
        algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (ψfun (algebraMap 𝕜 (Work.MotC5N3.KbA K) a))
            = g (algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D)
                  (algebraMap 𝕜 (Work.MotC5N3.KbA K) a)) := key _
        _ = g (algebraMap 𝕜 (Work.MotC5N3.OmA K D) a) :=
              congrArg g (IsScalarTower.algebraMap_apply 𝕜 (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) a).symm
        _ = algebraMap 𝕜 (Work.MotC5N3.OmA K D) a := AlgEquiv.commutes g a
        _ = algebraMap (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) (algebraMap 𝕜 (Work.MotC5N3.KbA K) a) :=
              IsScalarTower.algebraMap_apply 𝕜 (Work.MotC5N3.KbA K) (Work.MotC5N3.OmA K D) a) }
  exact ⟨ψ, RingHom.injective (ψ : Work.MotC5N3.KbA K →+* Work.MotC5N3.KbA K), fun c => hψ c⟩

end Work.MotC5N3.LamAS