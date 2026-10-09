import Mathlib
import Submission.NK.ShimizuRank.HausRank
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace NK.ShimizuRank

set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

open NK.Reconstruct

/-
**`NK.Reconstruct.HausQuot K K' ℓ` is torsion-free**, unconditionally.

see the docstring in the task for the mathematical argument.
-/
theorem hausQuot_torsionFree {K : Type*} [Field K] [NumberField K] {K' : Type*} [Field K']
    [Algebra K K'] [IsGalois K K'] {ℓ : ℕ} [Fact ℓ.Prime] :
    Module.IsTorsionFree (PadicInt ℓ) (NK.Reconstruct.HausQuot K K' ℓ) := by
  let Φ : Additive (Gamma K K' ℓ) →ₗ[PadicInt ℓ]
      (Dual (Gamma K K' ℓ) ℓ → PadicInt ℓ) :=
    { toFun := fun x g => dualToLinear g x
      map_add' := fun x y => by funext g; simp
      map_smul' := fun a x => by
        funext g
        simp [smul_eq_mul] }
  have hker : LinearMap.ker Φ = invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ) := by
    ext x
    rw [LinearMap.mem_ker, mem_invisibleSubmodule_iff]
    constructor
    · intro h g; exact congrFun h g
    · intro h; funext g; exact h g
  have hle : invisibleSubmodule (K := K) (K' := K') (ℓ := ℓ) ≤ LinearMap.ker Φ := hker.ge
  let Ψ : HausQuot K K' ℓ →ₗ[PadicInt ℓ] (Dual (Gamma K K' ℓ) ℓ → PadicInt ℓ) :=
    Submodule.liftQ _ Φ hle
  have hkerΨ : LinearMap.ker Ψ = ⊥ := Submodule.ker_liftQ_eq_bot _ _ _ hker.le
  have hinj : Function.Injective Ψ := by
    rw [← LinearMap.ker_eq_bot]
    exact hkerΨ
  exact Function.Injective.moduleIsTorsionFree Ψ hinj (fun a x => map_smul Ψ a x)

end NK.ShimizuRank
