import Mathlib
import Submission.Work.ORFlatness.Flat

namespace Work.ORFinal.Chain

universe u

open Work.ORFlatness

/-- `Tor1Vanishes R X N` only depends on the isomorphism class of the right module `X`.

Given a projective presentation `P₂ → X₂` of `X₂` witnessing `Tor₁^R(X₂, N) = 0`, we pull it
back along `e.symm : X₂ → X₁` to a projective presentation `P₂ → X₁ → 0` of `X₁`; the kernel
of the covering map is unchanged, because `e.symm` is injective
(`ker (e.symm ∘ π) = ker π`).  The map whose injectivity witnesses the vanishing is therefore
the same one, transported along the identification of the two kernels by the canonical
`Rᵐᵒᵖ`-linear equivalence `ψ : ker (e.symm ∘ π) ≃ₗ ker π` (`x ↦ x`), which is compatible with
the inclusions into `P₂.P`. -/
theorem tor1Vanishes_of_linearEquiv (R : Type u) [Ring R]
    (X₁ X₂ : Type u) [AddCommGroup X₁] [Module Rᵐᵒᵖ X₁]
    [AddCommGroup X₂] [Module Rᵐᵒᵖ X₂] (e : X₁ ≃ₗ[Rᵐᵒᵖ] X₂)
    (N : Type u) [AddCommGroup N] [Module R N] :
    Work.ORFlatness.Tor1Vanishes R X₂ N → Work.ORFlatness.Tor1Vanishes R X₁ N := by
  rintro ⟨P₂, hP₂⟩
  let P' : ProjPres R X₁ :=
    { P := P₂.P
      π := (e.symm : X₂ →ₗ[Rᵐᵒᵖ] X₁).comp P₂.π
      surj := e.symm.surjective.comp P₂.surj }
  refine ⟨P', ?_⟩
  have hK : P'.K = P₂.K := by
    change LinearMap.ker ((e.symm : X₂ →ₗ[Rᵐᵒᵖ] X₁).comp P₂.π) = LinearMap.ker P₂.π
    rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot]
  -- the canonical identification of the kernel of `e.symm ∘ π` with the kernel of `π`
  let ψ : P'.K ≃ₗ[Rᵐᵒᵖ] P₂.K :=
    { toFun := fun x => ⟨x.1, hK ▸ x.2⟩
      invFun := fun y => ⟨y.1, hK.symm ▸ y.2⟩
      left_inv := fun x => rfl
      right_inv := fun y => rfl
      map_add' := fun x y => rfl
      map_smul' := fun a x => rfl }
  have hsub : Submodule.subtype P'.K
      = (Submodule.subtype P₂.K).comp (ψ : P'.K →ₗ[Rᵐᵒᵖ] P₂.K) := by
    ext x
    rfl
  have hψinj : Function.Injective
      (BalTensor.map R (ψ : P'.K →ₗ[Rᵐᵒᵖ] P₂.K) (LinearMap.id : N →ₗ[R] N)) := by
    have hcomp : (BalTensor.map R (ψ.symm : P₂.K →ₗ[Rᵐᵒᵖ] P'.K)
          (LinearMap.id : N →ₗ[R] N)).comp
        (BalTensor.map R (ψ : P'.K →ₗ[Rᵐᵒᵖ] P₂.K) (LinearMap.id : N →ₗ[R] N))
        = AddMonoidHom.id (BalTensor R P'.K N) := by
      rw [← BalTensor.map_comp]
      simp
    intro a b hab
    have h1 : BalTensor.map R (ψ.symm : P₂.K →ₗ[Rᵐᵒᵖ] P'.K) (LinearMap.id : N →ₗ[R] N)
        (BalTensor.map R (ψ : P'.K →ₗ[Rᵐᵒᵖ] P₂.K) (LinearMap.id : N →ₗ[R] N) a) = a := by
      simpa using congrArg (fun f : BalTensor R P'.K N →+ BalTensor R P'.K N => f a) hcomp
    have h2 : BalTensor.map R (ψ.symm : P₂.K →ₗ[Rᵐᵒᵖ] P'.K) (LinearMap.id : N →ₗ[R] N)
        (BalTensor.map R (ψ : P'.K →ₗ[Rᵐᵒᵖ] P₂.K) (LinearMap.id : N →ₗ[R] N) b) = b := by
      simpa using congrArg (fun f : BalTensor R P'.K N →+ BalTensor R P'.K N => f b) hcomp
    rw [hab] at h1
    exact h1.symm.trans h2
  have hmap : BalTensor.map R (Submodule.subtype P'.K) (LinearMap.id : N →ₗ[R] N)
      = (BalTensor.map R (Submodule.subtype P₂.K) (LinearMap.id : N →ₗ[R] N)).comp
        (BalTensor.map R (ψ : P'.K →ₗ[Rᵐᵒᵖ] P₂.K) (LinearMap.id : N →ₗ[R] N)) := by
    rw [hsub]
    have h := BalTensor.map_comp (R := R) (Submodule.subtype P₂.K) (LinearMap.id : N →ₗ[R] N)
      (ψ : P'.K →ₗ[Rᵐᵒᵖ] P₂.K) (LinearMap.id : N →ₗ[R] N)
    simpa only [LinearMap.id_comp] using h
  rw [hmap]
  exact hP₂.comp hψinj

end Work.ORFinal.Chain
