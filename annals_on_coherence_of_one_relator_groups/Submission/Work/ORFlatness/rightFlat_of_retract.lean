import Mathlib
import Submission.Work.ORFlatness.Flat
import Submission.Work.ORFlatness.injective_map_of_retract

namespace Work.ORFlatness

universe u

/-- Right flatness is inherited by retracts: if a right `R`-module `X` is a retract of a
right flat right `R`-module `F` (that is, `ι : X → F`, `r : F → X` with `r ∘ ι = id`),
then `X` is right flat.

Proof: for an injective `g : M →ₗ[R] N`, the maps `a = ι ⊗ id_M : X ⊗ M → F ⊗ M` and
`b = r ⊗ id_M : F ⊗ M → X ⊗ M` satisfy `b ∘ a = (r ∘ ι) ⊗ id_M = id`, and by naturality
`(id_F ⊗ g) ∘ a = (ι ⊗ id_N) ∘ (id_X ⊗ g)`.  Hence if `(id_X ⊗ g) x = (id_X ⊗ g) y`
then applying `id_F ⊗ g` after `a` and using that `id_F ⊗ g` is injective (right flatness
of `F`) gives `a x = a y`, and applying `b` gives `x = y`. -/
theorem rightFlat_of_retract {R : Type u} [Ring R] {F X : Type u}
    [AddCommGroup F] [Module Rᵐᵒᵖ F] [AddCommGroup X] [Module Rᵐᵒᵖ X]
    (hF : RightFlat R F) (ι : X →ₗ[Rᵐᵒᵖ] F) (r : F →ₗ[Rᵐᵒᵖ] X)
    (hr : r.comp ι = LinearMap.id) : RightFlat R X := by
  intro M N _ _ _ _ g hg
  have hretract : (BalTensor.map R r (LinearMap.id : M →ₗ[R] M)).comp
      (BalTensor.map R ι (LinearMap.id : M →ₗ[R] M)) = AddMonoidHom.id _ := by
    rw [← BalTensor.map_comp, hr]
    simp [BalTensor.map_id]
  have hnat : (BalTensor.map R (LinearMap.id : F →ₗ[Rᵐᵒᵖ] F) g).comp
        (BalTensor.map R ι (LinearMap.id : M →ₗ[R] M)) =
      (BalTensor.map R ι (LinearMap.id : N →ₗ[R] N)).comp
        (BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) g) := by
    rw [← BalTensor.map_comp, ← BalTensor.map_comp]
    simp
  have hinjF : Function.Injective (BalTensor.map R (LinearMap.id : F →ₗ[Rᵐᵒᵖ] F) g) :=
    hF g hg
  intro x y hxy
  have hu : ∀ z : BalTensor R X M,
      (BalTensor.map R (LinearMap.id : F →ₗ[Rᵐᵒᵖ] F) g)
        ((BalTensor.map R ι (LinearMap.id : M →ₗ[R] M)) z) =
      (BalTensor.map R ι (LinearMap.id : N →ₗ[R] N))
        ((BalTensor.map R (LinearMap.id : X →ₗ[Rᵐᵒᵖ] X) g) z) := by
    intro z
    have hcomp := congrArg (fun (f : BalTensor R X M →+ BalTensor R F N) => f z) hnat
    simpa only [AddMonoidHom.comp_apply] using hcomp
  have haxy : (BalTensor.map R ι (LinearMap.id : M →ₗ[R] M)) x =
      (BalTensor.map R ι (LinearMap.id : M →ₗ[R] M)) y := by
    apply hinjF
    rw [hu x, hu y, hxy]
  calc x = (BalTensor.map R r (LinearMap.id : M →ₗ[R] M))
        ((BalTensor.map R ι (LinearMap.id : M →ₗ[R] M)) x) := by
        rw [← AddMonoidHom.comp_apply, hretract, AddMonoidHom.id_apply]
    _ = (BalTensor.map R r (LinearMap.id : M →ₗ[R] M))
        ((BalTensor.map R ι (LinearMap.id : M →ₗ[R] M)) y) := by rw [haxy]
    _ = y := by
        rw [← AddMonoidHom.comp_apply, hretract, AddMonoidHom.id_apply]

end Work.ORFlatness
