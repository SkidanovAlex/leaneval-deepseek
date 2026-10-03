import Mathlib
import Submission.Work.ORFlatness.Flat

namespace Work.ORFlatness

universe u

/-- The balanced tensor product `Work.ORFlatness.BalTensor` of a split injection of
right `R`-modules is injective: if `r ∘ ι = LinearMap.id` then
`BalTensor.map R ι (LinearMap.id : N →ₗ[R] N)` is injective.

Proof: `(BalTensor.map R r id).comp (BalTensor.map R ι id) = BalTensor.map R (r.comp ι) id
= BalTensor.map R LinearMap.id LinearMap.id = AddMonoidHom.id`, using
`Work.ORFlatness.BalTensor.map_comp`, `Work.ORFlatness.BalTensor.map_id` and
`Work.ORFlatness.BalTensor.map_mk`; hence `map ι id` is injective (`y = 0` follows from
`map ι id y = 0` by applying `map r id`). -/
theorem injective_map_of_retract {R : Type u} [Ring R] {K Q : Type u}
    [AddCommGroup K] [Module Rᵐᵒᵖ K] [AddCommGroup Q] [Module Rᵐᵒᵖ Q]
    (ι : K →ₗ[Rᵐᵒᵖ] Q) (r : Q →ₗ[Rᵐᵒᵖ] K) (hr : r.comp ι = LinearMap.id)
    (N : Type u) [AddCommGroup N] [Module R N] :
    Function.Injective
      (Work.ORFlatness.BalTensor.map R ι (LinearMap.id : N →ₗ[R] N)) := by
  have hcomp : (BalTensor.map R r (LinearMap.id : N →ₗ[R] N)).comp
      (BalTensor.map R ι (LinearMap.id : N →ₗ[R] N)) = AddMonoidHom.id _ := by
    rw [← BalTensor.map_comp]
    rw [hr, LinearMap.id_comp, BalTensor.map_id]
  have hleft : Function.LeftInverse (BalTensor.map R r (LinearMap.id : N →ₗ[R] N))
      (BalTensor.map R ι (LinearMap.id : N →ₗ[R] N)) := by
    intro y
    rw [← AddMonoidHom.comp_apply, hcomp, AddMonoidHom.id_apply]
  exact hleft.injective

end Work.ORFlatness
