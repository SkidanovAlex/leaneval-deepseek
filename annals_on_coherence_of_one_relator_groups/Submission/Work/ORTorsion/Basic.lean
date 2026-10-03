/-
# Node N8: elementary linear-algebra helpers for the torsion crux

Tensoring with a `K`-module over a field preserves injectivity (all `K`-modules are flat),
and the resulting injectivity statements for subalgebra inclusions.
-/
import Mathlib
import Submission.Work.ORTorsion.Defs

set_option autoImplicit false
set_option maxHeartbeats 1000000

open scoped TensorProduct

namespace Work.ORTorsion

variable {K : Type*} [Field K] {G : Type*} [Group G] {U : Type*} [Ring U] [Algebra K U]

/-- Tensoring with a `K`-module over a field preserves injectivity. -/
theorem map_id_injective {V M N : Type*} [AddCommGroup V] [Module K V]
    [AddCommGroup M] [AddCommGroup N] [Module K M] [Module K N]
    (f : M →ₗ[K] N) (hf : Function.Injective f) :
    Function.Injective (TensorProduct.map (LinearMap.id : V →ₗ[K] V) f) :=
  TensorProduct.map_injective_of_flat_flat (LinearMap.id : V →ₗ[K] V) f
    Function.injective_id hf

/-- Tensoring a subalgebra inclusion with the identity is injective. -/
theorem incl_injective {A B : Subalgebra K U} (h : A ≤ B) {V : Type*} [AddCommGroup V]
    [Module K V] :
    Function.Injective (TensorProduct.map (LinearMap.id : V →ₗ[K] V)
      (Subalgebra.inclusion h).toLinearMap) :=
  map_id_injective _ (Subalgebra.inclusion_injective h)

/-- A unit of a ring acts injectively on any module. -/
theorem unit_smul_injective {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] (u : Rˣ) :
    Function.Injective (fun m : M => (u : R) • m) := by
  intro m m' h
  have h' := congrArg (fun x : M => ((u⁻¹ : Rˣ) : R) • x) h
  simpa [smul_smul] using h'

end Work.ORTorsion
