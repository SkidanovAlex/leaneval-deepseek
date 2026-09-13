import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Commons.LinearAlgebra.LinearMap

open Module

/-- For a linear map `f : V →ₗ[K] W` with `V` finite-dimensional and a submodule `S ≤ W`,
the dimension of the preimage `comap f S` decomposes as the dimension of the kernel of `f`
plus the dimension of `S ⊓ range f`. This is the dimension formula for the restriction of `f`
to a preimage: `(comap f S) ⧸ ker f ≃ₗ S ⊓ range f`. -/
theorem finrank_comap_eq {K V W : Type*} [Field K] [AddCommGroup V] [Module K V]
    [AddCommGroup W] [Module K W] [FiniteDimensional K V]
    (f : V →ₗ[K] W) (S : Submodule K W) :
    Module.finrank K ↥(Submodule.comap f S) =
      Module.finrank K ↥(LinearMap.ker f) + Module.finrank K ↥(S ⊓ LinearMap.range f) := by
  let V' := Submodule.comap f S
  let g : V' →ₗ[K] W := f.comp V'.subtype
  have hg : finrank K (LinearMap.range g) + finrank K (LinearMap.ker g) = finrank K V' :=
    LinearMap.finrank_range_add_finrank_ker g
  have hrange : LinearMap.range g = S ⊓ LinearMap.range f := by
    rw [show LinearMap.range g = Submodule.map f V' from ?_, Submodule.map_comap_eq]
    · exact inf_comm _ _
    · change LinearMap.range (f.comp V'.subtype) = _
      rw [LinearMap.range_comp, Submodule.range_subtype]
  have hker : LinearMap.ker g = Submodule.comap V'.subtype (LinearMap.ker f) := by
    change LinearMap.ker (f.comp V'.subtype) = _
    rw [LinearMap.ker_comp]
  have hker_finrank : finrank K (LinearMap.ker g) = finrank K (LinearMap.ker f) := by
    rw [hker]
    exact LinearEquiv.finrank_eq (Submodule.comapSubtypeEquivOfLe (LinearMap.ker_le_comap f))
  rw [hrange, hker_finrank, add_comm] at hg
  dsimp only [V'] at hg
  exact hg.symm

end Commons.LinearAlgebra.LinearMap