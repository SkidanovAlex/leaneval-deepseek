import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Commons.LinearAlgebra

/-- **Dimension of the image of a subspace.**

For a linear map `f : V →ₗ[K] W` with `V` finite dimensional and a subspace `S ≤ V`,
the image `Submodule.map f S` has dimension `finrank S - finrank (S ⊓ ker f)`.

Proof: restrict `f` to `S`.  The resulting map `g : S →ₗ[K] W` has range
`Submodule.map f S` and kernel `S ⊓ ker f` (viewed inside `S`), so rank–nullity gives
`finrank (map f S) + finrank (S ⊓ ker f) = finrank S`. -/
theorem finrank_map_eq {K : Type*} [Field K] {V W : Type*}
    [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [FiniteDimensional K V] (f : V →ₗ[K] W) (S : Submodule K V) :
    Module.finrank K ↥(Submodule.map f S) =
      Module.finrank K ↥S - Module.finrank K ↥(S ⊓ LinearMap.ker f) := by
  classical
  let g : S →ₗ[K] W := f.comp S.subtype
  have hker_eq : LinearMap.ker g = Submodule.comap S.subtype (S ⊓ LinearMap.ker f) := by
    have h : LinearMap.ker g = Submodule.comap S.subtype (LinearMap.ker f) := by
      dsimp [g]
      rw [LinearMap.ker_comp]
    rw [h]
    ext x
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.mem_inf]
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  have hker_finrank : Module.finrank K ↥(LinearMap.ker g) =
      Module.finrank K ↥(S ⊓ LinearMap.ker f) := by
    rw [hker_eq]
    exact LinearEquiv.finrank_eq
      (Submodule.comapSubtypeEquivOfLe (p := S ⊓ LinearMap.ker f) (q := S) inf_le_left)
  have hrange_eq : LinearMap.range g = Submodule.map f S := by
    dsimp [g]
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hranknullity := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange_eq, hker_finrank] at hranknullity
  exact Nat.eq_sub_of_add_eq hranknullity

end Commons.LinearAlgebra