import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

namespace Commons.LinearAlgebra.Dimension

open Module

/-- **Dimension of the image of a finite-dimensional subspace.**

For a linear map `f : V →ₗ[K] W` and a finite-dimensional subspace `p ≤ V`, the image
`Submodule.map f p` has dimension `finrank p - finrank (p ⊓ ker f)`.

Proof: restrict `f` to `p`.  The resulting map `g : p →ₗ[K] W` has range `Submodule.map f p`
and kernel `p ⊓ ker f` (viewed inside `p`), so rank–nullity applied to the finite-dimensional
domain `p` gives `finrank (map f p) + finrank (p ⊓ ker f) = finrank p`. -/
theorem finrank_map_eq_finrank_sub_finrank_inf_ker {K V W : Type*} [Field K] [AddCommGroup V]
    [Module K V] [AddCommGroup W] [Module K W] (f : V →ₗ[K] W) (p : Submodule K V)
    [FiniteDimensional K ↥p] :
    Module.finrank K ↥(Submodule.map f p)
      = Module.finrank K ↥p - Module.finrank K ↥(p ⊓ LinearMap.ker f) := by
  classical
  let g : p →ₗ[K] W := f.comp p.subtype
  have hker_eq : LinearMap.ker g = Submodule.comap p.subtype (p ⊓ LinearMap.ker f) := by
    have h : LinearMap.ker g = Submodule.comap p.subtype (LinearMap.ker f) := by
      dsimp [g]
      rw [LinearMap.ker_comp]
    rw [h]
    ext x
    rw [Submodule.mem_comap, Submodule.mem_comap, Submodule.mem_inf]
    exact ⟨fun hx => ⟨x.2, hx⟩, fun hx => hx.2⟩
  have hker_finrank : Module.finrank K ↥(LinearMap.ker g) =
      Module.finrank K ↥(p ⊓ LinearMap.ker f) := by
    rw [hker_eq]
    exact LinearEquiv.finrank_eq
      (Submodule.comapSubtypeEquivOfLe (p := p ⊓ LinearMap.ker f) (q := p) inf_le_left)
  have hrange_eq : LinearMap.range g = Submodule.map f p := by
    dsimp [g]
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hranknullity := LinearMap.finrank_range_add_finrank_ker g
  rw [hrange_eq, hker_finrank] at hranknullity
  exact Nat.eq_sub_of_add_eq hranknullity

end Commons.LinearAlgebra.Dimension