import Mathlib
set_option linter.style.haveILetI false

namespace NK.Reconstruct

/-- If `φ : K →ₐ[k] L` is a `k`-algebra homomorphism into a separably closed field `L` and `L`
is separable over `k`, then `L` is a separable closure of `K` for the algebra structure induced
by `φ`. -/
theorem isSepClosure_of_algHom {k K L : Type*} [Field k] [Field K] [Field L] [Algebra k K]
    [Algebra k L] [IsSepClosed L] (φ : K →ₐ[k] L) [Algebra.IsSeparable k L] :
    @IsSepClosure K _ L _ φ.toRingHom.toAlgebra := by
  letI : Algebra K L := φ.toRingHom.toAlgebra
  haveI : IsScalarTower k K L :=
    IsScalarTower.of_algebraMap_eq (fun x => (φ.commutes x).symm)
  exact ⟨inferInstance, Algebra.isSeparable_tower_top_of_isSeparable k K L⟩

theorem exists_algebra_isSepClosure {K₂ K₁' : Type*} [Field K₂] [NumberField K₂] [Field K₁']
    [Algebra ℚ K₁'] [IsSepClosed K₁'] (halg : Algebra.IsAlgebraic ℚ K₁') :
    ∃ (ι : K₂ →ₐ[ℚ] K₁'), @IsSepClosure K₂ _ K₁' _ ι.toRingHom.toAlgebra := by
  haveI hsep : Algebra.IsSeparable ℚ K₁' := halg.isSeparable_of_perfectField
  exact ⟨(IsSepClosed.lift : K₂ →ₐ[ℚ] K₁'), isSepClosure_of_algHom _⟩

end NK.Reconstruct
