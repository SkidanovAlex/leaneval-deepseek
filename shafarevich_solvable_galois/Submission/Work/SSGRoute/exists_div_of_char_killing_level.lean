import Mathlib
import Submission.Work.SSGRoute.Interfaces
import Submission.Work.SSGRoute.exists_character_lift_of_fixingSubgroup_le_ker
import Submission.Work.SSGRoute.exists_unit_div_eq_of_character
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute

/-- **Finite-level Kummer/Hilbert 90 for a character of `Gal(ℚ̄/↥F)` over a normal subextension.**

Let `F : IntermediateField ℚ ℚ̄`, let `M` be a finite-dimensional normal intermediate field of
`ℚ̄` over `↥F`, and let `ω : Gal(ℚ̄/↥F) →* (↥F)ˣ` be a character with values in the units of the
base field which kills the fixing subgroup of `M`. Then `ω` is a coboundary: there is `θ ≠ 0` in
`ℚ̄` with `σ θ / θ = ω σ` (viewed in `ℚ̄`) for all `σ : Gal(ℚ̄/↥F)`.

Proof sketch: the restriction `AlgEquiv.restrictNormalHom (F := ↥F) (K₁ := ℚ̄) ↥M` is surjective
(`AlgEquiv.restrictNormalHom_surjective`, using `Normal ↥F ↥M` and `Normal ↥F ℚ̄`; the latter is
not a typeclass instance, add `haveI : IsAlgClosure ↥F ℚ̄` from `Algebra.IsAlgebraic` and then use
`IsAlgClosure.normal`) with kernel `M.fixingSubgroup`
(`IntermediateField.restrictNormalHom_ker`); hence `ω` descends to a monoid homomorphism
`d : Gal(M/↥F) →* (↥F)ˣ` given by `d τ = ω σ` for any lift `σ` of `τ` (well defined by the
hypothesis `hω`). Finite Hilbert 90 in the form
`Work.SSGRoute.exists_unit_div_eq_of_character` (applied with `U := ↥F`, `M := ↥M`) produces
`β : (↥M)ˣ` with `τ β / β = algebraMap ↥F ↥M (d τ)` for all `τ`. Then `θ := (β : ↥M)` coerced to
`ℚ̄` is nonzero, and for `σ : Gal(ℚ̄/↥F)` with restriction
`τ := AlgEquiv.restrictNormalHom ↥M σ` one has `σ θ = algebraMap ↥M ℚ̄ (τ β)`
(`AlgEquiv.restrictNormal_commutes`), whence
`σ θ / θ = algebraMap ↥M ℚ̄ (τ β / β) = algebraMap ↥F ℚ̄ (d τ) = algebraMap ↥F ℚ̄ (ω σ)`. -/
theorem exists_div_of_char_killing_level
    (F : IntermediateField ℚ SSGRoute.QBar) (M : IntermediateField ↥F SSGRoute.QBar)
    [FiniteDimensional ↥F M] [Normal ↥F M]
    (ω : (SSGRoute.QBar ≃ₐ[↥F] SSGRoute.QBar) →* (↥F)ˣ)
    (hω : ∀ σ : SSGRoute.QBar ≃ₐ[↥F] SSGRoute.QBar, σ ∈ M.fixingSubgroup → ω σ = 1) :
    ∃ θ : SSGRoute.QBar, θ ≠ 0 ∧ ∀ σ : SSGRoute.QBar ≃ₐ[↥F] SSGRoute.QBar,
      σ θ / θ = algebraMap ↥F SSGRoute.QBar ((ω σ : (↥F)ˣ) : ↥F) := by
  classical
  -- `ℚ̄` is an algebraic closure of `↥F`; the instance is not found automatically.
  haveI hACQ : IsAlgClosure ℚ SSGRoute.QBar := AlgebraicClosure.instIsAlgClosure ℚ
  haveI hAlgF : Algebra.IsAlgebraic ↥F SSGRoute.QBar := inferInstance
  haveI hACF : IsAlgClosure ↥F SSGRoute.QBar := ⟨inferInstance, hAlgF⟩
  haveI hNormQ : Normal ↥F SSGRoute.QBar := IsAlgClosure.normal ↥F SSGRoute.QBar
  -- The character descends to `Gal(M/↥F)`.
  have hle : M.fixingSubgroup ≤ ω.ker := fun σ hσ => by
    rw [MonoidHom.mem_ker]; exact hω σ hσ
  obtain ⟨d, hd⟩ :=
    exists_character_lift_of_fixingSubgroup_le_ker (U := ↥F) (L := SSGRoute.QBar) M ω hle
  -- Hilbert 90 in the finite extension `M/↥F`.
  obtain ⟨β, hβ⟩ := exists_unit_div_eq_of_character (U := ↥F) (M := ↥M) d
  have hθ0 : algebraMap ↥M SSGRoute.QBar (β : ↥M) ≠ 0 :=
    (algebraMap ↥M SSGRoute.QBar).injective.ne (Units.ne_zero β)
  refine ⟨algebraMap ↥M SSGRoute.QBar (β : ↥M), hθ0, fun σ => ?_⟩
  set χ : ↥M ≃ₐ[↥F] ↥M :=
    AlgEquiv.restrictNormalHom (F := ↥F) (K₁ := SSGRoute.QBar) ↥M σ with hχdef
  have hdχ : d χ = ω σ := by rw [hχdef]; exact hd σ
  have hχβ : χ (β : ↥M)
      = algebraMap ↥F ↥M (((ω σ : (↥F)ˣ) : ↥F)) * (β : ↥M) := by
    have h := hβ χ
    rw [div_eq_iff (Units.ne_zero β)] at h
    rw [h, hdχ]
  have hσθ : σ (algebraMap ↥M SSGRoute.QBar (β : ↥M))
      = algebraMap ↥M SSGRoute.QBar (χ (β : ↥M)) := by
    rw [hχdef]
    exact (AlgEquiv.restrictNormalHom_apply (K₁ := SSGRoute.QBar) M σ (β : ↥M)).symm
  rw [hσθ, hχβ, map_mul, ← IsScalarTower.algebraMap_apply ↥F ↥M SSGRoute.QBar]
  rw [mul_div_cancel_right₀ _ hθ0]

end Work.SSGRoute
