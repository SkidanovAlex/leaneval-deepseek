import Mathlib.NumberTheory.NumberField.Basic
import Mathlib.RepresentationTheory.Homological.GroupCohomology.LowDegree
import Submission.Work.SSGRoute.E0bDefs
import Submission.Work.SSGRoute.SSGStage.exists_regularModule_inert_level
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

namespace Work.SSGRoute.SSGStage

/-- **The group-theoretic identity behind the `1`-cocycle `γ ↦ φ (coordKer γ)`.**

For a section `s` of `galRes k K ↥L`, the `N`-coordinate `coordKer γ = γ * (s (galRes γ))⁻¹`
satisfies
`coordKer (g * h) = coordKer g * (s (galRes g) * coordKer h * (s (galRes g))⁻¹)`.

This is a purely formal consequence of `galRes` and `s` being monoid homs (no use of `hs`):
both sides equal `g * h * (s (galRes h))⁻¹ * (s (galRes g))⁻¹`. -/
theorem coordKer_mul (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
    (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ)
    (g h : ↥L ≃ₐ[k] ↥L) :
    coordKer k K Ω L s hs (g * h)
      = coordKer k K Ω L s hs g *
        ⟨s (SSGRoute.PTExt.galRes k K ↥L g) *
            (coordKer k K Ω L s hs h : ↥L ≃ₐ[k] ↥L) *
            (s (SSGRoute.PTExt.galRes k K ↥L g))⁻¹,
          ker_galRes_conj_mem p k K Ω L (s (SSGRoute.PTExt.galRes k K ↥L g))
            (coordKer k K Ω L s hs h)⟩ := by
  apply Subtype.ext
  simp only [coordKer_coe, Subgroup.coe_mul]
  rw [map_mul, map_mul, mul_inv_rev]
  group

theorem mem_cocycles_coordKer (p : ℕ) [Fact p.Prime] (k K : Type) [Field k] [NumberField k]
    [Field K] [NumberField K] [Algebra k K] [FiniteDimensional k K] [IsGalois k K]
    (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] [Algebra k Ω] [IsScalarTower k K Ω]
    (L : IntermediateField K Ω) [NumberField ↥L] [FiniteDimensional k ↥L] [IsGalois k ↥L]
    (M : Rep.{0} SSGRoute.PTExt.Coeff (K ≃ₐ[k] K))
    (s : (K ≃ₐ[k] K) →* (↥L ≃ₐ[k] ↥L))
    (hs : ∀ σ : K ≃ₐ[k] K, SSGRoute.PTExt.galRes k K ↥L (s σ) = σ)
    (φ : Additive ((SSGRoute.PTExt.galRes k K ↥L).ker) →+ M.V)
    (hφ : ∀ (σ : ↥L ≃ₐ[k] ↥L) (g : (SSGRoute.PTExt.galRes k K ↥L).ker),
      φ (Additive.ofMul ⟨σ * (g : ↥L ≃ₐ[k] ↥L) * σ⁻¹,
          ker_galRes_conj_mem p k K Ω L σ g⟩)
        = M.ρ (SSGRoute.PTExt.galRes k K ↥L σ) (φ (Additive.ofMul g))) :
    (fun γ : ↥L ≃ₐ[k] ↥L => φ (Additive.ofMul (coordKer k K Ω L s hs γ)))
      ∈ groupCohomology.cocycles₁ (Rep.res (SSGRoute.PTExt.galRes k K ↥L) M) := by
  rw [groupCohomology.mem_cocycles₁_iff]
  intro g h
  show φ (Additive.ofMul (coordKer k K Ω L s hs (g * h))) =
      M.ρ (SSGRoute.PTExt.galRes k K ↥L g) (φ (Additive.ofMul (coordKer k K Ω L s hs h))) +
        φ (Additive.ofMul (coordKer k K Ω L s hs g))
  rw [coordKer_mul p k K Ω L s hs g h]
  have h1 : Additive.ofMul (coordKer k K Ω L s hs g *
        ⟨s (SSGRoute.PTExt.galRes k K ↥L g) *
            (coordKer k K Ω L s hs h : ↥L ≃ₐ[k] ↥L) *
            (s (SSGRoute.PTExt.galRes k K ↥L g))⁻¹,
          ker_galRes_conj_mem p k K Ω L (s (SSGRoute.PTExt.galRes k K ↥L g))
            (coordKer k K Ω L s hs h)⟩)
      = Additive.ofMul (coordKer k K Ω L s hs g) +
        Additive.ofMul (⟨s (SSGRoute.PTExt.galRes k K ↥L g) *
            (coordKer k K Ω L s hs h : ↥L ≃ₐ[k] ↥L) *
            (s (SSGRoute.PTExt.galRes k K ↥L g))⁻¹,
          ker_galRes_conj_mem p k K Ω L (s (SSGRoute.PTExt.galRes k K ↥L g))
            (coordKer k K Ω L s hs h)⟩) := rfl
  rw [h1, map_add, hφ (s (SSGRoute.PTExt.galRes k K ↥L g)) (coordKer k K Ω L s hs h),
      hs (SSGRoute.PTExt.galRes k K ↥L g)]
  exact add_comm _ _

end Work.SSGRoute.SSGStage
