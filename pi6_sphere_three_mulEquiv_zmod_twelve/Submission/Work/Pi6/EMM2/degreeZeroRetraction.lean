import Mathlib
import Submission.Work.SSS.expTensHomologyZero
set_option backward.isDefEq.respectTransparency false  -- v435port
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false  -- v435port
set_option backward.isDefEq.respectTransparency.types false  -- v435port

/-!
# The boundaries in degree zero are a direct summand when `H_0` is free

`Work.Pi6.EMM2.degreeZeroRetraction` provides the retraction of `K_0` onto its boundaries
`B_0 = im (d_1 : K_1 → K_0)` that is used in the degree-one case of the universal coefficient
argument `Work.Pi6.EMM2.coeffVanishing`: it makes `B_0 ⊗ M → K_0 ⊗ M` injective for every
coefficient module `M`.

`H_0(K) ≅ cokernel (d_1) ≅ K_0 ⧸ B_0` and `H_0(K)` is free, hence projective, so the quotient
`K_0 ⧸ B_0` is projective and the surjection `K_0 ↠ K_0 ⧸ B_0` splits; a section `i` of it gives
the retraction `ρ = id - i ∘ mkQ` of `K_0` onto `ker mkQ = B_0`.
-/

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] Submodule.module
attribute [-instance] AddCommGroup.toIntModule

namespace Work.Pi6.EMM2

/-- If `H_0(K)` is free then the inclusion of the boundaries `B_0 = im d_1 ⊆ K_0` has a retraction,
i.e. `B_0` is a direct summand of `K_0`. -/
theorem degreeZeroRetraction (K : ChainComplex (ModuleCat.{0} ℤ) ℕ)
    (h0 : Module.Free ℤ ↥(K.homology 0)) :
    ∃ ρ : ↥(K.X 0) →ₗ[ℤ] ↥(LinearMap.range (K.d 1 0).hom),
      ρ ∘ₗ (LinearMap.range (K.d 1 0).hom).subtype = LinearMap.id := by
  haveI : Module.Projective ℤ ↥(K.homology 0) := Module.Projective.of_free
  have e : K.homology 0 ≅ ModuleCat.of ℤ (↥(K.X 0) ⧸ LinearMap.range (K.d 1 0).hom) :=
    ChainComplex.isoHomologyι₀ K ≪≫ Work.SSS.opcyclesZeroIsoCokernel K ≪≫
      ModuleCat.cokernelIsoRangeQuotient (K.d 1 0)
  haveI : Module.Projective ℤ (↥(K.X 0) ⧸ LinearMap.range (K.d 1 0).hom) :=
    Module.Projective.of_equiv' (Iso.toLinearEquiv e)
  set p : Submodule ℤ ↥(K.X 0) := LinearMap.range (K.d 1 0).hom
  obtain ⟨i, hi⟩ := Module.projective_lifting_property p.mkQ
    (LinearMap.id : (↥(K.X 0) ⧸ p) →ₗ[ℤ] (↥(K.X 0) ⧸ p)) p.mkQ_surjective
  have hi' : ∀ x : ↥(K.X 0) ⧸ p, p.mkQ (i x) = x := fun x => LinearMap.congr_fun hi x
  have hmem : ∀ x : ↥(K.X 0),
      ((LinearMap.id : ↥(K.X 0) →ₗ[ℤ] ↥(K.X 0)) - i.comp p.mkQ) x ∈ p := by
    intro x
    have h1 : p.mkQ (((LinearMap.id : ↥(K.X 0) →ₗ[ℤ] ↥(K.X 0)) - i.comp p.mkQ) x) = 0 := by
      rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, map_sub,
        hi' (p.mkQ x), sub_self]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h1
    exact h1
  refine ⟨LinearMap.codRestrict p
    ((LinearMap.id : ↥(K.X 0) →ₗ[ℤ] ↥(K.X 0)) - i.comp p.mkQ) hmem, ?_⟩
  ext x
  have hx : p.mkQ (p.subtype x) = 0 := by
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact x.2
  show ((LinearMap.id : ↥(K.X 0) →ₗ[ℤ] ↥(K.X 0)) - i.comp p.mkQ) (p.subtype x)
      = (x : ↥(K.X 0))
  rw [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.comp_apply, hx, map_zero, sub_zero]
  exact Submodule.subtype_apply x

end Work.Pi6.EMM2
