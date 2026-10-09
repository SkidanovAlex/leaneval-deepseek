import Mathlib
import Submission.NK.CFTLib.HR.TransferAux.Setup
import Submission.NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# `H¹(Gal(E/M), Eˣ) = 0` for the units of a Galois level

This file records the vanishing of the first cohomology of the units `Eˣ` of a finite Galois
extension `E/K` of number fields, restricted to the subgroup `Gal(E/M) = ker (Gal(E/K) → Gal(M/K))`
for an intermediate Galois extension `M/K`.  It is Noether's generalisation of Hilbert's
Theorem 90, transported from Mathlib's statement for `Gal(E/M)` along the identification
`Gal(E/M) ≅ ker (restrictNormalHom : Gal(E/K) →* Gal(M/K))`.

The main result is `NK.CFTLib.HR.TransferAux.h1ResUnits`.
-/

set_option maxHeartbeats 1600000
set_option linter.style.haveILetI false
set_option autoImplicit false

open CategoryTheory

namespace NK.CFTLib.HR.TransferAux

section GroupIso

variable {K M E : Type} [Field K] [Field M] [Field E] [Algebra K M] [Algebra K E]
    [Algebra M E] [IsScalarTower K M E] [Normal K M]

/-- An element of `Gal(E/K)` fixing the image of `M` pointwise, viewed as an `M`-algebra
automorphism of `E`. -/
noncomputable def fixEquivOfFixes (σ : E ≃ₐ[K] E)
    (hσ : ∀ m : M, σ (algebraMap M E m) = algebraMap M E m) : E ≃ₐ[M] E :=
  AlgEquiv.ofBijective
    { toFun := σ
      map_one' := map_one σ
      map_mul' := map_mul σ
      map_zero' := map_zero σ
      map_add' := map_add σ
      commutes' := hσ }
    ⟨σ.injective, σ.surjective⟩

/-- An element of the kernel of `restrictNormalHom : Gal(E/K) →* Gal(M/K)` fixes the image of `M`
in `E` pointwise. -/
lemma fixes_of_mem_rN (σ : E ≃ₐ[K] E) (hσ : σ ∈ rN K M E) :
    ∀ m : M, σ (algebraMap M E m) = algebraMap M E m := by
  intro m
  have h1 : σ.restrictNormal M = 1 := hσ
  have h2 := AlgEquiv.restrictNormal_commutes (F := K) (χ := σ) (E := M) m
  rw [h1] at h2
  simpa using h2.symm

/-- An `M`-algebra automorphism of `E`, viewed as a `K`-algebra automorphism, lies in
`ker (restrictNormalHom : Gal(E/K) →* Gal(M/K))`. -/
lemma restrictScalars_mem_rN (τ : E ≃ₐ[M] E) :
    AlgEquiv.restrictScalarsHom K τ ∈ rN K M E := by
  rw [rN, MonoidHom.mem_ker]
  rw [show (AlgEquiv.restrictNormalHom (F := K) (K₁ := E) (E := M))
        (AlgEquiv.restrictScalarsHom K τ)
      = (AlgEquiv.restrictScalars K τ).restrictNormal M from rfl]
  ext m
  apply (algebraMap M E).injective
  rw [AlgEquiv.restrictNormal_commutes (F := K) (χ := AlgEquiv.restrictScalars K τ)
      (K₁ := E) (K₂ := E) (E := M) m, AlgEquiv.coe_restrictScalars, AlgEquiv.commutes]
  rfl

/-- **The Galois group of `E` over the image of `M` is the kernel of the restriction map
`Gal(E/K) →* Gal(M/K)`.** -/
noncomputable def rNEquiv : (E ≃ₐ[M] E) ≃* ↥(rN K M E) where
  toFun τ := ⟨AlgEquiv.restrictScalarsHom K τ, restrictScalars_mem_rN τ⟩
  invFun γ := fixEquivOfFixes γ.1 (fixes_of_mem_rN γ.1 γ.2)
  left_inv τ := by ext x; rfl
  right_inv γ := by ext x; rfl
  map_mul' τ υ := by ext x; rfl

/-- The action of `Gal(E/K)` on the units `Eˣ` of `E`, written additively. -/
lemma urep_rho_apply (σ : E ≃ₐ[K] E) (y : Additive Eˣ) :
    (NK.CFTLib.IdeleHasse.Crux.urep K E).ρ σ y
      = Additive.ofMul (σ • Additive.toMul y) := rfl

/-- The action of `Gal(E/M)` on the units `Eˣ` of `E`, written additively. -/
lemma urep_rho_apply_M (τ : E ≃ₐ[M] E) (y : Additive Eˣ) :
    (NK.CFTLib.IdeleHasse.Crux.urep M E).ρ τ y
      = Additive.ofMul (τ • Additive.toMul y) := rfl

/-- **The key computation of the actions**: on the units `Eˣ`, the action of `γ ∈ Gal(E/K)` lying
in `ker (restrictNormalHom : Gal(E/K) →* Gal(M/K))` agrees with the action of the corresponding
element of `Gal(E/M)`. -/
lemma res_rho_eq_units (γ : ↥(rN K M E))
    (x : (Rep.res (rN K M E).subtype (NK.CFTLib.IdeleHasse.Crux.urep K E)).V) :
    (Rep.res (rN K M E).subtype (NK.CFTLib.IdeleHasse.Crux.urep K E)).ρ γ x
      = (NK.CFTLib.IdeleHasse.Crux.urep M E).ρ
          ((rNEquiv (K:=K) (M:=M) (E:=E)).symm γ) x := by
  change (NK.CFTLib.IdeleHasse.Crux.urep K E).ρ (γ : E ≃ₐ[K] E) (show Additive Eˣ from x)
    = (NK.CFTLib.IdeleHasse.Crux.urep M E).ρ
        ((rNEquiv (K:=K) (M:=M) (E:=E)).symm γ) (show Additive Eˣ from x)
  rw [urep_rho_apply, urep_rho_apply_M]
  congr 1

end GroupIso

/-- **Noether's generalisation of Hilbert's Theorem 90 for the subgroup `Gal(E/M)`**: for a tower
`K ⊆ M ⊆ E` of finite Galois extensions of number fields, the first cohomology of the units `Eˣ`
with coefficients in the `Gal(E/K)`-representation restricted to
`ker (restrictNormalHom : Gal(E/K) →* Gal(M/K)) = Gal(E/M)` vanishes. -/
theorem h1ResUnits {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M]
    [Field E] [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E]
    [FiniteDimensional K M] [FiniteDimensional K E] [FiniteDimensional M E]
    [IsGalois K M] [IsGalois K E] :
    Subsingleton (groupCohomology
      (Rep.res (NK.CFTLib.HR.TransferAux.rN K M E).subtype
        (NK.CFTLib.IdeleHasse.Crux.urep K E)) 1) := by
  -- `E/M` is again Galois, so Mathlib's Hilbert 90 applies to the extension `E/M`
  haveI hME : IsGalois M E := IsGalois.tower_top_of_isGalois K M E
  haveI hA : Subsingleton (groupCohomology (NK.CFTLib.IdeleHasse.Crux.urep M E) 1) :=
    NK.HassePrinciple.subsingleton_groupCohomology_one_unitsRep
  -- the identity identification of the coefficient modules `Eˣ` of the two representations
  let e' : (Rep.res (rN K M E).subtype (NK.CFTLib.IdeleHasse.Crux.urep K E)).V ≃ₗ[NK.HassePrinciple.CoeffInt]
      (NK.CFTLib.IdeleHasse.Crux.urep M E).V := LinearEquiv.refl _ _
  have he : ∀ γ : ↥(rN K M E),
      (e' : (Rep.res (rN K M E).subtype (NK.CFTLib.IdeleHasse.Crux.urep K E)).V →ₗ[NK.HassePrinciple.CoeffInt]
          (NK.CFTLib.IdeleHasse.Crux.urep M E).V) ∘ₗ
        (Rep.res (rN K M E).subtype (NK.CFTLib.IdeleHasse.Crux.urep K E)).ρ γ
      = (NK.CFTLib.IdeleHasse.Crux.urep M E).ρ ((rNEquiv (K:=K) (M:=M) (E:=E)).symm γ) ∘ₗ
        (e' : (Rep.res (rN K M E).subtype (NK.CFTLib.IdeleHasse.Crux.urep K E)).V →ₗ[NK.HassePrinciple.CoeffInt]
          (NK.CFTLib.IdeleHasse.Crux.urep M E).V) := by
    intro γ
    apply LinearMap.ext
    intro x
    exact res_rho_eq_units γ x
  -- transport the vanishing of `H¹(Gal(E/M), Eˣ)` along `rNEquiv`
  have hmap := groupCohomology.mapIso
    (A := NK.CFTLib.IdeleHasse.Crux.urep M E)
    (B := Rep.res (rN K M E).subtype (NK.CFTLib.IdeleHasse.Crux.urep K E))
    (rNEquiv (K:=K) (M:=M) (E:=E)).symm e' he 1
  refine ⟨fun a b => ?_⟩
  exact (ConcreteCategory.bijective_of_isIso hmap.hom).1
    (Subsingleton.elim (hmap.hom a) (hmap.hom b))

end NK.CFTLib.HR.TransferAux
