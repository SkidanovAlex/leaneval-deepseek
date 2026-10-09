import Mathlib
import Submission.NK.CFTLib.HR.TransferAux.Setup
import Submission.NK.CFTLib.HR.TransferAux.h1ResUnits
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

open NK.GlobalCFT CategoryTheory

namespace NK.CFTLib.HR.TransferAux

open IsDedekindDomain IdeleHasse

attribute [local instance 5000] Rep.hV1 Rep.hV2

lemma exists_units_map_eq_of_fixed {M E : Type} [Field M] [Field E] [Algebra M E]
    [FiniteDimensional M E] [IsGalois M E] (u : Eˣ)
    (hu : ∀ τ : E ≃ₐ[M] E, τ (u : E) = (u : E)) :
    ∃ m : Mˣ, Units.map (algebraMap M E).toMonoidHom m = u := by
  obtain ⟨m, hm⟩ := (IsGalois.mem_range_algebraMap_iff_fixed (F := M) (E := E) (u : E)).mpr hu
  refine ⟨Units.mk0 m ?_, ?_⟩
  · intro h0
    rw [h0, map_zero] at hm
    exact u.ne_zero hm.symm
  · ext
    simp only [Units.coe_map, Units.val_mk0]
    exact hm

section Main

variable {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M]
    [Field E] [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E]
    [FiniteDimensional K M] [FiniteDimensional K E] [FiniteDimensional M E]
    [IsGalois K M] [IsGalois K E]

noncomputable def unitsIncl :
    Additive Mˣ →ₗ[NK.HassePrinciple.CoeffInt.{0}] Additive Eˣ :=
  unitsInclLinearMap K M E

lemma unitsIncl_apply (y : Additive Mˣ) :
    unitsIncl (K := K) (M := M) (E := E) y
      = Additive.ofMul (Units.map (algebraMap M E).toMonoidHom (Additive.toMul y)) := rfl

noncomputable def inclInv :
    Additive Mˣ →ₗ[NK.HassePrinciple.CoeffInt.{0}]
      ((NK.CFTLib.IdeleHasse.Crux.urep K E).quotientToInvariants (rN K M E)).V :=
  LinearMap.codRestrict _ (unitsIncl (K := K) (M := M) (E := E))
    (fun y => by
      rw [Representation.mem_invariants]
      intro g
      have hg : AlgEquiv.restrictNormalHom (K₁ := E) (E := M) (g : E ≃ₐ[K] E) = 1 := g.2
      have h := LinearMap.congr_fun ((unitsInclCoeff K M E).hom.isIntertwining' (g : E ≃ₐ[K] E)) y
      simp only [MonoidHom.comp_apply, hg, map_one] at h
      exact h.symm)

lemma inclInv_coe (y : Additive Mˣ) :
    (inclInv (K := K) (M := M) (E := E) y).1
      = unitsIncl (K := K) (M := M) (E := E) y := rfl

/-- The action of the quotient group on the invariants, on underlying elements. -/
lemma quot_apply_mk'_coe (g : E ≃ₐ[K] E)
    (x : ((NK.CFTLib.IdeleHasse.Crux.urep K E).quotientToInvariants (rN K M E)).V) :
    ((((NK.CFTLib.IdeleHasse.Crux.urep K E).quotientToInvariants (rN K M E)).ρ
        (QuotientGroup.mk' (rN K M E) g)) x).1
      = (NK.CFTLib.IdeleHasse.Crux.urep K E).ρ g x.1 := rfl

lemma inclInv_injective : Function.Injective (inclInv (K := K) (M := M) (E := E)) := by
  intro a b hab
  have h : unitsIncl (K := K) (M := M) (E := E) a
      = unitsIncl (K := K) (M := M) (E := E) b := congrArg Subtype.val hab
  rw [unitsIncl_apply, unitsIncl_apply] at h
  have h2 : Units.map (algebraMap M E).toMonoidHom ((Additive.toMul a : Mˣ))
      = Units.map (algebraMap M E).toMonoidHom ((Additive.toMul b : Mˣ)) :=
    Additive.ofMul.injective h
  have h3 : ((Additive.toMul a : Mˣ)) = ((Additive.toMul b : Mˣ)) :=
    Units.map_injective (RingHom.injective (algebraMap M E)) h2
  exact Additive.ext h3

lemma inclInv_surjective : Function.Surjective (inclInv (K := K) (M := M) (E := E)) := by
  have hgal : IsGalois M E := IsGalois.tower_top_of_isGalois K M E
  intro x
  have hfix : ∀ g : E ≃ₐ[K] E, g ∈ rN K M E →
      g • ((Additive.toMul x.1) : Eˣ) = (Additive.toMul x.1 : Eˣ) := by
    intro g hg
    have h2 : (NK.CFTLib.IdeleHasse.Crux.urep K E).ρ g x.1 = x.1 := x.2 ⟨g, hg⟩
    have h3 : Additive.ofMul (g • ((Additive.toMul x.1) : Eˣ))
        = Additive.ofMul ((Additive.toMul x.1) : Eˣ) := h2
    exact Additive.ofMul.injective h3
  have hfixM : ∀ τ : E ≃ₐ[M] E,
      τ (((Additive.toMul x.1) : Eˣ) : E) = (((Additive.toMul x.1) : Eˣ) : E) := by
    intro τ
    have h1 := hfix (AlgEquiv.restrictScalarsHom K τ) (restrictScalars_mem_rN (K := K) τ)
    have h2 := congrArg (fun v : Eˣ => (v : E)) h1
    simpa [AlgEquiv.coe_restrictScalars] using h2
  obtain ⟨m, hm⟩ := exists_units_map_eq_of_fixed (M := M) (E := E)
    (Additive.toMul x.1) hfixM
  refine ⟨Additive.ofMul m, ?_⟩
  apply Subtype.ext
  show unitsIncl (K := K) (M := M) (E := E) (Additive.ofMul m) = x.1
  rw [unitsIncl_apply, toMul_ofMul, hm]
  exact ofMul_toMul x.1

noncomputable def descentEquiv :
    Additive Mˣ ≃ₗ[NK.HassePrinciple.CoeffInt.{0}]
      ((NK.CFTLib.IdeleHasse.Crux.urep K E).quotientToInvariants (rN K M E)).V :=
  LinearEquiv.ofBijective (inclInv (K := K) (M := M) (E := E))
    ⟨inclInv_injective (K := K) (M := M) (E := E),
     inclInv_surjective (K := K) (M := M) (E := E)⟩

lemma descentEquiv_apply (y : Additive Mˣ) :
    descentEquiv (K := K) (M := M) (E := E) y
      = inclInv (K := K) (M := M) (E := E) y := rfl

lemma descentEquiv_equivar (σ : M ≃ₐ[K] M) (y : Additive Mˣ) :
    (Rep.res ((rQuot K M E).symm.toMonoidHom)
        ((NK.CFTLib.IdeleHasse.Crux.urep K E).quotientToInvariants (rN K M E))).ρ σ
        (descentEquiv (K := K) (M := M) (E := E) y)
      = descentEquiv (K := K) (M := M) (E := E)
          ((NK.CFTLib.IdeleHasse.Crux.urep K M).ρ σ y) := by
  obtain ⟨st, hst⟩ := AlgEquiv.restrictNormalHom_surjective (F := K) (K₁ := M) (E := E) σ
  have hsym : (rQuot K M E).symm σ = QuotientGroup.mk' (rN K M E) st := by
    have h := DFunLike.congr_fun (rQuot_symm_comp (K := K) (M := M) (E := E)) st
    simpa [hst] using h
  rw [descentEquiv_apply (K := K) (M := M) (E := E) y,
      descentEquiv_apply (K := K) (M := M) (E := E)
        ((NK.CFTLib.IdeleHasse.Crux.urep K M).ρ σ y)]
  apply Subtype.ext
  show ((((NK.CFTLib.IdeleHasse.Crux.urep K E).quotientToInvariants (rN K M E)).ρ
      ((rQuot K M E).symm σ)) (inclInv (K := K) (M := M) (E := E) y)).1
      = (inclInv (K := K) (M := M) (E := E)
          ((NK.CFTLib.IdeleHasse.Crux.urep K M).ρ σ y)).1
  rw [hsym, quot_apply_mk'_coe, inclInv_coe, inclInv_coe]
  have h := LinearMap.congr_fun ((unitsInclCoeff K M E).hom.isIntertwining' st) y
  simp only [MonoidHom.comp_apply, hst] at h
  exact h.symm

end Main

/-- **The descent morphism of the Brauer transfer**: the `Gal(M/K)`-equivariant identification of
the invariants of `Eˣ` under `Gal(E/M)` with the units `Mˣ`, as a morphism of representations. -/
theorem descentMorphism {K M E : Type} [Field K] [NumberField K] [Field M] [NumberField M]
    [Field E] [NumberField E] [Algebra K M] [Algebra K E] [Algebra M E] [IsScalarTower K M E]
    [FiniteDimensional K M] [FiniteDimensional K E] [FiniteDimensional M E]
    [IsGalois K M] [IsGalois K E] :
    ∃ P : Rep.res ((NK.CFTLib.HR.TransferAux.rQuot K M E).symm.toMonoidHom)
        ((NK.CFTLib.IdeleHasse.Crux.urep K E).quotientToInvariants
          (NK.CFTLib.HR.TransferAux.rN K M E)) ⟶
        (NK.CFTLib.IdeleHasse.Crux.urep K M),
      ∀ x : ((NK.CFTLib.IdeleHasse.Crux.urep K E).quotientToInvariants
          (NK.CFTLib.HR.TransferAux.rN K M E)).V,
        NK.CFTLib.HR.TransferAux.unitsInclLinearMap K M E (P.hom x) = x.1 := by
  refine ⟨Rep.ofHom { toLinearMap := (descentEquiv (K := K) (M := M) (E := E)).symm.toLinearMap,
                       isIntertwining' := ?_ }, ?_⟩
  · intro σ
    apply LinearMap.ext
    intro x
    show (descentEquiv (K := K) (M := M) (E := E)).symm
        ((Rep.res ((rQuot K M E).symm.toMonoidHom)
          ((NK.CFTLib.IdeleHasse.Crux.urep K E).quotientToInvariants (rN K M E))).ρ σ x)
      = (NK.CFTLib.IdeleHasse.Crux.urep K M).ρ σ
          ((descentEquiv (K := K) (M := M) (E := E)).symm x)
    rw [LinearEquiv.symm_apply_eq]
    conv_lhs => rw [← LinearEquiv.apply_symm_apply (descentEquiv (K := K) (M := M) (E := E)) x]
    exact descentEquiv_equivar (K := K) (M := M) (E := E) σ
      ((descentEquiv (K := K) (M := M) (E := E)).symm x)
  · intro x
    have h : inclInv (K := K) (M := M) (E := E)
        ((descentEquiv (K := K) (M := M) (E := E)).symm x) = x := by
      rw [← descentEquiv_apply]
      exact LinearEquiv.apply_symm_apply _ x
    show unitsIncl (K := K) (M := M) (E := E)
        ((descentEquiv (K := K) (M := M) (E := E)).symm x) = x.1
    rw [← inclInv_coe]
    exact congrArg Subtype.val h

end NK.CFTLib.HR.TransferAux
