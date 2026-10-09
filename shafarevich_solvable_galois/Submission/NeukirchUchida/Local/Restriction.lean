import Submission.NeukirchUchida.Local.PlaceUnder
import Submission.Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction of decomposition groups to intermediate fields

Let `M / K` be a finite Galois extension of number fields and `L` an intermediate field (normal
over `K`).  A finite place `w` of `M` restricts to a finite place `w|_L` of `L`
(`Submission.NeukirchUchida.Local.placeUnder`), and the decomposition group of `w` maps into the
decomposition group of `w|_L` under the restriction homomorphism `Gal(M/K) →* Gal(L/K)`.

This is the compatibility that turns the decomposition groups of a tower of number fields into a
projective system, whose limit is the decomposition group of a place of a separable closure
(compare `Submission.NeukirchUchida.Local.InfiniteDecomposition`).

The main results are

* `galRestrict_restrictNormalHom` : the action of `σ` on `𝓞 M` restricts to the action of `σ|_L`
  on `𝓞 L`;
* `restrictNormalHom_mem_decompositionSubgroup` : `σ ∈ D_w → σ|_L ∈ D_{w|_L}`.
-/

open scoped NumberField

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

namespace Submission.NeukirchUchida.Local

/-! ## The action on the rings of integers -/

section RingOfIntegers

variable {K M : Type*} [Field K] [Field M] [NumberField K] [NumberField M] [Algebra K M]
  [FiniteDimensional K M] [IsGalois K M]

/-- **Compatibility of `galRestrict` with restriction to an intermediate field**, evaluated in
`M`. -/
theorem algebraMap_galRestrict_restrictNormalHom (L : IntermediateField K M) [Normal K L]
    (σ : Gal(M/K)) (x : 𝓞 L) :
    algebraMap (𝓞 M) M (algebraMap (𝓞 L) (𝓞 M) ((galRestrict (𝓞 K) K ↥L (𝓞 ↥L)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ)) x)) =
      algebraMap (𝓞 M) M (galRestrict (𝓞 K) K M (𝓞 M) σ
        (algebraMap (𝓞 L) (𝓞 M) x)) := by
  conv_lhs => rw [← IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 M) M]
  conv_rhs => rw [algebraMap_galRestrict_apply]
  conv_lhs => rw [IsScalarTower.algebraMap_apply (𝓞 L) ↥L M]
  conv_lhs => rw [algebraMap_galRestrict_apply]
  conv_lhs => rw [show (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ) =
      σ.restrictNormal ↥L from rfl]
  conv_lhs => rw [AlgEquiv.restrictNormal_commutes]
  conv_rhs => rw [← IsScalarTower.algebraMap_apply (𝓞 L) (𝓞 M) M]
  conv_rhs => rw [IsScalarTower.algebraMap_apply (𝓞 L) ↥L M]

/-- **Compatibility of `galRestrict` with restriction to an intermediate field.**  The element of
`𝓞 M` obtained by applying the automorphism induced by `σ` to an element of `𝓞 L` only depends on
the restriction `σ|_L` of `σ` to `L`. -/
theorem galRestrict_restrictNormalHom (L : IntermediateField K M) [Normal K L]
    (σ : Gal(M/K)) (x : 𝓞 L) :
    algebraMap (𝓞 L) (𝓞 M) ((galRestrict (𝓞 K) K ↥L (𝓞 ↥L)
        (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ)) x) =
      galRestrict (𝓞 K) K M (𝓞 M) σ (algebraMap (𝓞 L) (𝓞 M) x) := by
  refine Subtype.ext ?_
  exact algebraMap_galRestrict_restrictNormalHom L σ x

end RingOfIntegers

/-! ## A general computation with `Ideal.comap` -/

section IdealComap

/-- **A general computation with `Ideal.comap` and `Ideal.map`.**  Let `φ` be a ring automorphism
of `A`, `χ` a ring automorphism of `B`, `ψ : A →+* B` a ring homomorphism with `ψ φ = χ ψ`, and
`P` a `χ`-stable ideal of `B`.  Then `φ` stabilises the contraction of `P` along `ψ`. -/
theorem Ideal.map_comap_eq_of_comp_eq {A B : Type*} [CommRing A] [CommRing B]
    (φ : A ≃+* A) (ψ : A →+* B) (χ : B ≃+* B) (P : Ideal B)
    (hcomp : ∀ x, ψ ((φ : A →+* A) x) = (χ : B →+* B) (ψ x))
    (hP : Ideal.map (χ : B →+* B) P = P) :
    Ideal.map (φ : A →+* A) (Ideal.comap ψ P) = Ideal.comap ψ P := by
  have hPsymm : Ideal.map (χ.symm : B →+* B) P = P := by
    have h := congrArg (Ideal.map (χ.symm : B →+* B)) hP
    rw [Ideal.map_map] at h
    rw [show (χ.symm : B →+* B).comp (χ : B →+* B) = RingHom.id _ from by
      ext z; simp] at h
    simpa using h.symm
  have hmem : ∀ y : B, (χ : B →+* B) y ∈ P ↔ y ∈ P := fun y =>
    ⟨fun hy => by
        have h2 : χ.symm ((χ : B →+* B) y) ∈ Ideal.map (χ.symm : B →+* B) P :=
          Ideal.mem_map_of_mem _ hy
        rw [hPsymm] at h2
        simpa using h2,
      fun hy => by
        have h2 := Ideal.mem_map_of_mem (χ : B →+* B) hy
        rwa [hP] at h2⟩
  have hmem' : ∀ y : B, (χ.symm : B →+* B) y ∈ P ↔ y ∈ P := fun y =>
    ⟨fun hy => by
        have h2 : χ ((χ.symm : B →+* B) y) ∈ Ideal.map (χ : B →+* B) P :=
          Ideal.mem_map_of_mem _ hy
        rw [hP] at h2
        simpa using h2,
      fun hy => by
        have h2 := Ideal.mem_map_of_mem (χ.symm : B →+* B) hy
        rwa [hPsymm] at h2⟩
  have hcomp' : ∀ x, ψ (((φ.symm : A ≃+* A) : A →+* A) x) =
      ((χ.symm : B ≃+* B) : B →+* B) (ψ x) := fun x => by
    have h := hcomp ((φ.symm : A ≃+* A) x)
    have h2 : ψ x = (χ : B →+* B) (ψ (((φ.symm : A ≃+* A) : A →+* A) x)) := by
      simpa using h
    have h3 := congrArg ((χ.symm : B ≃+* B) : B → B) h2
    simpa using h3.symm
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro x hx
    rw [Ideal.mem_comap] at hx
    rw [Ideal.mem_comap]
    show ψ ((φ : A →+* A) x) ∈ P
    rw [hcomp x]
    exact (hmem (ψ x)).mpr hx
  · intro x hx
    rw [Ideal.mem_comap] at hx
    have hmem2 : ((φ.symm : A ≃+* A) : A →+* A) x ∈ Ideal.comap ψ P := by
      rw [Ideal.mem_comap, hcomp' x]
      exact (hmem' (ψ x)).mpr hx
    rw [show x = (φ : A →+* A) (((φ.symm : A ≃+* A) : A →+* A) x) from by simp]
    exact Ideal.mem_map_of_mem (φ : A →+* A) hmem2

end IdealComap

/-! ## Restriction of decomposition groups -/

section Decomposition

variable {K M : Type*} [Field K] [Field M] [NumberField K] [NumberField M] [Algebra K M]
  [FiniteDimensional K M] [IsGalois K M]

/-- **The decomposition subgroup of `w` maps into the decomposition subgroup of the place of an
intermediate field below `w`.** -/
theorem restrictNormalHom_mem_decompositionSubgroup (L : IntermediateField K M) [Normal K L]
    (w : IsDedekindDomain.HeightOneSpectrum (𝓞 M)) (σ : Gal(M/K))
    (hσ : σ ∈ decompositionSubgroup (K := K) w) :
    haveI : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
    AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ ∈
      decompositionSubgroup (K := K) (placeUnder (K := K) L w) := by
  haveI : IsGalois K ↥L := Commons.FieldTheory.Galois.isGalois_of_normal_of_charZero
  rw [mem_decompositionSubgroup]
  apply IsDedekindDomain.HeightOneSpectrum.ext
  rw [placeSmul_asIdeal, placeUnder_asIdeal, Ideal.under_def]
  refine Ideal.map_comap_eq_of_comp_eq
    ((galRestrict (𝓞 K) K ↥L (𝓞 ↥L)
      (AlgEquiv.restrictNormalHom (F := K) (K₁ := M) L σ) : 𝓞 L ≃+* 𝓞 L))
    (algebraMap (𝓞 L) (𝓞 M))
    ((galRestrict (𝓞 K) K M (𝓞 M) σ : 𝓞 M ≃+* 𝓞 M))
    w.asIdeal ?_ ?_
  · intro x
    exact galRestrict_restrictNormalHom L σ x
  · exact decompositionSubgroup_map_eq hσ

end Decomposition

end Submission.NeukirchUchida.Local
