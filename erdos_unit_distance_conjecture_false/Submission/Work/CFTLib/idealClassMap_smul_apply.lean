import Mathlib
import Submission.Work.CFTLib.NKIdeles
import Submission.Work.CFTLib.RelShafDefs
import Submission.Work.CFTLib.idealClassMap_smul

/-!
# The ideal class map commutes with the Galois action on idèles

For a finite Galois extension `K/F` of number fields and `σ : Gal(K/F)`, the ideal class map
`𝕀 K →* Cl(𝓞 K)` is equivariant for the action of `Gal(K/F)` on the idèles (given by
`(σ · x)_w = σ_*(x_{σ⁻¹ w})`) and the canonical action `clEquiv F K σ` on the class group.

The proof has two independent ingredients:

* `IdealClassMapAux.classGroup_mulEquiv_mk`: for a Dedekind domain `R`, a ring automorphism
  `e : R ≃+* R` and a field of fractions `K` of `R`, Mathlib's transport
  `ClassGroup.mulEquiv e` is computed on the classes of fractional ideals by
  `ClassGroup.mk K I ↦ ClassGroup.mk K (Units.mapEquiv (ringEquivOfRingEquiv K K e) I)`.
  The proof reduces to the decomposition `I = toPrincipalIdeal u * mk0 J` of an invertible
  fractional ideal into a principal ideal and an integral ideal.
* `IdealClassMapAux.idealOf_smul`: the fractional ideal `idealOf` attached to an idèle is
  transported by `σ`, i.e. `ringEquivOfRingEquiv K K e (idealOf x) = idealOf (σ · x)`.
  This is a statement about the `q`-adic exponents: `exp q (σ · x) = exp (σ⁻¹ q) x`, together
  with the fact that the transport of fractional ideals sends the prime `q` to `σ q`.
-/

open scoped nonZeroDivisors
open NumberField IsDedekindDomain

noncomputable section

namespace Work.CFTLib

namespace IdealClassMapAux

variable {R K : Type}

/-! ## The transport of the class group along a ring automorphism -/

/-- `ClassGroup.mk K` sends a principal fractional ideal to the identity class. -/
lemma classGroup_mk_toPrincipalIdeal [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (x : Kˣ) :
    ClassGroup.mk K (toPrincipalIdeal R K x) = 1 := by
  rw [ClassGroup.mk_eq_one_iff]
  refine Submodule.IsPrincipal.mk ⟨(x : K), ?_⟩
  rw [coe_toPrincipalIdeal, FractionalIdeal.coe_spanSingleton]

/-- The transport of a principal fractional ideal is the principal fractional ideal of the
transported generator. -/
lemma mapEquiv_toPrincipalIdeal [CommRing R] [IsDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (e : R ≃+* R) (u : Kˣ) :
    Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv K K e) (toPrincipalIdeal R K u) =
      toPrincipalIdeal R K (Units.mapEquiv
        (IsFractionRing.ringEquivOfRingEquiv (K := K) (L := K) e) u) := by
  apply Units.ext
  rw [Units.coe_mapEquiv, coe_toPrincipalIdeal, coe_toPrincipalIdeal, Units.coe_mapEquiv]
  exact FractionalIdeal.ringEquivOfRingEquiv_spanSingleton (K := K) (L := K) e (u : K)

/-- The transport of the integral fractional ideal attached to a nonzero integral ideal. -/
lemma mapEquiv_mk0 [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (e : R ≃+* R) (J : (Ideal R)⁰) :
    Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv K K e) (FractionalIdeal.mk0 K J) =
      FractionalIdeal.mk0 K ⟨J.1.map (e : R →+* R),
        mem_nonZeroDivisors_of_ne_zero
          ((Ideal.map_eq_bot_iff_of_injective e.injective).mp.mt
            (mem_nonZeroDivisors_iff_ne_zero.mp J.2))⟩ := by
  apply Units.ext
  rw [Units.coe_mapEquiv, FractionalIdeal.coe_mk0, FractionalIdeal.coe_mk0]
  exact Work.CFTLib.ClassGroupTransport.ringEquivOfRingEquiv_coeIdeal e J.1

/-- Every invertible fractional ideal is the product of a principal fractional ideal and the
fractional ideal attached to a nonzero integral ideal. -/
lemma exists_toPrincipalIdeal_mul_mk0 [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (I : (FractionalIdeal R⁰ K)ˣ) :
    ∃ (u : Kˣ) (J : (Ideal R)⁰), I = toPrincipalIdeal R K u * FractionalIdeal.mk0 K J := by
  obtain ⟨a, aI, ha, hI⟩ := FractionalIdeal.exists_eq_spanSingleton_mul (I : FractionalIdeal R⁰ K)
  have hane : algebraMap R K a ≠ 0 :=
    fun h => ha ((IsFractionRing.injective R K) (by rw [h, map_zero]))
  have haI : aI ≠ 0 := by
    intro h
    exact I.ne_zero (by rw [hI, h, Ideal.zero_eq_bot, FractionalIdeal.coeIdeal_bot, mul_zero])
  refine ⟨(Units.mk0 (algebraMap R K a) hane)⁻¹,
    ⟨aI, mem_nonZeroDivisors_of_ne_zero haI⟩, ?_⟩
  apply Units.ext
  rw [Units.val_mul, hI, coe_toPrincipalIdeal, FractionalIdeal.coe_mk0, Units.val_inv_eq_inv_val,
    Units.val_mk0]

/-- **Mathlib's `ClassGroup.mulEquiv` computed on the classes of fractional ideals.**  For a
Dedekind domain `R`, a ring automorphism `e : R ≃+* R` and a field of fractions `K` of `R`,
the induced automorphism of the class group sends `ClassGroup.mk K I` to the class of the
transported fractional ideal. -/
theorem classGroup_mulEquiv_mk [CommRing R] [IsDedekindDomain R] [Field K] [Algebra R K]
    [IsFractionRing R K] (e : R ≃+* R) (I : (FractionalIdeal R⁰ K)ˣ) :
    ClassGroup.mulEquiv e (ClassGroup.mk K I) =
      ClassGroup.mk K (Units.mapEquiv (FractionalIdeal.ringEquivOfRingEquiv K K e) I) := by
  obtain ⟨u, J, hIJ⟩ := exists_toPrincipalIdeal_mul_mk0 I
  rw [hIJ]
  simp only [map_mul]
  rw [classGroup_mk_toPrincipalIdeal, map_one, one_mul, ClassGroup.mk_mk0,
    Work.CFTLib.ClassGroupTransport.mk0_mulEquiv]
  rw [mapEquiv_toPrincipalIdeal, classGroup_mk_toPrincipalIdeal, mapEquiv_mk0,
    ClassGroup.mk_mk0, one_mul]

/-! ## Transport of the fractional ideal of an idèle -/

/-- The bijection of finite places induced by a ring automorphism `e`, sending `q` to
`e⁻¹ q = primeMap e q`. -/
noncomputable def primeMapEquiv [CommRing R] [IsDedekindDomain R] (e : R ≃+* R) :
    HeightOneSpectrum R ≃ HeightOneSpectrum R where
  toFun := primeMap e.symm
  invFun := primeMap e
  left_inv w := primeMap_symm_primeMap e w
  right_inv w := primeMap_symm_primeMap e.symm w

@[simp] lemma primeMapEquiv_apply [CommRing R] [IsDedekindDomain R] (e : R ≃+* R)
    (w : HeightOneSpectrum R) : primeMapEquiv e w = primeMap e.symm w := rfl

@[simp] lemma primeMapEquiv_symm_apply [CommRing R] [IsDedekindDomain R] (e : R ≃+* R)
    (w : HeightOneSpectrum R) : (primeMapEquiv e).symm w = primeMap e w := rfl

/-- The underlying prime of `primeMap e.symm q` is the image of `q.asIdeal` under `e`. -/
lemma primeMap_symm_asIdeal_map [CommRing R] [IsDedekindDomain R] (e : R ≃+* R)
    (q : HeightOneSpectrum R) :
    (primeMap e.symm q).asIdeal = (q.asIdeal.map (e : R →+* R) : Ideal R) := by
  rw [primeMap_asIdeal_map, RingEquiv.symm_symm]
  rfl

/-- **The fractional ideal of an idèle is transported by the Galois action.**  For `σ : Gal(K/F)`
and an idèle `x` of `K`, the transport of the fractional ideal `idealOf x` along the
ring automorphism of `𝓞 K` induced by `σ` is the fractional ideal of `σ · x`. -/
theorem idealOf_smul {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K] [Algebra F K]
    (σ : K ≃ₐ[F] K) (x : NK.GlobalCFT.Idele K) :
    FractionalIdeal.ringEquivOfRingEquiv K K
        (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv
        (NK.GlobalCFT.Idele.idealOf x) = NK.GlobalCFT.Idele.idealOf (σ • x) := by
  set e : 𝓞 K ≃+* 𝓞 K := (NumberField.RingOfIntegers.mapAlgEquiv σ).toRingEquiv
  have heq : e = NK.GlobalCFT.Place.ringOfIntegersEquiv σ := rfl
  have hh : Finsupp.equivMapDomain (primeMapEquiv e) (NK.GlobalCFT.Idele.expFinsupp x)
      = NK.GlobalCFT.Idele.expFinsupp (σ • x) := by
    ext q
    rw [Finsupp.equivMapDomain_apply, NK.GlobalCFT.Idele.expFinsupp_apply,
      NK.GlobalCFT.Idele.expFinsupp_apply, primeMapEquiv_symm_apply, heq,
      primeMap_ringOfIntegersEquiv, ← NK.GlobalCFT.Idele.exp_smul]
  rw [NK.GlobalCFT.Idele.idealOf, NK.GlobalCFT.Idele.idealOf, ← hh,
    Finsupp.prod_equivMapDomain]
  rw [Finsupp.prod, Finsupp.prod, map_prod]
  refine Finset.prod_congr rfl fun q _ => ?_
  rw [map_zpow₀, Work.CFTLib.ClassGroupTransport.ringEquivOfRingEquiv_coeIdeal,
    primeMapEquiv_apply, primeMap_symm_asIdeal_map]

end IdealClassMapAux

/-- **The ideal class map commutes with the Galois action on idèles.**  For `σ : Gal(K/F)`, the
class of the ideal attached to `σ · x` is the transport by `σ` of the class of the ideal
attached to `x`. -/
theorem idealClassMap_smul_apply {F K : Type} [Field F] [NumberField F] [Field K] [NumberField K]
    [Algebra F K] (σ : K ≃ₐ[F] K) (x : NK.GlobalCFT.Idele K) :
    NK.GlobalCFT.IdeleClassGroup.idealClassMap K (σ • x) =
      Work.CFTLib.clEquiv F K σ (NK.GlobalCFT.IdeleClassGroup.idealClassMap K x) := by
  rw [NK.GlobalCFT.IdeleClassGroup.idealClassMap_apply,
    NK.GlobalCFT.IdeleClassGroup.idealClassMap_apply, Work.CFTLib.clEquiv,
    IdealClassMapAux.classGroup_mulEquiv_mk]
  congr 1
  apply Units.ext
  rw [Units.coe_mapEquiv, Units.val_mk0, Units.val_mk0]
  exact (IdealClassMapAux.idealOf_smul σ x).symm

end Work.CFTLib
