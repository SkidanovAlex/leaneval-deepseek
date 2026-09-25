import Submission.NeukirchUchida.Local.PlaceFromValuation
import Mathlib.FieldTheory.Galois.Profinite
import Mathlib.FieldTheory.Galois.GaloisClosure
import Mathlib.FieldTheory.IntermediateField.Adjoin.Basic
import Mathlib.Topology.Compactness.Compact
import Submission.Commons.RingTheory.Valuation.ValuationSubring.smul_eq_comap_symm
import Submission.Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
import Submission.Commons.NumberTheory.RamificationInertia.exists_map_galRestrict_eq
import Submission.Commons.NumberTheory.RamificationInertia.exists_smul_valuationSubringAtPrime_eq
import Submission.Commons.NumberTheory.RamificationInertia.exists_smul_eq_of_comap_eq_of_finite
import Submission.Commons.NumberTheory.NumberField.ringOfIntegers_le_of_ne_top
import Submission.Commons.FieldTheory.Galois.eq_of_comap_eq_forall_finite_normal
import Submission.Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul
import Submission.Commons.FieldTheory.Galois.restrictNormal_symm_eq
import Submission.Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq

/-!
# Surjectivity of the restriction of decomposition groups

Let `K` be a number field, `K'` a Galois extension of `K` and `A` a valuation subring of `K'`
whose trace on `K` is the valuation ring `𝒪_𝔭` of a finite place `p` of `K`.  For every finite
normal intermediate field `L`, the trace `A ∩ L = A.comap (algebraMap L K')` is the valuation ring
of a finite place `w_L` of `L` (`placeOf`), and `Gal(K'/K) →* Gal(L/K)` restricts the
decomposition group `D_A` of `A` into `D_{w_L}`
(`restrictNormalHom_mem_decompositionSubgroup_of_mem_stabilizer`).

This file proves that this restriction is **surjective**:

* `decompositionRestrictHom` : the restriction homomorphism `D_A →* D_{w_L}`;
* `decompositionRestrictHom_surjective` : it is onto.

Equivalently (`exists_mem_stabilizer_restrictNormalHom_eq`): `Gal(K'/L)` acts *transitively* on
the places of `K'` restricting to a fixed place of `L`.  The key input is the transitivity of the
Galois action on the places of `K'` over a place of the base field, which is formalised in the
shared commons as `Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq` (finite level:
`Commons.NumberTheory.RamificationInertia.exists_smul_eq_of_comap_eq_of_finite`, obtained from the
fundamental identity `∑ e_i f_i = [L : K]`; infinite level: a compactness argument over the
finite normal intermediate fields).

Together with `stabilizer_eq_iInf_decompositionSubgroup`, the surjectivity says that the
decomposition group of a place of an infinite Galois extension of number fields *is* the inverse
limit of the local Galois groups of the completions of its finite levels — Neukirch–Schmidt–
Wingberg, *Cohomology of Number Fields*, Chapter XII §1.
-/

open scoped NumberField Pointwise Topology

set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false
set_option autoImplicit false

namespace Submission.NeukirchUchida.Local

section Basic

variable {F K' : Type*} [Field F] [Field K'] [Algebra F K']

/-- The image of a valuation subring under an algebra automorphism is the preimage under the
inverse automorphism. -/
theorem smul_eq_comap_symm_alg (A : ValuationSubring K') (σ : K' ≃ₐ[F] K') :
    σ • A = A.comap (σ.symm : K' →+* K') := by
  apply ValuationSubring.ext
  intro x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_comap]
  simp [AlgEquiv.smul_def]

/-- The preimage (`comap`) form of
`Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul`: the trace on a normal
intermediate field of `A.comap σ.symm` is the trace of `A` transported by `σ|_L`. -/
theorem comap_symm_comap_eq (A : ValuationSubring K') (σ : K' ≃ₐ[F] K')
    (L : IntermediateField F K') [Normal F L] :
    (A.comap (σ.symm : K' →+* K')).comap (algebraMap ↥L K') =
      (A.comap (algebraMap ↥L K')).comap
        ((AlgEquiv.restrictNormalHom (F := F) (K₁ := K') L σ).symm : ↥L →+* ↥L) := by
  have h := Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul A σ L
  rw [smul_eq_comap_symm_alg A σ,
    smul_eq_comap_symm_alg (A.comap (algebraMap ↥L K'))
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := K') L σ)] at h
  exact h

end Basic

/-! ## The finite level -/

section FiniteLevel

variable {F L : Type*} [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L]
  [FiniteDimensional F L] [IsGalois F L]

/-- The preimage form of the finite-level transitivity
`Commons.NumberTheory.RamificationInertia.exists_smul_eq_of_comap_eq_of_finite`. -/
theorem exists_comap_symm_eq_of_comap_eq_of_finite (P Q : ValuationSubring L) (hP : P ≠ ⊤)
    (hQ : Q ≠ ⊤)
    (h : P.comap (algebraMap F L) = Q.comap (algebraMap F L)) :
    ∃ σ : L ≃ₐ[F] L, P.comap (σ.symm : L →+* L) = Q := by
  obtain ⟨σ, hσ⟩ :=
    Commons.NumberTheory.RamificationInertia.exists_smul_eq_of_comap_eq_of_finite P Q hP hQ h
  exact ⟨σ, by rw [smul_eq_comap_symm_alg P σ] at hσ; exact hσ⟩

end FiniteLevel

/-! ## Surjectivity of the restriction of decomposition groups -/

section Application

variable {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K'] [IsGalois K K']

/-- **The restriction of the decomposition group of a place of `K'` to a finite normal
intermediate field is surjective.**

Equivalently: for `L/K` finite normal, `Gal(K'/L)` acts transitively on the places of `K'`
restricting to a given place of `L`. -/
theorem exists_mem_stabilizer_restrictNormalHom_eq
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L]
    (τ : decompositionSubgroup (K := K) (placeOf p A hA L)) :
    ∃ σ : Gal(K'/K), σ ∈ MulAction.stabilizer (Gal(K'/K)) A ∧
      AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ = (τ : ↥L ≃ₐ[K] ↥L) := by
  haveI : IsGalois ↥L K' := inferInstance
  haveI : NumberField ↥L := inferInstance
  have hCL := comap_eq_valuationSubringAtPrime_placeOf p A hA L
  set τ' : ↥L ≃ₐ[K] ↥L := (τ : ↥L ≃ₐ[K] ↥L) with hτ'def
  set σ₀ : K' ≃ₐ[K] K' := τ'.liftNormal K' with hσ₀def
  set B : ValuationSubring K' := A.comap (σ₀.symm : K' →+* K') with hBdef
  have hρσ₀ : AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L σ₀ = τ' := by
    rw [hσ₀def]
    rw [show AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L (τ'.liftNormal K') =
        (τ'.liftNormal K').restrictNormal L from rfl]
    exact AlgEquiv.restrict_liftNormal (K₁ := L) (E := K') τ'
  have hBcomap : B.comap (algebraMap ↥L K') = A.comap (algebraMap ↥L K') := by
    rw [hBdef, comap_symm_comap_eq A σ₀ L, hρσ₀]
    rw [← smul_eq_comap_symm_alg (A.comap (algebraMap ↥L K')) τ']
    rw [hτ'def, hCL]
    exact (mem_stabilizer_valuationSubringAtPrime_iff_mem_decompositionSubgroup
      (placeOf p A hA L) (τ : ↥L ≃ₐ[K] ↥L)).mpr τ.2
  have hBne : B.comap (algebraMap ↥L K') ≠ ⊤ := by
    rw [hBcomap, hCL]
    exact valuationSubringAtPrime_ne_top (K := ↥L) (placeOf p A hA L)
  obtain ⟨σ', hσ'⟩ :=
    Commons.FieldTheory.Galois.exists_smul_eq_of_comap_eq (F := ↥L) (K' := K') B A hBne hBcomap
  have hfix : AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L (σ'.restrictScalars K) = 1 := by
    rw [show AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L (σ'.restrictScalars K) =
        (σ'.restrictScalars K).restrictNormal L from rfl]
    ext x
    rw [AlgEquiv.restrictNormal_apply, AlgEquiv.restrictScalars_apply]
    show σ' ↑x = ↑x
    exact σ'.commutes x
  have hsmul : (σ'.restrictScalars K) • B = σ' • B := by
    rw [smul_eq_comap_symm_alg B (σ'.restrictScalars K), smul_eq_comap_symm_alg B σ']
    congr 1
  refine ⟨(σ'.restrictScalars K) * σ₀, ?_, ?_⟩
  · rw [MulAction.mem_stabilizer_iff, mul_smul]
    have h1 : σ₀ • A = B := by
      rw [hBdef]
      exact smul_eq_comap_symm_alg A σ₀
    rw [h1, hsmul, hσ']
  · rw [map_mul, hρσ₀, hfix, one_mul]

/-- **The restriction homomorphism `D_A →* D_{w_L}` from the decomposition group of a place of
`K'` to the decomposition group of its trace on a finite normal intermediate field.** -/
noncomputable def decompositionRestrictHom
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] :
    MulAction.stabilizer (Gal(K'/K)) A →* decompositionSubgroup (K := K) (placeOf p A hA L) :=
  MonoidHom.codRestrict
    ((AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L).comp
      (MulAction.stabilizer (Gal(K'/K)) A).subtype)
    (decompositionSubgroup (K := K) (placeOf p A hA L))
    (fun σ => restrictNormalHom_mem_decompositionSubgroup_of_mem_stabilizer A L
      (placeOf p A hA L) (comap_eq_valuationSubringAtPrime_placeOf p A hA L) (σ : Gal(K'/K)) σ.2)

theorem decompositionRestrictHom_apply
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L]
    (σ : MulAction.stabilizer (Gal(K'/K)) A) :
    ((decompositionRestrictHom p A hA L σ : decompositionSubgroup (K := K) (placeOf p A hA L)) :
        ↥L ≃ₐ[K] ↥L) =
      AlgEquiv.restrictNormalHom (F := K) (K₁ := K') L (σ : Gal(K'/K)) := rfl

/-- **The restriction `D_A →* D_{w_L}` is surjective.**  This is the inverse-limit statement at the
level of the finite quotients: together with `stabilizer_eq_iInf_decompositionSubgroup` it says
that the decomposition group of a place of an infinite Galois extension is the inverse limit of
the decomposition groups of its finite-level traces. -/
theorem decompositionRestrictHom_surjective
    (p : IsDedekindDomain.HeightOneSpectrum (𝓞 K)) (A : ValuationSubring K')
    (hA : A.comap (algebraMap K K') =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime K p)
    (L : IntermediateField K K') [FiniteDimensional K L] [Normal K L] :
    Function.Surjective (decompositionRestrictHom p A hA L) := by
  intro τ
  obtain ⟨σ, hσ, hσ'⟩ := exists_mem_stabilizer_restrictNormalHom_eq p A hA L τ
  exact ⟨⟨σ, hσ⟩, Subtype.ext hσ'⟩

end Application

end Submission.NeukirchUchida.Local
