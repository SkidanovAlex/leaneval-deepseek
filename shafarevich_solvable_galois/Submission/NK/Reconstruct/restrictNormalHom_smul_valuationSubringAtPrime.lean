import Mathlib.RingTheory.DedekindDomain.AdicValuation
import Submission.Commons.RingTheory.Valuation.comap_valuationSubringAtPrime
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

/-!
# Restriction of a place-stabilising automorphism to a normal intermediate field

Let `K ⊆ E ⊆ N` be a tower of number fields with `E/K` normal and `N/K` Galois, and let `q` be a
finite place of `N` lying over the finite place `q'` of `E`.  If `σ ∈ Gal(N/K)` stabilises the
valuation ring `𝒪_{N,q}`, then its restriction `σ|_E ∈ Gal(E/K)` stabilises `𝒪_{E,q'}`.

This is the compatibility of the Galois action on valuation subrings with restriction to
intermediate fields: it is what makes the projective system of decomposition groups of the finite
levels well defined (Neukirch–Schmidt–Wingberg, *Cohomology of Number Fields*, Chapter XII §1).

The proof has two ingredients:

* `comap_smul_eq_restrictNormalHom_smul'` : for any valuation subring `A` of `N`, the trace on `E`
  of `σ • A` is `σ|_E • (A ∩ E)`;
* `Commons.RingTheory.Valuation.comap_valuationSubringAtPrime` : `𝒪_{N,q} ∩ E = 𝒪_{E,q'}`.
-/

namespace NK.Reconstruct

open scoped Pointwise

/-- **The trace on a normal intermediate field of the image of a valuation subring is the image
of its trace**: `(σ • A) ∩ E = σ|_E • (A ∩ E)`, where `E` is any field equipped with a scalar
tower `F ⊆ E ⊆ K` and `E/F` is normal (the version of
`Commons.FieldTheory.Galois.comap_smul_eq_restrictNormalHom_smul` for a bare intermediate type
rather than an `IntermediateField`). -/
theorem comap_smul_eq_restrictNormalHom_smul' {F E K : Type*} [Field F] [Field E] [Field K]
    [Algebra F E] [Algebra E K] [Algebra F K] [IsScalarTower F E K] [Normal F E]
    (A : ValuationSubring K) (σ : K ≃ₐ[F] K) :
    (σ • A).comap (algebraMap E K) =
      (AlgEquiv.restrictNormalHom (F := F) (K₁ := K) E σ) • (A.comap (algebraMap E K)) := by
  ext x
  simp only [ValuationSubring.mem_comap, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
  rw [show (σ⁻¹ : K ≃ₐ[F] K) = σ.symm from rfl]
  rw [show ((AlgEquiv.restrictNormalHom (F := F) (K₁ := K) E σ)⁻¹ : E ≃ₐ[F] E)
      = AlgEquiv.restrictNormalHom (F := F) (K₁ := K) E σ.symm from
        (map_inv (AlgEquiv.restrictNormalHom (F := F) (K₁ := K) E) σ).symm]
  change σ.symm (algebraMap E K x) ∈ A ↔
      algebraMap E K ((AlgEquiv.restrictNormalHom (F := F) (K₁ := K) E) σ.symm x) ∈ A
  rw [show (AlgEquiv.restrictNormalHom (F := F) (K₁ := K) E) σ.symm
      = (σ.symm).restrictNormal E from rfl]
  rw [AlgEquiv.restrictNormal_commutes]

open scoped Pointwise in
theorem restrictNormalHom_smul_valuationSubringAtPrime {K E N : Type*} [Field K] [NumberField K]
    [Field E] [NumberField E] [Field N] [NumberField N] [Algebra K E] [Algebra E N] [Algebra K N]
    [IsScalarTower K E N] [FiniteDimensional K E] [Normal K E]
    [FiniteDimensional K N] [IsGalois K N]
    (q : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers N))
    (q' : IsDedekindDomain.HeightOneSpectrum (NumberField.RingOfIntegers E))
    (hq' : q'.asIdeal = q.asIdeal.under (NumberField.RingOfIntegers E))
    {σ : Gal(N/K)}
    (hσ : σ • IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime N q =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime N q) :
    (AlgEquiv.restrictNormalHom (F := K) (K₁ := N) E σ) •
        IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E q' =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E q' := by
  -- `N` is finite over the intermediate field `E`
  have hfin : FiniteDimensional E N := Module.Finite.of_restrictScalars_finite K E N
  -- `q` lies over `q'`
  have hLies : q.asIdeal.LiesOver q'.asIdeal := ⟨hq'⟩
  -- the trace of the valuation ring of `q` on `E` is the valuation ring of `q'`
  have hcomap : (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime N q).comap
        (algebraMap E N) =
      IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime E q' :=
    Commons.RingTheory.Valuation.comap_valuationSubringAtPrime q' q hLies
  -- the trace of `σ • 𝒪_{N,q}` is the image of the trace
  have hkey := comap_smul_eq_restrictNormalHom_smul' (F := K) (E := E) (K := N)
    (IsDedekindDomain.HeightOneSpectrum.valuationSubringAtPrime N q) σ
  rw [hσ] at hkey
  rw [hcomap] at hkey
  exact hkey.symm

end NK.Reconstruct
