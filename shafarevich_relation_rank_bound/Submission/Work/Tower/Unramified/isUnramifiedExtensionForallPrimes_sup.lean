import Mathlib
import Submission.Work.Tower.Unramified.Basic
import Submission.Work.Tower.Unramified.isFractionRing_of_span_eq_top
import Submission.Work.Tower.Unramified.span_eq_top_of_le

open NumberField
open scoped Classical nonZeroDivisors

namespace Work
namespace Tower
namespace Unramified

variable {F L : Type*} [Field F] [NumberField F] [Field L] [Algebra F L]

/-- For a finite extension `E/F` of number fields, being unramified at every finite prime is
equivalent to formal unramifiedness of the extension `𝓞 E / 𝓞 F` of rings of integers. -/
theorem isUnramifiedExtensionForallPrimes_iff_formallyUnramified
    {E : IntermediateField F L} [FiniteDimensional F E] :
    Tower.IsUnramifiedExtensionForallPrimes F E ↔
      Algebra.FormallyUnramified (𝓞 F) (𝓞 ↥E) := by
  haveI : NumberField ↥E := NumberField.of_module_finite F ↥E
  rw [Algebra.formallyUnramified_iff_forall]
  constructor
  · intro h 𝔭
    exact Tower.IsUnramifiedExtensionForallPrimes_iff_forall_isUnramifiedAt.mp h 𝔭.1
  · intro h 𝔓 h𝔓
    exact Tower.IsUnramifiedExtensionForallPrimes_iff_forall_isUnramifiedAt.mpr
      (fun 𝔓 h𝔓 => h ⟨𝔓, h𝔓⟩) 𝔓 h𝔓


/-- Every element of `F = Frac A` is an `F`-multiple of an element of the image of `A`. -/
theorem algebraMap_mem_span {A F K : Type*} [CommRing A] [Field F] [Field K]
    [Algebra A F] [IsFractionRing A F] [Algebra A K] [Algebra F K] [IsScalarTower A F K]
    (f : F) : algebraMap F K f ∈ Submodule.span F (Set.range (algebraMap A K)) := by
  obtain ⟨a, s, hs, h⟩ := IsFractionRing.div_surjective A (K := F) f
  have hmem : (algebraMap A F s)⁻¹ • (algebraMap A K a)
      ∈ Submodule.span F (Set.range (algebraMap A K)) :=
    Submodule.smul_mem _ ((algebraMap A F s)⁻¹)
      (Submodule.subset_span (Set.mem_range_self (f := algebraMap A K) a))
  convert hmem using 1
  rw [← h, map_div₀, ← IsScalarTower.algebraMap_apply A F K,
    ← IsScalarTower.algebraMap_apply A F K, div_eq_mul_inv, mul_comm,
    IsScalarTower.algebraMap_apply A F K, ← map_inv₀, Algebra.smul_def]

theorem isUnramifiedExtensionForallPrimes_sup
    {F L : Type*} [Field F] [NumberField F] [Field L] [Algebra F L]
    {E₁ E₂ : IntermediateField F L} [FiniteDimensional F E₁] [FiniteDimensional F E₂]
    (h₁ : Work.Tower.IsUnramifiedExtensionForallPrimes F E₁)
    (h₂ : Work.Tower.IsUnramifiedExtensionForallPrimes F E₂) :
    Work.Tower.IsUnramifiedExtensionForallPrimes F ↥(E₁ ⊔ E₂) := by
  haveI : NumberField ↥E₁ := NumberField.of_module_finite F ↥E₁
  haveI : NumberField ↥E₂ := NumberField.of_module_finite F ↥E₂
  haveI : NumberField ↥(E₁ ⊔ E₂) := NumberField.of_module_finite F ↥(E₁ ⊔ E₂)
  refine (isUnramifiedExtensionForallPrimes_iff_formallyUnramified (E := E₁ ⊔ E₂)).mpr ?_
  haveI hFU₁ : Algebra.FormallyUnramified (𝓞 F) (𝓞 ↥E₁) :=
    (isUnramifiedExtensionForallPrimes_iff_formallyUnramified (E := E₁)).mp h₁
  haveI hFU₂ : Algebra.FormallyUnramified (𝓞 F) (𝓞 ↥E₂) :=
    (isUnramifiedExtensionForallPrimes_iff_formallyUnramified (E := E₂)).mp h₂
  -- The `𝓞 F`-algebra maps `𝓞 Eᵢ → 𝓞 (E₁ ⊔ E₂)`.
  let φ₁ : 𝓞 ↥E₁ →ₐ[𝓞 F] 𝓞 ↥(E₁ ⊔ E₂) :=
    RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂))
  let φ₂ : 𝓞 ↥E₂ →ₐ[𝓞 F] 𝓞 ↥(E₁ ⊔ E₂) :=
    RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂))
  -- The tensor product is formally unramified over `𝓞 F`.
  haveI hT' : Algebra.FormallyUnramified (𝓞 ↥E₁) (TensorProduct (𝓞 F) (𝓞 ↥E₁) (𝓞 ↥E₂)) :=
    Algebra.FormallyUnramified.base_change (R := 𝓞 F) (A := 𝓞 ↥E₂) (𝓞 ↥E₁)
  haveI hT : Algebra.FormallyUnramified (𝓞 F) (TensorProduct (𝓞 F) (𝓞 ↥E₁) (𝓞 ↥E₂)) :=
    Algebra.FormallyUnramified.comp (𝓞 F) (𝓞 ↥E₁) _
  -- The multiplication map and its image `S`.
  let μ : TensorProduct (𝓞 F) (𝓞 ↥E₁) (𝓞 ↥E₂) →ₐ[𝓞 F] 𝓞 ↥(E₁ ⊔ E₂) :=
    Algebra.TensorProduct.lift φ₁ φ₂ (fun _ _ => .all _ _)
  let S : Subalgebra (𝓞 F) (𝓞 ↥(E₁ ⊔ E₂)) := μ.range
  haveI hS : Algebra.FormallyUnramified (𝓞 F) S :=
    Algebra.FormallyUnramified.of_surjective μ.rangeRestrict μ.rangeRestrict_surjective
  haveI hFin : Module.Finite (𝓞 F) S := by
    refine Module.Finite.of_surjective (μ.rangeRestrict.restrictScalars (𝓞 F)).toLinearMap ?_
    exact μ.rangeRestrict_surjective
  haveI hDom : IsDomain S := by infer_instance
  haveI hDed : IsDedekindDomain S := IsDedekindDomain.of_formallyUnramified (𝓞 F) S
  -- `S` is integrally closed, so it is the integral closure of `𝓞 F` in `↥(E₁ ⊔ E₂)`.
  haveI hInt : Algebra.IsIntegral (𝓞 F) S :=
    ⟨fun x => (isIntegral_algHom_iff (f := Subalgebra.val S) Subtype.val_injective).mp
      (Algebra.IsIntegral.isIntegral (Subalgebra.val S x))⟩
  have hspan : Submodule.span F ((algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)) ''
      (S : Set (𝓞 ↥(E₁ ⊔ E₂)))) = ⊤ :=
    span_eq_top_of_le S
      (fun x => ⟨x ⊗ₜ[𝓞 F] 1, by
        change (Algebra.TensorProduct.lift φ₁ φ₂ (fun x y => Commute.all (φ₁ x) (φ₂ y)))
          (x ⊗ₜ[𝓞 F] 1) = φ₁ x
        rw [Algebra.TensorProduct.lift_tmul, map_one, mul_one]⟩)
      (fun y => ⟨1 ⊗ₜ[𝓞 F] y, by
        change (Algebra.TensorProduct.lift φ₁ φ₂ (fun x y => Commute.all (φ₁ x) (φ₂ y)))
          (1 ⊗ₜ[𝓞 F] y) = φ₂ y
        rw [Algebra.TensorProduct.lift_tmul, map_one, one_mul]⟩)
  have hFrac : IsFractionRing S ↥(E₁ ⊔ E₂) := isFractionRing_of_span_eq_top S hspan
  have hIC : IsIntegralClosure S (𝓞 F) ↥(E₁ ⊔ E₂) :=
    IsIntegralClosure.of_isIntegrallyClosed S (𝓞 F) ↥(E₁ ⊔ E₂)
  -- Hence `S` is all of `𝓞 ↥(E₁ ⊔ E₂)`.
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : IsIntegral (𝓞 F) (algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂) x) :=
      IsIntegral.map (Algebra.ofId (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂))
        (Algebra.IsIntegral.isIntegral x)
    obtain ⟨y, hy⟩ :=
      (IsIntegralClosure.isIntegral_iff (A := S) (R := 𝓞 F) (B := ↥(E₁ ⊔ E₂))).mp hx
    obtain ⟨t, ht⟩ := y.2
    have h1 : (((y : ↥S) : 𝓞 ↥(E₁ ⊔ E₂)) : ↥(E₁ ⊔ E₂))
        = ((x : 𝓞 ↥(E₁ ⊔ E₂)) : ↥(E₁ ⊔ E₂)) := by
      simpa only [IsScalarTower.algebraMap_apply ↥S (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂),
        Subalgebra.algebraMap_apply] using hy
    refine ⟨t, ?_⟩
    rw [ht]
    exact IsFractionRing.injective (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂) h1
  exact Algebra.FormallyUnramified.of_surjective (Subalgebra.val S)
    (fun x => ⟨⟨x, by rw [htop]; trivial⟩, rfl⟩)

end Unramified
end Tower
end Work
