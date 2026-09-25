import Mathlib
import Submission.Work.Tower.FrattiniLayer.Basic

/-!
# Base change of unramified extensions

If `E/F` is unramified at every finite prime and `L/F` is any finite extension of number fields,
then the compositum `E·L` is unramified over `L`: unramified-ness is preserved under base
change ("translation").  This is the lemma `Work.Tower.FrattiniLayer.baseChange_unramified`.

The proof goes through formal unramifiedness of rings of integers:

* `𝓞 ↥E` is formally unramified over `𝓞 F` by hypothesis;
* hence the tensor product `𝓞 ↥L ⊗[𝓞 F] 𝓞 ↥E` is formally unramified over `𝓞 ↥L`;
* the image `S` of the multiplication map into `𝓞 ↥(E ⊔ L)` is thus formally unramified over
  `𝓞 ↥L`, and, being a domain finite over the Dedekind domain `𝓞 ↥L`, is a Dedekind domain;
* an elementary argument with the fraction fields of `𝓞 ↥E` and `𝓞 ↥L` shows that the fraction
  field of `S` is all of `↥(E ⊔ L)`; since `𝓞 ↥(E ⊔ L)` is integral over `S` and `S` is
  integrally closed, `S = 𝓞 ↥(E ⊔ L)` and we are done.
-/

open NumberField
open scoped Classical nonZeroDivisors TensorProduct

namespace Work.Tower.FrattiniLayer

/-- For `E/F` a finite extension of number fields, the ring of integers `𝓞 E` is a finite
`𝓞 F`-module. -/
theorem module_finite_ringOfIntegers {F Ω : Type*} [Field F] [NumberField F] [Field Ω]
    [Algebra F Ω] (E : IntermediateField F Ω) [FiniteDimensional F ↥E] :
    Module.Finite (𝓞 F) (𝓞 ↥E) := by
  haveI : NumberField ↥E := NumberField.of_module_finite F ↥E
  haveI hst : IsScalarTower (𝓞 F) (𝓞 ↥E) ↥E := by
    refine IsScalarTower.of_algebraMap_eq fun x => ?_
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F ↥E,
      ← RingOfIntegers.coe_eq_algebraMap (K := F) x,
      ← RingOfIntegers.coe_eq_algebraMap (K := ↥E) ((algebraMap (𝓞 F) (𝓞 ↥E)) x)]
    exact (RingOfIntegers.mapRingHom_apply (algebraMap F ↥E) x).symm.trans rfl
  haveI hInt : Algebra.IsIntegral (𝓞 F) (𝓞 ↥E) :=
    ⟨fun x => IsIntegral.tower_top (R := ℤ) (A := 𝓞 F) (Algebra.IsIntegral.isIntegral x)⟩
  haveI : IsIntegralClosure (𝓞 ↥E) (𝓞 F) ↥E :=
    IsIntegralClosure.of_isIntegrallyClosed (𝓞 ↥E) (𝓞 F) ↥E
  exact IsIntegralClosure.finite (𝓞 F) F ↥E (𝓞 ↥E)

theorem baseChange_unramified {F Ω : Type*} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    (E L : IntermediateField F Ω) [FiniteDimensional F ↥E] [FiniteDimensional F ↥L]
    (hE : Work.Tower.FrattiniLayer.IsUnramifiedOver F ↥E) :
    Work.Tower.FrattiniLayer.IsUnramifiedSup E L := by
  haveI : NumberField ↥E := NumberField.of_module_finite F ↥E
  haveI : NumberField ↥L := NumberField.of_module_finite F ↥L
  letI : Algebra ↥L ↥(E ⊔ L) := (IntermediateField.inclusion (le_sup_right : L ≤ E ⊔ L)).toAlgebra
  letI : Algebra ↥E ↥(E ⊔ L) := (IntermediateField.inclusion (le_sup_left : E ≤ E ⊔ L)).toAlgebra
  haveI : NumberField ↥(E ⊔ L) := NumberField.of_module_finite F ↥(E ⊔ L)
  -- Reduce to formal unramifiedness of the rings of integers.
  rw [IsUnramifiedSup, isUnramifiedOver_iff_formallyUnramified]
  have hFE : Algebra.FormallyUnramified (𝓞 F) (𝓞 ↥E) :=
    (isUnramifiedOver_iff_formallyUnramified F ↥E).mp hE
  haveI : Algebra.FormallyUnramified (𝓞 ↥L) (𝓞 ↥L ⊗[𝓞 F] 𝓞 ↥E) :=
    Algebra.FormallyUnramified.base_change (𝓞 ↥L)
  -- The multiplication map on rings of integers.
  let μ : (𝓞 ↥L ⊗[𝓞 F] 𝓞 ↥E) →ₐ[𝓞 ↥L] 𝓞 ↥(E ⊔ L) :=
    Algebra.TensorProduct.lift
      (IsScalarTower.toAlgHom (𝓞 ↥L) (𝓞 ↥L) (𝓞 ↥(E ⊔ L)))
      (RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_left : E ≤ E ⊔ L)))
      (fun _ _ => Commute.all _ _)
  let S : Subalgebra (𝓞 ↥L) (𝓞 ↥(E ⊔ L)) := μ.range
  have hmemL : ∀ x : 𝓞 ↥L, algebraMap (𝓞 ↥L) (𝓞 ↥(E ⊔ L)) x ∈ S := fun x =>
    ⟨x ⊗ₜ[𝓞 F] 1, by simp [μ, Algebra.TensorProduct.lift_tmul]⟩
  have hmemE : ∀ x : 𝓞 ↥E,
      RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_left : E ≤ E ⊔ L)) x ∈ S :=
    fun x => ⟨1 ⊗ₜ[𝓞 F] x, by
      change μ (1 ⊗ₜ[𝓞 F] x) =
        RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_left : E ≤ E ⊔ L)) x
      simp only [μ, Algebra.TensorProduct.lift_tmul, map_one, one_mul]⟩
  haveI hUnramS : Algebra.FormallyUnramified (𝓞 ↥L) S :=
    Algebra.FormallyUnramified.of_surjective μ.rangeRestrict μ.rangeRestrict_surjective
  -- `S` is a Dedekind domain.
  haveI hFinE : Module.Finite (𝓞 F) (𝓞 ↥E) := module_finite_ringOfIntegers E
  haveI hFinT : Module.Finite (𝓞 ↥L) (𝓞 ↥L ⊗[𝓞 F] 𝓞 ↥E) :=
    Module.Finite.base_change (𝓞 F) (𝓞 ↥L) (𝓞 ↥E)
  haveI hFinS : Module.Finite (𝓞 ↥L) S :=
    Module.Finite.of_surjective (μ.rangeRestrict.restrictScalars (𝓞 ↥L)).toLinearMap
      μ.rangeRestrict_surjective
  haveI hDedS : IsDedekindDomain S := IsDedekindDomain.of_formallyUnramified (𝓞 ↥L) S
  -- The fraction field of `S` is `↥(E ⊔ L)`.
  let ψ : S →+* ↥(E ⊔ L) :=
    (algebraMap (𝓞 ↥(E ⊔ L)) ↥(E ⊔ L)).comp (Subalgebra.val S).toRingHom
  have halg : ∀ x : S, algebraMap S ↥(E ⊔ L) x = ψ x := fun x => rfl
  let φ : S →+* Ω := (IntermediateField.val (E ⊔ L)).toRingHom.comp ψ
  have hφ_apply : ∀ x : S, φ x = (IntermediateField.val (E ⊔ L)) (ψ x) := fun x => rfl
  -- `𝓞 ↥L` generates `↥L` inside `S`.
  have hLmem : (L : Set Ω) ⊆ (Subfield.closure (Set.range φ) : Set Ω) := by
    intro x hx
    obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (𝓞 ↥L) (⟨x, hx⟩ : ↥L)
    have hxa : φ ⟨algebraMap (𝓞 ↥L) (𝓞 ↥(E ⊔ L)) a, hmemL a⟩
        = ((algebraMap (𝓞 ↥L) ↥L a : ↥L) : Ω) := rfl
    have hxb : φ ⟨algebraMap (𝓞 ↥L) (𝓞 ↥(E ⊔ L)) b, hmemL b⟩
        = ((algebraMap (𝓞 ↥L) ↥L b : ↥L) : Ω) := rfl
    have hdiv : φ ⟨algebraMap (𝓞 ↥L) (𝓞 ↥(E ⊔ L)) a, hmemL a⟩
        / φ ⟨algebraMap (𝓞 ↥L) (𝓞 ↥(E ⊔ L)) b, hmemL b⟩ = x := by
      rw [hxa, hxb]
      change (IntermediateField.val L) ((algebraMap (𝓞 ↥L) ↥L) a / (algebraMap (𝓞 ↥L) ↥L) b) = x
      rw [hab]
      rfl
    rw [← hdiv]
    exact Subfield.div_mem _ (Subfield.subset_closure ⟨_, hxa⟩) (Subfield.subset_closure ⟨_, hxb⟩)
  -- `𝓞 ↥E` generates `↥E` inside `S`.
  have hEmem : (E : Set Ω) ⊆ (Subfield.closure (Set.range φ) : Set Ω) := by
    intro x hx
    obtain ⟨a, b, -, hab⟩ := IsFractionRing.div_surjective (𝓞 ↥E) (⟨x, hx⟩ : ↥E)
    have hxa : φ ⟨RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_left : E ≤ E ⊔ L)) a,
        hmemE a⟩ = ((algebraMap (𝓞 ↥E) ↥E a : ↥E) : Ω) := rfl
    have hxb : φ ⟨RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_left : E ≤ E ⊔ L)) b,
        hmemE b⟩ = ((algebraMap (𝓞 ↥E) ↥E b : ↥E) : Ω) := rfl
    have hdiv : φ ⟨RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_left : E ≤ E ⊔ L)) a,
          hmemE a⟩
        / φ ⟨RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_left : E ≤ E ⊔ L)) b,
          hmemE b⟩ = x := by
      rw [hxa, hxb]
      change (IntermediateField.val E) ((algebraMap (𝓞 ↥E) ↥E) a / (algebraMap (𝓞 ↥E) ↥E) b) = x
      rw [hab]
      rfl
    rw [← hdiv]
    exact Subfield.div_mem _ (Subfield.subset_closure ⟨_, hxa⟩) (Subfield.subset_closure ⟨_, hxb⟩)
  have hE' : E.toSubfield ≤ Subfield.closure (Set.range φ) := by
    rw [← Subfield.closure_eq E.toSubfield]
    exact Subfield.closure_le.mpr hEmem
  have hL : L.toSubfield ≤ Subfield.closure (Set.range φ) := by
    rw [← Subfield.closure_eq L.toSubfield]
    exact Subfield.closure_le.mpr hLmem
  have hclosure : Subfield.closure (Set.range φ) = (E ⊔ L).toSubfield := by
    refine le_antisymm (Subfield.closure_le.mpr ?_) ?_
    · rintro y ⟨s, rfl⟩
      rw [hφ_apply, IntermediateField.coe_toSubfield]
      exact SetLike.coe_mem (ψ s)
    · calc (E ⊔ L).toSubfield = E.toSubfield ⊔ L.toSubfield := IntermediateField.sup_toSubfield E L
        _ ≤ Subfield.closure (Set.range φ) := sup_le hE' hL
  have hsub : Subring.closure (Set.range φ) = φ.range := by
    refine le_antisymm ?_ ?_
    · rw [Subring.closure_le]
      rintro y ⟨s, rfl⟩
      exact RingHom.mem_range.mpr ⟨s, rfl⟩
    · rw [RingHom.range_eq_map, Subring.map_le_iff_le_comap]
      intro x _
      exact Subring.subset_closure ⟨x, rfl⟩
  haveI hFaith : FaithfulSMul S ↥(E ⊔ L) := by
    refine (faithfulSMul_iff_algebraMap_injective S ↥(E ⊔ L)).mpr fun x y hxy => ?_
    have h : ψ x = ψ y := by rw [← halg, ← halg]; exact hxy
    exact Subtype.val_injective (RingOfIntegers.coe_injective h)
  haveI hFrac : IsFractionRing S ↥(E ⊔ L) := by
    refine IsFractionRing.of_field S ↥(E ⊔ L) fun z => ?_
    have hz : ((z : ↥(E ⊔ L)) : Ω) ∈ Subfield.closure (Set.range φ) := by
      rw [hclosure]
      exact z.2
    obtain ⟨y, hy, y', hy', hyy⟩ := Subfield.mem_closure_iff.mp hz
    rw [hsub] at hy hy'
    obtain ⟨x, rfl⟩ := RingHom.mem_range.mp hy
    obtain ⟨x', rfl⟩ := RingHom.mem_range.mp hy'
    refine ⟨x, x', ?_⟩
    rw [halg, halg]
    apply Subtype.ext
    change (IntermediateField.val (E ⊔ L)) z = (IntermediateField.val (E ⊔ L)) (ψ x / ψ x')
    rw [map_div₀, ← hφ_apply x, ← hφ_apply x']
    exact hyy.symm
  -- `𝓞 ↥(E ⊔ L)` is integral over the integrally closed ring `S`, hence equal to it.
  have hInt : Algebra.IsIntegral S (𝓞 ↥(E ⊔ L)) :=
    ⟨fun x => IsIntegral.tower_top (R := ℤ) (A := S) (Algebra.IsIntegral.isIntegral x)⟩
  obtain ⟨-, -, -, hIC⟩ := (isDedekindDomain_iff S (↥(E ⊔ L))).mp hDedS
  have htop : S = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : IsIntegral S (algebraMap (𝓞 ↥(E ⊔ L)) ↥(E ⊔ L) x) := (hInt.1 x).algebraMap
    obtain ⟨y, hy⟩ := hIC hx
    have hyx : (y : 𝓞 ↥(E ⊔ L)) = x := by
      apply RingOfIntegers.coe_injective (K := ↥(E ⊔ L))
      exact hy
    rw [← hyx]
    exact y.2
  exact Algebra.FormallyUnramified.of_surjective (Subalgebra.val S)
    (fun x => ⟨⟨x, by rw [htop]; trivial⟩, rfl⟩)

end Work.Tower.FrattiniLayer
