import Mathlib

set_option linter.style.haveILetI false

namespace Work.Tower.Unramified

open NumberField

/-- In a number field `k`, some nonzero natural multiple of every element lies in the image
of the ring of integers. -/
lemma exists_nat_nsmul_eq_algebraMap (k : Type*) [Field k] [NumberField k] (x : k) :
    ∃ (m : ℕ) (r : 𝓞 k), m ≠ 0 ∧ m • x = algebraMap (𝓞 k) k r := by
  have hx : IsAlgebraic ℤ x := (IsFractionRing.isAlgebraic_iff ℤ ℚ k).mpr (.of_finite ℚ x)
  exact hx.exists_nsmul_eq (𝓞 k)

lemma inclusion_range_le_adjoin_left
    {F L : Type*} [Field F] [NumberField F] [Field L] [Algebra F L]
    {E₁ E₂ : IntermediateField F L} [FiniteDimensional F E₁] [FiniteDimensional F E₂]
    (S : Subalgebra (𝓞 F) (𝓞 ↥(E₁ ⊔ E₂)))
    (h₁ : ∀ x : 𝓞 ↥E₁,
      RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂)) x ∈ S) :
    (IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂)).range ≤
      Algebra.adjoin F ((algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)) ''
        (S : Set (𝓞 ↥(E₁ ⊔ E₂)))) := by
  haveI : NumberField ↥E₁ := NumberField.of_module_finite F ↥E₁
  haveI : NumberField ↥(E₁ ⊔ E₂) := NumberField.of_module_finite F ↥(E₁ ⊔ E₂)
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨m, r, hm, hr⟩ := exists_nat_nsmul_eq_algebraMap ↥E₁ y
  have hmem_image : algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)
      (RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂)) r) ∈
      (algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)) '' (S : Set (𝓞 ↥(E₁ ⊔ E₂))) :=
    ⟨RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂)) r,
      h₁ r, rfl⟩
  have hEq : (m : F) • (IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂) y) =
      algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)
        (RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂)) r) := by
    rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hr]
    rfl
  have hmul : (m : F) • (IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂) y) ∈
      Algebra.adjoin F ((algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)) ''
        (S : Set (𝓞 ↥(E₁ ⊔ E₂)))) := hEq ▸ Algebra.subset_adjoin hmem_image
  have hthis := (Algebra.adjoin F ((algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)) ''
        (S : Set (𝓞 ↥(E₁ ⊔ E₂))))).smul_mem hmul ((m : F)⁻¹)
  rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm), one_smul] at hthis
  simpa using hthis

lemma inclusion_range_le_adjoin_right
    {F L : Type*} [Field F] [NumberField F] [Field L] [Algebra F L]
    {E₁ E₂ : IntermediateField F L} [FiniteDimensional F E₁] [FiniteDimensional F E₂]
    (S : Subalgebra (𝓞 F) (𝓞 ↥(E₁ ⊔ E₂)))
    (h₂ : ∀ x : 𝓞 ↥E₂,
      RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂)) x ∈ S) :
    (IntermediateField.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂)).range ≤
      Algebra.adjoin F ((algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)) ''
        (S : Set (𝓞 ↥(E₁ ⊔ E₂)))) := by
  haveI : NumberField ↥E₂ := NumberField.of_module_finite F ↥E₂
  haveI : NumberField ↥(E₁ ⊔ E₂) := NumberField.of_module_finite F ↥(E₁ ⊔ E₂)
  intro x hx
  obtain ⟨y, rfl⟩ := hx
  obtain ⟨m, r, hm, hr⟩ := exists_nat_nsmul_eq_algebraMap ↥E₂ y
  have hmem_image : algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)
      (RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂)) r) ∈
      (algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)) '' (S : Set (𝓞 ↥(E₁ ⊔ E₂))) :=
    ⟨RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂)) r,
      h₂ r, rfl⟩
  have hEq : (m : F) • (IntermediateField.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂) y) =
      algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)
        (RingOfIntegers.mapAlgHom (IntermediateField.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂)) r) := by
    rw [Nat.cast_smul_eq_nsmul, ← map_nsmul, hr]
    rfl
  have hmul : (m : F) • (IntermediateField.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂) y) ∈
      Algebra.adjoin F ((algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)) ''
        (S : Set (𝓞 ↥(E₁ ⊔ E₂)))) := hEq ▸ Algebra.subset_adjoin hmem_image
  have hthis := (Algebra.adjoin F ((algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)) ''
        (S : Set (𝓞 ↥(E₁ ⊔ E₂))))).smul_mem hmul ((m : F)⁻¹)
  rw [smul_smul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hm), one_smul] at hthis
  simpa using hthis

lemma range_inclusion_sup_eq_top
    {F L : Type*} [Field F] [Field L] [Algebra F L]
    {E₁ E₂ : IntermediateField F L} [FiniteDimensional F E₁] [FiniteDimensional F E₂] :
    (IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂)).range ⊔
      (IntermediateField.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂)).range = ⊤ := by
  have hι : Function.Injective (IntermediateField.val (E₁ ⊔ E₂)) := fun a b h => Subtype.ext h
  refine Subalgebra.map_injective (f := IntermediateField.val (E₁ ⊔ E₂)) hι ?_
  have hcomp₁ : (IntermediateField.val (E₁ ⊔ E₂)).comp
      (IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂)) = E₁.val :=
    AlgHom.ext fun x => rfl
  have hcomp₂ : (IntermediateField.val (E₁ ⊔ E₂)).comp
      (IntermediateField.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂)) = E₂.val :=
    AlgHom.ext fun x => rfl
  have hA : (IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂)).range.map
      (IntermediateField.val (E₁ ⊔ E₂)) = E₁.toSubalgebra := by
    rw [← AlgHom.range_comp (IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂))
      (IntermediateField.val (E₁ ⊔ E₂)), hcomp₁, IntermediateField.range_val]
  have hB : (IntermediateField.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂)).range.map
      (IntermediateField.val (E₁ ⊔ E₂)) = E₂.toSubalgebra := by
    rw [← AlgHom.range_comp (IntermediateField.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂))
      (IntermediateField.val (E₁ ⊔ E₂)), hcomp₂, IntermediateField.range_val]
  rw [Algebra.map_sup, Algebra.map_top, hA, hB, IntermediateField.range_val,
    ← IntermediateField.sup_toSubalgebra_of_left E₁ E₂]

theorem span_eq_top_of_le
    {F L : Type*} [Field F] [NumberField F] [Field L] [Algebra F L]
    {E₁ E₂ : IntermediateField F L} [FiniteDimensional F E₁] [FiniteDimensional F E₂]
    (S : Subalgebra (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥(E₁ ⊔ E₂)))
    (h₁ : ∀ x : NumberField.RingOfIntegers ↥E₁,
      NumberField.RingOfIntegers.mapAlgHom
        (IntermediateField.inclusion (le_sup_left : E₁ ≤ E₁ ⊔ E₂)) x ∈ S)
    (h₂ : ∀ x : NumberField.RingOfIntegers ↥E₂,
      NumberField.RingOfIntegers.mapAlgHom
        (IntermediateField.inclusion (le_sup_right : E₂ ≤ E₁ ⊔ E₂)) x ∈ S) :
    Submodule.span F
      ((algebraMap (NumberField.RingOfIntegers ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)) ''
        (S : Set (NumberField.RingOfIntegers ↥(E₁ ⊔ E₂)))) = ⊤ := by
  haveI : NumberField ↥(E₁ ⊔ E₂) := NumberField.of_module_finite F ↥(E₁ ⊔ E₂)
  have htop : Algebra.adjoin F ((algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)) ''
      (S : Set (𝓞 ↥(E₁ ⊔ E₂)))) = ⊤ := by
    apply le_antisymm le_top
    rw [← range_inclusion_sup_eq_top (E₁ := E₁) (E₂ := E₂)]
    exact sup_le (inclusion_range_le_adjoin_left S h₁) (inclusion_range_le_adjoin_right S h₂)
  have hspan : Submodule.span F ((algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)) ''
      (S : Set (𝓞 ↥(E₁ ⊔ E₂)))) =
      (Algebra.adjoin F ((algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)) ''
        (S : Set (𝓞 ↥(E₁ ⊔ E₂))))).toSubmodule := by
    rw [Algebra.adjoin_eq_span]
    congr 1
    let f : 𝓞 ↥(E₁ ⊔ E₂) →+* ↥(E₁ ⊔ E₂) := algebraMap (𝓞 ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)
    let N : Submonoid ↥(E₁ ⊔ E₂) := (Subsemiring.map f S.toSubsemiring).toSubmonoid
    have hMN : (N : Set ↥(E₁ ⊔ E₂)) = f '' (S : Set (𝓞 ↥(E₁ ⊔ E₂))) := by
      simp [N, f]
    rw [← hMN, Submonoid.closure_eq]
  rw [hspan, htop]
  exact Algebra.top_toSubmodule

end Work.Tower.Unramified
