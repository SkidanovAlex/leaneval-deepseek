import Mathlib

namespace Work.Tower.Unramified

open NumberField

/-- If an `𝓞_F`-subalgebra `S` of the ring of integers of `E₁ ⊔ E₂` spans the whole compositum
`E₁ ⊔ E₂` as an `F`-vector space, then `E₁ ⊔ E₂` is the field of fractions of `S`.

The proof uses `IsFractionRing.of_field`: the canonical map `S → E₁ ⊔ E₂` is injective (both maps
`S ↪ 𝓞_{E₁⊔E₂}` and `𝓞_{E₁⊔E₂} ↪ E₁ ⊔ E₂` are), and every element of `E₁ ⊔ E₂` is a ratio of
elements of `S`. For the latter, write a given element as an `F`-linear combination of images of
elements of `S` (using the hypothesis), clear the denominators of the scalars using
`IsFractionRing (𝓞 F) F`, and use that `S` is an `𝓞 F`-subalgebra. -/
theorem isFractionRing_of_span_eq_top
    {F L : Type*} [Field F] [NumberField F] [Field L] [Algebra F L]
    {E₁ E₂ : IntermediateField F L} [FiniteDimensional F E₁] [FiniteDimensional F E₂]
    (S : Subalgebra (NumberField.RingOfIntegers F) (NumberField.RingOfIntegers ↥(E₁ ⊔ E₂)))
    (h : Submodule.span F
      ((algebraMap (NumberField.RingOfIntegers ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)) ''
        (S : Set (NumberField.RingOfIntegers ↥(E₁ ⊔ E₂)))) = ⊤) :
    IsFractionRing S ↥(E₁ ⊔ E₂) := by
  classical
  -- The canonical map `S → E₁ ⊔ E₂` is injective.
  have hinj : Function.Injective (algebraMap S ↥(E₁ ⊔ E₂)) := fun a b hab =>
    Subtype.ext (NumberField.RingOfIntegers.coe_injective hab)
  have hf : FaithfulSMul S ↥(E₁ ⊔ E₂) :=
    (faithfulSMul_iff_algebraMap_injective S ↥(E₁ ⊔ E₂)).2 hinj
  apply IsFractionRing.of_field S ↥(E₁ ⊔ E₂)
  intro z
  have hz : z ∈ Submodule.span F
      ((algebraMap (NumberField.RingOfIntegers ↥(E₁ ⊔ E₂)) ↥(E₁ ⊔ E₂)) ''
        (S : Set (NumberField.RingOfIntegers ↥(E₁ ⊔ E₂)))) := by
    rw [h]; exact Submodule.mem_top
  -- We prove the stronger, cross-multiplied form of surjectivity by induction on the `F`-span.
  suffices key : ∃ x y : S, y ≠ 0 ∧
      algebraMap S ↥(E₁ ⊔ E₂) x = z * algebraMap S ↥(E₁ ⊔ E₂) y by
    obtain ⟨x, y, hy, hxy⟩ := key
    exact ⟨x, y, (eq_div_iff_mul_eq ((map_ne_zero_iff _ hinj).2 hy)).2 hxy.symm⟩
  refine Submodule.span_induction (p := fun w _ => ∃ x y : S, y ≠ 0 ∧
      algebraMap S ↥(E₁ ⊔ E₂) x = w * algebraMap S ↥(E₁ ⊔ E₂) y) ?_ ?_ ?_ ?_ hz
  · -- generators: `algebraMap (𝓞_{E₁⊔E₂}) (E₁⊔E₂) s` for `s ∈ S`
    rintro x ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, 1, one_ne_zero, by simp⟩
  · exact ⟨0, 1, one_ne_zero, by simp⟩
  · -- addition of two ratios
    rintro x y _ _ ⟨x₁, y₁, hy₁, h₁⟩ ⟨x₂, y₂, hy₂, h₂⟩
    refine ⟨x₁ * y₂ + x₂ * y₁, y₁ * y₂, mul_ne_zero hy₁ hy₂, ?_⟩
    simp only [map_add, map_mul, h₁, h₂]
    ring
  · -- multiplication by a scalar `c : F`; clear the denominator of `c` in `𝓞 F`
    rintro c x _ ⟨x₁, y₁, hy₁, h₁⟩
    obtain ⟨⟨a, b⟩, hab⟩ :=
      IsLocalization.surj (nonZeroDivisors (NumberField.RingOfIntegers F)) c
    have hb : b.1 ≠ 0 := mem_nonZeroDivisors_iff_ne_zero.mp b.2
    have hbF : algebraMap (NumberField.RingOfIntegers F) F b.1 ≠ 0 :=
      mt (NumberField.RingOfIntegers.coe_eq_zero_iff).1 hb
    -- the images in `S` of `a` and `b`
    have hkey : algebraMap S ↥(E₁ ⊔ E₂) (⟨algebraMap (NumberField.RingOfIntegers F)
        (NumberField.RingOfIntegers ↥(E₁ ⊔ E₂)) a, S.algebraMap_mem a⟩ : S)
        = algebraMap F ↥(E₁ ⊔ E₂) (algebraMap (NumberField.RingOfIntegers F) F a) := rfl
    have hkey' : algebraMap S ↥(E₁ ⊔ E₂) (⟨algebraMap (NumberField.RingOfIntegers F)
        (NumberField.RingOfIntegers ↥(E₁ ⊔ E₂)) b.1, S.algebraMap_mem b.1⟩ : S)
        = algebraMap F ↥(E₁ ⊔ E₂) (algebraMap (NumberField.RingOfIntegers F) F b.1) := rfl
    have hbS : (⟨algebraMap (NumberField.RingOfIntegers F)
        (NumberField.RingOfIntegers ↥(E₁ ⊔ E₂)) b.1, S.algebraMap_mem b.1⟩ : S) ≠ 0 := by
      intro hb0
      apply hbF
      have h1 : algebraMap F ↥(E₁ ⊔ E₂)
          (algebraMap (NumberField.RingOfIntegers F) F b.1) = 0 := by
        rw [← hkey', hb0, map_zero]
      exact (map_eq_zero_iff (algebraMap F ↥(E₁ ⊔ E₂)) (RingHom.injective _)).1 h1
    -- cross-multiplied form of `c = a / b` in `E₁ ⊔ E₂`
    have hc_rel : algebraMap F ↥(E₁ ⊔ E₂) c *
        algebraMap S ↥(E₁ ⊔ E₂) (⟨algebraMap (NumberField.RingOfIntegers F)
          (NumberField.RingOfIntegers ↥(E₁ ⊔ E₂)) b.1, S.algebraMap_mem b.1⟩ : S)
        = algebraMap S ↥(E₁ ⊔ E₂) (⟨algebraMap (NumberField.RingOfIntegers F)
          (NumberField.RingOfIntegers ↥(E₁ ⊔ E₂)) a, S.algebraMap_mem a⟩ : S) := by
      rw [hkey', ← map_mul, hab, ← hkey]
    refine ⟨⟨algebraMap (NumberField.RingOfIntegers F)
          (NumberField.RingOfIntegers ↥(E₁ ⊔ E₂)) a, S.algebraMap_mem a⟩ * x₁,
        ⟨algebraMap (NumberField.RingOfIntegers F)
          (NumberField.RingOfIntegers ↥(E₁ ⊔ E₂)) b.1, S.algebraMap_mem b.1⟩ * y₁,
        mul_ne_zero hbS hy₁, ?_⟩
    rw [map_mul, map_mul, Algebra.smul_def, h₁, ← hc_rel]
    ring

end Work.Tower.Unramified
