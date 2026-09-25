import Mathlib
import Submission.Work.Tower.Chebotarev.Defs

namespace Work.Tower.Chebotarev

open NumberField IntermediateField Polynomial
open scoped Classical NumberField

/-- The compositum of `ℚ(i)` (inside `ℂ`) with the image of a Galois number field `N` under an
embedding `φ : N →ₐ[ℚ] ℂ` is a finite Galois extension of `ℚ`. -/
theorem isGalois_sup_adjoin_I {N : Type} [Field N] [NumberField N] [IsGalois ℚ N]
    (φ : N →ₐ[ℚ] ℂ) : IsGalois ℚ ↥(ℚ⟮Complex.I⟯ ⊔ φ.fieldRange) := by
  -- `φ.fieldRange ≃ₐ[ℚ] N`, so it is Galois over `ℚ` because `N` is.
  haveI hNφ : IsGalois ℚ ↥φ.fieldRange := IsGalois.of_algEquiv φ.equivFieldRange
  -- `ℚ⟮I⟯` is the splitting field of `X ^ 2 + 1` over `ℚ`, hence normal over `ℚ`.
  haveI hNI : Normal ℚ ↥ℚ⟮Complex.I⟯ := by
    have hsq : (Polynomial.C Complex.I : ℂ[X]) * Polynomial.C Complex.I = -1 := by
      rw [← Polynomial.C_mul, Complex.I_mul_I, Polynomial.C_neg, Polynomial.C_1]
    have hfac : (X - Polynomial.C Complex.I) * (X + Polynomial.C Complex.I)
        = (X ^ 2 + 1 : ℂ[X]) := by
      have h1 : (X - Polynomial.C Complex.I) * (X + Polynomial.C Complex.I)
          = X ^ 2 - Polynomial.C Complex.I * Polynomial.C Complex.I := by ring
      rw [h1, hsq]; ring
    have hmap : Polynomial.map (algebraMap ℚ ℂ) (X ^ 2 + 1 : ℚ[X])
        = (X - Polynomial.C Complex.I) * (X + Polynomial.C Complex.I) := by
      rw [show Polynomial.map (algebraMap ℚ ℂ) (X ^ 2 + 1 : ℚ[X]) = (X ^ 2 + 1 : ℂ[X])
            from by simp, hfac]
    have hsplit : (Polynomial.map (algebraMap ℚ ℂ) (X ^ 2 + 1 : ℚ[X])).Splits := by
      rw [hmap]
      exact (Polynomial.Splits.X_sub_C Complex.I).mul
        (by simpa using (Polynomial.Splits.X_sub_C (-Complex.I)))
    haveI : Polynomial.IsSplittingField ℚ
        ↥(adjoin ℚ ((X ^ 2 + 1 : ℚ[X]).rootSet ℂ)) (X ^ 2 + 1) :=
      IntermediateField.adjoin_rootSet_isSplittingField hsplit
    have hnorm : Normal ℚ ↥(adjoin ℚ ((X ^ 2 + 1 : ℚ[X]).rootSet ℂ)) :=
      Normal.of_isSplittingField (X ^ 2 + 1 : ℚ[X])
    have hne : Polynomial.map (algebraMap ℚ ℂ) (X ^ 2 + 1 : ℚ[X]) ≠ 0 := by
      rw [show Polynomial.map (algebraMap ℚ ℂ) (X ^ 2 + 1 : ℚ[X]) = (X ^ 2 + 1 : ℂ[X])
            from by simp]
      exact (Polynomial.monic_X_pow_add_C (a := (1 : ℂ)) (by norm_num)).ne_zero
    have hroot : (X ^ 2 + 1 : ℚ[X]).rootSet ℂ = {Complex.I, -Complex.I} := by
      ext z
      rw [Polynomial.mem_rootSet']
      constructor
      · rintro ⟨-, hz⟩
        have hz2 : z ^ 2 + 1 = 0 := by simpa using hz
        have hz3 : z ^ 2 = -1 := by linear_combination hz2
        have hzfac : (z - Complex.I) * (z + Complex.I) = 0 := by
          have h1 : (z - Complex.I) * (z + Complex.I) = z ^ 2 - Complex.I ^ 2 := by ring
          rw [h1, Complex.I_sq, hz3]; ring
        have : z = Complex.I ∨ z = -Complex.I := by
          rcases mul_eq_zero.mp hzfac with h | h
          · exact Or.inl (by linear_combination h)
          · exact Or.inr (by linear_combination h)
        rcases this with rfl | rfl <;> simp
      · intro hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl <;> exact ⟨hne, by simp [Complex.I_sq]⟩
    have hadj : adjoin ℚ ({Complex.I, -Complex.I} : Set ℂ) = ℚ⟮Complex.I⟯ := by
      apply le_antisymm
      · rw [adjoin_le_iff]
        intro z hz
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
        rcases hz with rfl | rfl
        · exact mem_adjoin_simple_self ℚ Complex.I
        · exact neg_mem (mem_adjoin_simple_self ℚ Complex.I)
      · rw [adjoin_le_iff]
        intro z hz
        rw [Set.mem_singleton_iff] at hz
        subst hz
        exact subset_adjoin ℚ _ (by simp)
    rw [hroot, hadj] at hnorm
    exact hnorm
  -- The compositum of two normal extensions is normal.
  haveI : Normal ℚ ↥(ℚ⟮Complex.I⟯ ⊔ φ.fieldRange) := inferInstance
  -- In characteristic zero, algebraic extensions are separable.
  exact isGalois_iff.mpr ⟨inferInstance, inferInstance⟩

end Work.Tower.Chebotarev
