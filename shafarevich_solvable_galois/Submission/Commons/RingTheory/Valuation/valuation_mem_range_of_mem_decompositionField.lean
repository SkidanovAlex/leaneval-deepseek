import Mathlib
import Submission.Commons.FieldTheory.Galois.exists_finite_galois_containing
import Submission.Commons.RingTheory.Valuation.exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois
import Submission.Commons.RingTheory.Valuation.exists_val_eq_algebraMap_of_mem_fixedField_stabilizer
import Submission.Commons.RingTheory.Valuation.ValuationSubring.eq_top_of_comap_algebraMap_eq_top
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option linter.style.haveILetI false

namespace Commons.RingTheory.Valuation

open scoped Pointwise

/-- If two elements of the domain of a ring homomorphism have the same value at the pullback
place `A.comap f`, then their images have the same value at `A`.

Only this direction holds in general: the value group of `A.comap f` is a quotient of the value
group of the valuation of `A` restricted to the image of `f`, so equality of the pullback values
implies equality of the values in the larger field. -/
private theorem valuation_comp_of_comap_valuation_eq {K L : Type*} [Field K] [Field L]
    (A : ValuationSubring L) (f : K →+* L) {x y : K}
    (h : (A.comap f).valuation x = (A.comap f).valuation y) :
    A.valuation (f x) = A.valuation (f y) := by
  refine le_antisymm ?_ ?_
  · obtain ⟨a, ha⟩ := (ValuationSubring.valuation_le_iff (A.comap f) x y).mp h.le
    rw [ValuationSubring.valuation_le_iff]
    refine ⟨⟨f (a : K), ValuationSubring.mem_comap.mp a.2⟩, ?_⟩
    rw [← map_mul, ha]
  · obtain ⟨a, ha⟩ := (ValuationSubring.valuation_le_iff (A.comap f) y x).mp h.symm.le
    rw [ValuationSubring.valuation_le_iff]
    refine ⟨⟨f (a : K), ValuationSubring.mem_comap.mp a.2⟩, ?_⟩
    rw [← map_mul, ha]

/-- The valuation attached to `⊤ : ValuationSubring E` is the trivial valuation. -/
private theorem valuation_eq_one_of_eq_top {E : Type*} [Field E] (A : ValuationSubring E)
    (hA : A = ⊤) {z : E} (hz : z ≠ 0) : A.valuation z = 1 := by
  have hzA : z ∈ A := by rw [hA]; exact trivial
  have hz1A : z⁻¹ ∈ A := by rw [hA]; exact trivial
  have hunit : IsUnit (⟨z, hzA⟩ : A) :=
    ⟨⟨⟨z, hzA⟩, ⟨z⁻¹, hz1A⟩, Subtype.ext (mul_inv_cancel₀ hz),
      Subtype.ext (inv_mul_cancel₀ hz)⟩, rfl⟩
  exact (ValuationSubring.valuation_eq_one_iff A ⟨z, hzA⟩).mp hunit

/-- **The decomposition field of a valuation subring of a separable closure is an immediate
extension of the base field.**

Let `E/F` be a separable closure, `A : ValuationSubring E` and `Z = Fix(Stab_{Gal(E/F)}(A))` the
decomposition field of `A`.  Then every element of `Z` has the same `A`-value as some element of
`F`: the value group of the restriction of `A` to `Z` is the value group of `A` on `F`. -/
theorem valuation_mem_range_of_mem_decompositionField {F E : Type*} [Field F] [Field E]
    [Algebra F E] [IsSepClosure F E] (A : ValuationSubring E)
    (x : IntermediateField.fixedField (MulAction.stabilizer (E ≃ₐ[F] E) A)) :
    ∃ y : F, A.valuation (x : E) = A.valuation (algebraMap F E y) := by
  classical
  by_cases hx0 : (x : E) = 0
  · exact ⟨0, by simp [hx0]⟩
  by_cases hA : A = ⊤
  · -- the valuation of `A` is the trivial valuation
    refine ⟨1, ?_⟩
    rw [valuation_eq_one_of_eq_top A hA hx0]
    simp
  · -- the main case: `A` is a proper valuation subring
    have hcomp : A.comap (algebraMap F E) ≠ ⊤ := fun h =>
      hA (ValuationSubring.eq_top_of_comap_algebraMap_eq_top A (F := F) (K' := E)
        inferInstance h)
    -- a finite Galois intermediate field containing `x`
    obtain ⟨N, hNfin, hNgal, hxN⟩ :=
      Commons.FieldTheory.Galois.exists_finite_galois_containing (k := F) (K := E) (x : E)
    haveI := hNfin
    haveI := hNgal
    -- `x` is fixed by the decomposition group of the trace of `A` on `N`
    have hxmem : (⟨(x : E), hxN⟩ : ↥N) ∈
        IntermediateField.fixedField
          (MulAction.stabilizer (↥N ≃ₐ[F] ↥N) (A.comap (algebraMap ↥N E))) := by
      rw [IntermediateField.mem_fixedField_iff]
      intro τ hτ
      obtain ⟨σ, hσ, hστ⟩ :=
        exists_mem_stabilizer_restrictNormalHom_eq_of_isGalois A hcomp N τ hτ
      have hσx : σ (x : E) = (x : E) :=
        (IntermediateField.mem_fixedField_iff (MulAction.stabilizer (E ≃ₐ[F] E) A) (x : E)).mp
          x.2 σ hσ
      refine Subtype.ext ?_
      calc ((τ ⟨(x : E), hxN⟩ : ↥N) : E)
          = (((AlgEquiv.restrictNormalHom (F := F) (K₁ := E) N σ)
              ⟨(x : E), hxN⟩ : ↥N) : E) := by rw [hστ]
        _ = σ ((⟨(x : E), hxN⟩ : ↥N) : E) := by
            rw [AlgEquiv.restrictNormalHom_apply]
        _ = (x : E) := by rw [hσx]
        _ = ((⟨(x : E), hxN⟩ : ↥N) : E) := rfl
    -- the finite Galois case
    obtain ⟨y, hy⟩ :=
      exists_val_eq_algebraMap_of_mem_fixedField_stabilizer (K := F) (L := ↥N)
        (A.comap (algebraMap ↥N E)) ⟨⟨(x : E), hxN⟩, hxmem⟩
    refine ⟨y, ?_⟩
    have h1 := valuation_comp_of_comap_valuation_eq A (algebraMap ↥N E) hy
    have h2 : (algebraMap ↥N E) (⟨(x : E), hxN⟩ : ↥N) = (x : E) := rfl
    have h3 : (algebraMap ↥N E) (algebraMap F ↥N y) = algebraMap F E y :=
      IsScalarTower.algebraMap_apply F ↥N E y
    rw [h2, h3] at h1
    exact h1

end Commons.RingTheory.Valuation
