import Mathlib
import Submission.Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq
import Submission.Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff
import Submission.Commons.NumberTheory.NumberField.Valuation.exists_val_lt_one_and_ne_sq
import Submission.Commons.FieldTheory.IntermediateField.mem_adjoin_sq_eq
-- PORT435-BEGIN (v4.35 isDefEq respectTransparency compat)
set_option backward.isDefEq.respectTransparency false
set_option backward.isDefEq.respectTransparency.instanceSearchTypes false
set_option backward.isDefEq.respectTransparency.types false
-- PORT435-END

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.style.haveILetI false

open Polynomial IntermediateField

namespace Commons.NumberTheory.NumberField.Valuation

open scoped Pointwise

/-- Quadratic conjugation preserves the unit ball. -/
theorem mem_add_sub_mul_iff {K K' : Type*} [Field K] [Field K'] [Algebra K K']
    (A : ValuationSubring K') {π : K} {α : K'}
    (hα : α ^ 2 = algebraMap K K' π)
    (hH : ∀ c : K, A.valuation (algebraMap K K' π) ≠ A.valuation ((algebraMap K K' c) ^ 2)) :
    ∀ a b : K, (A.valuation (algebraMap K K' a + algebraMap K K' b * α) ≤ 1 ↔
      A.valuation (algebraMap K K' a - algebraMap K K' b * α) ≤ 1) := by
  intro a b
  by_cases hb : b = 0
  · subst hb
    simp
  by_cases ha : a = 0
  · subst ha
    simp only [map_zero]
    have hL : (0 : K') + algebraMap K K' b * α = algebraMap K K' b * α := by ring
    have hR : (0 : K') - algebraMap K K' b * α = -(algebraMap K K' b * α) := by ring
    rw [hL, hR, Valuation.map_neg]
  · have hb' : algebraMap K K' b ≠ 0 :=
      fun h => hb (RingHom.injective (algebraMap K K') (by simpa using h))
    have hbval : A.valuation (algebraMap K K' b) ≠ 0 := by
      rw [Valuation.ne_zero_iff]; exact hb'
    have hne : A.valuation (algebraMap K K' a) ≠
        A.valuation (algebraMap K K' b) * A.valuation α := by
      intro h
      have h1 : A.valuation (algebraMap K K' (a / b)) = A.valuation α := by
        rw [map_div₀, Valuation.map_div, h]
        exact mul_div_cancel_left₀ (A.valuation α) hbval
      have h2 : A.valuation (algebraMap K K' π) =
          A.valuation ((algebraMap K K' (a / b)) ^ 2) := by
        rw [map_pow, h1, ← map_pow, hα]
      exact hH (a / b) h2
    rw [Valuation.map_add_of_distinct_val A.valuation hne,
      show algebraMap K K' a - algebraMap K K' b * α =
        algebraMap K K' a + (-(algebraMap K K' b * α)) by ring,
      Valuation.map_add_of_distinct_val A.valuation (by rw [Valuation.map_neg]; exact hne),
      Valuation.map_neg, map_mul]

/-- The minimal polynomial of a square root of `π` which is not in the base field. -/
theorem minpoly_eq_X_sq_sub_C {K K' : Type*} [Field K] [Field K'] [Algebra K K'] {π : K} {α : K'}
    (hα : α ^ 2 = algebraMap K K' π) (hαK : α ∉ Set.range (algebraMap K K')) :
    minpoly K α = X ^ 2 - C π := by
  have hzero : aeval α (X ^ 2 - C π : K[X]) = 0 := by
    simp [hα]
  have hirr : Irreducible (X ^ 2 - C π : K[X]) := by
    rw [X_pow_sub_C_irreducible_iff_of_prime Nat.prime_two]
    intro b hb
    apply hαK
    have h2 : α ^ 2 - (algebraMap K K' b) ^ 2 = 0 := by
      rw [hα, ← map_pow, hb, sub_self]
    have h1 : (α - algebraMap K K' b) * (α + algebraMap K K' b) = 0 := by
      linear_combination h2
    rcases mul_eq_zero.mp h1 with h | h
    · exact ⟨b, (sub_eq_zero.mp h).symm⟩
    · exact ⟨-b, by rw [map_neg (algebraMap K K') b]; exact (eq_neg_of_add_eq_zero_left h).symm⟩
  exact (minpoly.eq_of_irreducible_of_monic hirr hzero (monic_X_pow_sub_C π (by norm_num))).symm

theorem exists_ne_one_comap_eq_of_comap_ne_top {K K' : Type*} [Field K] [NumberField K] [Field K'] [Algebra K K']
    [IsSepClosure K K'] (A : ValuationSubring K') (hA : A.comap (algebraMap K K') ≠ ⊤) :
    ∃ σ : K' ≃ₐ[K] K', σ ≠ 1 ∧ A.comap (σ : K' →+* K') = A := by
  obtain ⟨π, hπlt, hH⟩ := exists_val_lt_one_and_ne_sq A hA
  haveI hsc : IsSepClosed K' := IsSepClosure.sep_closed K
  haveI : CharZero K' := charZero_of_injective_algebraMap (algebraMap K K').injective
  haveI : NeZero (2 : K') := inferInstance
  obtain ⟨α, hα⟩ := IsSepClosed.exists_pow_nat_eq (algebraMap K K' π) 2
  have hπ0 : π ≠ 0 := by
    intro h
    refine hH 0 ?_
    rw [h]
    simp
  have hα0 : α ≠ 0 := by
    intro h
    refine hH 0 ?_
    rw [← hα, h]
    simp
  have hαK : α ∉ Set.range (algebraMap K K') := by
    rintro ⟨k, hk⟩
    subst hk
    exact hH k (by rw [hα.symm])
  haveI : Algebra.IsAlgebraic K K' := inferInstance
  have halg : IsAlgebraic K α := Algebra.IsAlgebraic.isAlgebraic α
  have hαint : IsIntegral K α := ⟨X ^ 2 - C π, monic_X_pow_sub_C π (by norm_num), by
    simp only [eval₂_sub, eval₂_X_pow, eval₂_C, hα, sub_self]⟩
  have hmin := minpoly_eq_X_sq_sub_C hα hαK
  let L : IntermediateField K K' := IntermediateField.adjoin K {α}
  have hLfin : FiniteDimensional K L := IntermediateField.adjoin.finiteDimensional hαint
  haveI : FiniteDimensional K L := hLfin
  haveI : Module.Free K (K⟮α⟯) := inferInstance
  haveI : Algebra.IsQuadraticExtension K (K⟮α⟯) :=
    ⟨by rw [IntermediateField.adjoin.finrank hαint, hmin, Polynomial.natDegree_X_pow_sub_C]⟩
  haveI : Normal K L := inferInstance
  have hroot : aeval (-α) (minpoly K α) = 0 := by
    rw [hmin]
    simp only [_root_.map_sub, map_pow, aeval_X, aeval_C]
    rw [neg_sq, hα, sub_self]
  obtain ⟨σ₀, hσ₀⟩ := minpoly.exists_algEquiv_of_root' (K := K) (L := K') (x := -α) (y := α)
    halg hroot
  have hαL : α ∈ L := IntermediateField.mem_adjoin_simple_self K α
  let τ : L ≃ₐ[K] L := σ₀.restrictNormal L
  have hτα : ∀ x : L, algebraMap L K' (τ x) = σ₀ (algebraMap L K' x) :=
    fun x => AlgEquiv.restrictNormal_commutes σ₀ L x
  have hτne : τ ≠ 1 := by
    intro h
    have h3 : σ₀ α = α := by
      have h1 : algebraMap L K' (τ ⟨α, hαL⟩) = σ₀ (algebraMap L K' ⟨α, hαL⟩) := hτα _
      rw [h] at h1
      simpa using h1.symm
    have h6 : α = -α := h3.symm.trans hσ₀
    have h7 : α + α = 0 := (eq_neg_iff_add_eq_zero).mp h6
    have h8 : (2 : K') * α = 0 := by rw [two_mul]; exact h7
    rcases mul_eq_zero.mp h8 with h9 | h9
    · exact two_ne_zero h9
    · exact hα0 h9
  have hτstab : τ ∈ MulAction.stabilizer (L ≃ₐ[K] L) (A.comap (algebraMap L K')) := by
    rw [Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff]
    intro x
    obtain ⟨a, b, hab⟩ := (Commons.FieldTheory.IntermediateField.mem_adjoin_sq_eq hα hαK (x : K')).mp x.2
    have hx : algebraMap L K' (τ x) = algebraMap K K' a - algebraMap K K' b * α := by
      rw [hτα x, show algebraMap L K' x = algebraMap K K' a + algebraMap K K' b * α from hab]
      rw [map_add, map_mul, σ₀.commutes a, σ₀.commutes b, hσ₀]
      ring
    rw [ValuationSubring.mem_comap, ValuationSubring.mem_comap, hx,
      show algebraMap L K' x = algebraMap K K' a + algebraMap K K' b * α from hab]
    rw [← A.valuation_le_one_iff _, ← A.valuation_le_one_iff _]
    exact mem_add_sub_mul_iff A hα hH a b
  obtain ⟨σ, hσmem, hσrest⟩ :=
    Commons.FieldTheory.Galois.exists_mem_stabilizer_restrictNormalHom_eq A hA L τ hτstab
  refine ⟨σ, ?_, ?_⟩
  · intro h
    apply hτne
    rw [← hσrest, h]
    simp
  · have hmem := (Commons.RingTheory.Valuation.mem_stabilizer_valuationSubring_iff A σ).mp hσmem
    ext x
    rw [ValuationSubring.mem_comap]
    exact (hmem x).symm

end Commons.NumberTheory.NumberField.Valuation
