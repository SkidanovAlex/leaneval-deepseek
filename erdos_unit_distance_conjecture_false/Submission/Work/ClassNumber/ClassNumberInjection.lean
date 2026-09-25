import Mathlib

namespace Work.ClassNumber

open scoped nonZeroDivisors

/-- **Minkowski's class number bound.**

If `M` dominates the Minkowski bound of the number field `K`, then every ideal class of `K`
contains an integral ideal of norm at most `⌊M⌋₊`. Consequently the class number of `K` — the
cardinality of the class group — is at most the number of nonzero integral ideals of `K` whose
absolute norm is at most `⌊M⌋₊`.

The proof exhibits the (evidently surjective) map sending such an ideal `I` to its class
`ClassGroup.mk0 I`, and uses that `NumberField.exists_ideal_in_class_of_norm_le` provides, in
every class `C`, a representative of norm at most the Minkowski bound of `K`. -/
theorem ClassNumberInjection (K : Type*) [Field K] [NumberField K] (M : ℝ)
    (hM : (4 / Real.pi) ^ NumberField.InfinitePlace.nrComplexPlaces K *
        ((Module.finrank ℚ K).factorial / (Module.finrank ℚ K) ^ (Module.finrank ℚ K) *
          Real.sqrt |((NumberField.discr K : ℤ) : ℝ)|) ≤ M) :
    (NumberField.classNumber K : ℝ) ≤
      Nat.card {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ ⌊M⌋₊} := by
  classical
  -- The Minkowski bound is nonnegative, so `M` is.
  have hM0 : 0 ≤ M := le_trans (by positivity) hM
  -- There are only finitely many ideals of bounded absolute norm.
  have hfin : Finite {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ ⌊M⌋₊} :=
    (Ideal.finite_setOfPred_absNorm_le ⌊M⌋₊).subset (fun I hI => hI.2)
  -- The class map on nonzero ideals of bounded norm is surjective: Minkowski's theorem
  -- supplies a representative of norm at most the Minkowski bound in every class.
  have hsurj : Function.Surjective
      (fun I : {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ ⌊M⌋₊} =>
        ClassGroup.mk0 ⟨I.1, mem_nonZeroDivisors_iff_ne_zero.mpr
          (fun h0 => I.2.1 (h0.trans Ideal.zero_eq_bot))⟩) := by
    intro C
    obtain ⟨I, hIC, hIle⟩ := NumberField.exists_ideal_in_class_of_norm_le C
    have hI0 : (I : Ideal (NumberField.RingOfIntegers K)) ≠ 0 := nonZeroDivisors.coe_ne_zero I
    -- The Minkowski bound of `K` is at most `M`.
    have hbound : (Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) : ℝ) ≤ M :=
      hIle.trans hM
    have hfloor : Ideal.absNorm (I : Ideal (NumberField.RingOfIntegers K)) ≤ ⌊M⌋₊ :=
      (Nat.le_floor_iff hM0).mpr hbound
    have hIbot : (I : Ideal (NumberField.RingOfIntegers K)) ≠ ⊥ :=
      fun h0 => hI0 (h0.trans Ideal.zero_eq_bot.symm)
    exact ⟨⟨I.1, hIbot, hfloor⟩, (congrArg ClassGroup.mk0 (Subtype.ext rfl)).trans hIC⟩
  have hcard : Nat.card (ClassGroup (NumberField.RingOfIntegers K)) ≤
      Nat.card {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ ⌊M⌋₊} :=
    @Nat.card_le_card_of_surjective _ _ hfin _ hsurj
  calc (NumberField.classNumber K : ℝ)
      = (Nat.card (ClassGroup (NumberField.RingOfIntegers K)) : ℝ) := by
        rw [NumberField.classNumber, Nat.card_eq_fintype_card]
    _ ≤ (Nat.card {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ ⌊M⌋₊} : ℝ) := by
        exact_mod_cast hcard

end Work.ClassNumber
