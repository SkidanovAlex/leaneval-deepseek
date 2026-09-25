import Mathlib
import Submission.Work.ClassNumber.PrimeNormCount
import Submission.Work.ClassNumber.PrimeProductBound
import Submission.Work.ClassNumber.SlotDefs
import Submission.Work.ClassNumber.TupleCount
import Submission.Work.ClassNumber.PhiInj

namespace Work.ClassNumber

open NumberField

variable (K : Type*) [Field K] [NumberField K]

/-- No entry of `Phi K I` vanishes when `I` is nonzero. -/
theorem Phi_ne_zero (I : Ideal (NumberField.RingOfIntegers K)) (hI : I ≠ ⊥)
    (i : Fin (Module.finrank ℚ K)) : Phi K I i ≠ 0 := by
  intro h
  have hprod := Phi_prod I hI
  have h0 : ∏ j, Phi K I j = 0 := Finset.prod_eq_zero (Finset.mem_univ i) h
  rw [hprod] at h0
  exact hI ((Ideal.absNorm_eq_zero_iff).mp h0)

/-- The number of nonzero integral ideals of absolute norm at most `m` is at most
`m ^ 2 * 2 ^ [K : ℚ]`. -/
theorem IdealCount (K : Type*) [Field K] [NumberField K] (m : ℕ) :
    Nat.card {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ m} ≤
      m ^ 2 * 2 ^ Module.finrank ℚ K := by
  classical
  haveI hfin : Finite {t : Fin (Module.finrank ℚ K) → ℕ // (∀ i, t i ≠ 0) ∧ ∏ i, t i ≤ m} := by
    refine Finite.of_injective
      (fun t : {t : Fin (Module.finrank ℚ K) → ℕ // (∀ i, t i ≠ 0) ∧ ∏ i, t i ≤ m} =>
        fun i => (⟨t.1 i, ?_⟩ : Fin (m + 1))) ?_
    · have h1 : ∀ j ∈ (Finset.univ : Finset (Fin (Module.finrank ℚ K))), 1 ≤ t.1 j :=
        fun j _ => Nat.one_le_iff_ne_zero.mpr (t.2.1 j)
      exact Nat.lt_succ_of_le
        (le_trans (Finset.single_le_prod h1 (Finset.mem_univ i)) t.2.2)
    · intro a b hab
      exact Subtype.ext (funext fun i => by
        have := congrFun hab i
        simpa using congrArg Fin.val this)
  have h1 : Nat.card {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ m}
      ≤ Nat.card {t : Fin (Module.finrank ℚ K) → ℕ // (∀ i, t i ≠ 0) ∧ ∏ i, t i ≤ m} := by
    refine Nat.card_le_card_of_injective
      (fun I : {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ m} =>
        ⟨Phi K I.1, Phi_ne_zero (K := K) I.1 I.2.1, by rw [Phi_prod I.1 I.2.1]; exact I.2.2⟩) ?_
    intro I I' h
    have hh : Phi K I.1 = Phi K I'.1 := congrArg Subtype.val h
    exact Subtype.ext (PhiInj K I.1 I'.1 I.2.1 I'.2.1 hh)
  calc Nat.card {I : Ideal (NumberField.RingOfIntegers K) // I ≠ ⊥ ∧ Ideal.absNorm I ≤ m}
      ≤ Nat.card {t : Fin (Module.finrank ℚ K) → ℕ // (∀ i, t i ≠ 0) ∧ ∏ i, t i ≤ m} := h1
    _ ≤ 2 ^ Module.finrank ℚ K * m ^ 2 := TupleCount _ _
    _ = m ^ 2 * 2 ^ Module.finrank ℚ K := by ring

end Work.ClassNumber
