import Mathlib.FieldTheory.Galois.Basic

set_option linter.style.haveILetI false

namespace Commons.FieldTheory.Galois

open IntermediateField

theorem exists_finite_galois_finrank_ge_of_infinite_gal
    {F K : Type} [Field F] [Field K] [Algebra F K] [IsGalois F K]
    (h : Infinite Gal(K/F)) (n : ℕ) :
    ∃ L : IntermediateField F K, FiniteDimensional F L ∧ IsGalois F L ∧
      n ≤ Module.finrank F ↥L := by
  have hfd : ¬ FiniteDimensional F K := by
    intro hfd
    letI : FiniteDimensional F K := hfd
    haveI : Finite Gal(K/F) := by
      haveI : Fintype Gal(K/F) := AlgEquiv.fintype F K
      infer_instance
    exact not_finite (Gal(K/F))
  haveI : Algebra.IsAlgebraic F K := inferInstance
  obtain ⟨E, hEfd, hn⟩ := IntermediateField.exists_lt_finrank_of_infinite_dimensional hfd n
  refine ⟨IntermediateField.normalClosure F E K, ?_, ?_, ?_⟩
  · infer_instance
  · infer_instance
  · exact hn.le.trans (IntermediateField.finrank_le_of_le_right (IntermediateField.le_normalClosure E))

end Commons.FieldTheory.Galois