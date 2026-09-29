import Mathlib.FieldTheory.IsAlgClosed.Basic

namespace Commons.Algebra.Polynomial

theorem exists_rootMultiplicity_pos_of_natDegree_ne_zero {K : Type*} [Field K] [IsAlgClosed K]
    (p : Polynomial K) (hp : p.natDegree ≠ 0) : ∃ a : K, 1 ≤ p.rootMultiplicity a := by
  have hp0 : p ≠ 0 := by
    rintro rfl
    simp at hp
  have hdeg : p.degree ≠ 0 := by
    rw [Polynomial.degree_eq_natDegree hp0]
    simpa using hp
  obtain ⟨a, ha⟩ := IsAlgClosed.exists_root p hdeg
  exact ⟨a, (p.rootMultiplicity_pos hp0).2 ha⟩

end Commons.Algebra.Polynomial