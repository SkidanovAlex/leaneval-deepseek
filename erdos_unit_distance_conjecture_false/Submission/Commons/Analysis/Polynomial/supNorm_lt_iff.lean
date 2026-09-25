import Mathlib.Analysis.Polynomial.Norm

namespace Commons.Analysis.Polynomial

lemma supNorm_lt_iff {A : Type*} [SeminormedRing A] (p : Polynomial A) (ε : ℝ) :
    p.supNorm < ε ↔ ∀ i : ℕ, ‖p.coeff i‖ < ε := by
  constructor
  · intro h i
    exact lt_of_le_of_lt (Polynomial.le_supNorm p i) h
  · intro h
    rcases p.exists_eq_supNorm with ⟨i, hi⟩
    rw [hi]
    exact h i

end Commons.Analysis.Polynomial