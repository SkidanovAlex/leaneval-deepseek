import Submission.Work.WilkiesD.Proj

namespace Work.WilkiesD.Cover

open WilkiesDesign WilkiesConjecture

/-- The projected truncated zero set of an exp-polynomial is contained in the set of which the
exp-polynomial is a witness (the `X_M ⊆ X` half of the truncation argument). -/
theorem projFst_boxZero_subset {n m : ℕ} {P : MvPolynomial (Fin (n + m) ⊕ Fin (n + m)) ℝ}
    {X : Set (Fin n → ℝ)}
    (hX : X = {x | ∃ y : Fin m → ℝ, expPolyEval P (Fin.append x y) = 0}) (M : ℝ) :
    projFst m (boxZero M P) ⊆ X := by
  intro x hx
  rw [projFst_mem_iff] at hx
  obtain ⟨y, hy⟩ := hx
  rw [hX]
  exact ⟨y, hy.2⟩

end Work.WilkiesD.Cover
