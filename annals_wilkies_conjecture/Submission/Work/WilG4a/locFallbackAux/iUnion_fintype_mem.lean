import Mathlib
import Submission.Work.Wilkies.Defs

namespace Work.WilG4a.locFallbackAux

open WilkiesDesign

theorem iUnion_fintype_mem (S : WilkiesDesign.SOMin) {n : ℕ} {ι : Type} [Fintype ι] {a d : ℕ}
    (X : ι → Set (Fin n → ℝ)) (h : ∀ i, X i ∈ S.Ω a d n) :
    (⋃ i, X i) ∈ S.Ω a (Fintype.card ι * d) n := by
  classical
  have heq : (⋃ i : Fin (Fintype.card ι), X ((Fintype.equivFin ι).symm i)) = (⋃ i : ι, X i) := by
    ext x
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hi⟩; exact ⟨(Fintype.equivFin ι).symm i, hi⟩
    · rintro ⟨i, hi⟩; exact ⟨Fintype.equivFin ι i, by simpa using hi⟩
  have hcard : (∑ _ : Fin (Fintype.card ι), d) = Fintype.card ι * d := by
    simp [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  rw [← heq, ← hcard]
  exact S.union (fun _ => d) (fun i => X ((Fintype.equivFin ι).symm i)) (fun i => h _)

end Work.WilG4a.locFallbackAux
