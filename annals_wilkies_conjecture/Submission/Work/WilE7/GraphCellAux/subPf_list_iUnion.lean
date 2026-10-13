import Mathlib
import Submission.Work.Wilkies.E.Spec
import Submission.Work.WilE7.subPf_algebra

namespace Work.WilE7.GraphCellAux

/-- Splitting off the head of a union indexed by a list. -/
theorem iUnion_list_cons {n : ℕ} (a : WilkiesDesign.E.StarPiece n)
    (t : List (WilkiesDesign.E.StarPiece n))
    (A : WilkiesDesign.E.StarPiece n → Set (Fin n → ℝ)) :
    (⋃ P ∈ (a :: t), A P) = A a ∪ ⋃ P ∈ t, A P := by
  ext x
  simp [List.mem_cons, Set.mem_iUnion]

/-- The union indexed by the empty list is empty. -/
theorem iUnion_list_nil {n : ℕ} (A : WilkiesDesign.E.StarPiece n → Set (Fin n → ℝ)) :
    (⋃ P ∈ ([] : List (WilkiesDesign.E.StarPiece n)), A P) = (∅ : Set (Fin n → ℝ)) := by
  ext x
  simp

/-- A union of sub-Pfaffian sets indexed by a list is sub-Pfaffian. -/
theorem subPf_list_iUnion {n : ℕ} (L : List (WilkiesDesign.E.StarPiece n))
    (A : WilkiesDesign.E.StarPiece n → Set (Fin n → ℝ))
    (h : ∀ P ∈ L, WilkiesDesign.E.SubPf n (A P)) :
    WilkiesDesign.E.SubPf n (⋃ P ∈ L, A P) := by
  revert h
  induction L with
  | nil =>
    intro _
    rw [iUnion_list_nil]
    exact Work.WilE7.SubPfAlg.subPf_empty n
  | cons a t ih =>
    intro h
    rw [iUnion_list_cons]
    exact Work.WilE7.SubPfAlg.subPf_union (h a (by simp))
      (ih (fun P hP => h P (by simp [hP])))

end Work.WilE7.GraphCellAux
