import Mathlib
import Submission.Work.WilE7.Defs
import Submission.Work.WilE8.Basic

namespace Work.WilE7

open WilkiesDesign WilkiesDesign.E

/-- Union of a finite family of `*`-sets with a *common* format bound `F` and a
*common* degree bound `D`, where only the indices in the finset `s` are assumed to be
`*`-sets. The degree bound of the union is `s.card * D`. -/
theorem star_iUnion_finset {n ι : ℕ} (s : Finset (Fin ι)) (A : Fin ι → Set (Fin n → ℝ))
    (F D : ℕ) (h : ∀ i ∈ s, Star F D n (A i)) :
    Star F (s.card * D) n (⋃ i ∈ s, A i) := by
  classical
  revert h
  refine Finset.induction_on (motive := fun t => (∀ i ∈ t, Star F D n (A i)) →
      Star F (t.card * D) n (⋃ i ∈ t, A i)) s ?_ ?_
  · intro _
    have h0 : (⋃ i ∈ (∅ : Finset (Fin ι)), A i) = (∅ : Set (Fin n → ℝ)) := by
      ext x
      simp
    rw [h0, Finset.card_empty, Nat.zero_mul]
    exact Work.WilE8.Star.empty F n
  · intro a t ht ih h
    rw [Work.WilE8.Star.iUnion_finset_insert, Finset.card_insert_of_notMem ht]
    have ha' : Star F D n (A a) := h a (Finset.mem_insert_self a t)
    have ht' : Star F (t.card * D) n (⋃ i ∈ t, A i) :=
      ih (fun i hi => h i (Finset.mem_insert_of_mem hi))
    have hunion : Star F (D + t.card * D) n (A a ∪ ⋃ i ∈ t, A i) :=
      Work.WilE8.Star.union2 ha' ht'
    have hle : D + t.card * D ≤ (t.card + 1) * D := by
      have hEq : (t.card + 1) * D = D + t.card * D := by ring
      exact le_of_eq hEq.symm
    exact Work.WilE8.Star.mono hunion le_rfl hle

theorem star_algebra :
    (∀ {n : ℕ} (P : WilkiesDesign.E.StarPiece n), P.set ⊆ WilkiesDesign.E.cubeC n) ∧
    (∀ {F F' D D' n : ℕ} {Y : Set (Fin n → ℝ)}, F ≤ F' → D ≤ D' →
        WilkiesDesign.E.Star F D n Y → WilkiesDesign.E.Star F' D' n Y) ∧
    (∀ {n F D₁ D₂ : ℕ} {Y₁ Y₂ : Set (Fin n → ℝ)}, WilkiesDesign.E.Star F D₁ n Y₁ →
        WilkiesDesign.E.Star F D₂ n Y₂ → WilkiesDesign.E.Star F (D₁ + D₂) n (Y₁ ∪ Y₂)) ∧
    (∀ {n ι : ℕ} (s : Finset (Fin ι)) (A : Fin ι → Set (Fin n → ℝ)) (F D : ℕ),
        (∀ i ∈ s, WilkiesDesign.E.Star F D n (A i)) →
        WilkiesDesign.E.Star F (s.card * D) n (⋃ i ∈ s, A i)) ∧
    (∀ {n F : ℕ}, WilkiesDesign.E.Star F 0 n (∅ : Set (Fin n → ℝ))) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro n P
    exact Work.WilE8.StarPiece.set_subset_cube P
  · intro F F' D D' n Y hF hD h
    exact Work.WilE8.Star.mono h hF hD
  · intro n F D₁ D₂ Y₁ Y₂ h1 h2
    exact Work.WilE8.Star.union2 h1 h2
  · intro n ι s A F D h
    exact star_iUnion_finset s A F D h
  · intro n F
    exact Work.WilE8.Star.empty F n

end Work.WilE7
