import Mathlib
import Submission.Work.WilE7.Defs

namespace Work.WilE7

open WilkiesDesign

/-- The degree sum of a flattened list of `*`-pieces, read through `f`, is the sum of the
degree sums of the pieces: `∑_{x ∈ l} ∑_{a ∈ x} f a = ∑_{x ∈ l} (∑_{a ∈ x} f a)`. -/
private lemma flatten_map_sum {α : Type*} (l : List (List α)) (f : α → ℕ) :
    ((l.flatten).map f).sum = (l.map (fun x => (x.map f).sum)).sum := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatten_cons, List.map_append, List.sum_append, List.map_cons, List.sum_cons, ih]

theorem list_sum_tools :
    (∀ {n : ℕ} (L : List (WilkiesDesign.E.StarPiece n)),
        ((L.filter fun P => P.X.deg ≠ 0).map fun P => P.X.deg).sum ≤
          (L.map fun P => P.X.deg).sum) ∧
    (∀ {n : ℕ} (L : List (WilkiesDesign.E.StarPiece n)) (P : WilkiesDesign.E.StarPiece n),
        P ∈ L → P.X.deg ≤ (L.map fun P => P.X.deg).sum) ∧
    (∀ {n k : ℕ} (L : Fin k → List (WilkiesDesign.E.StarPiece n)),
        ((List.flatten (List.ofFn L)).map fun P => P.X.deg).sum ≤
          ∑ i, ((L i).map fun P => P.X.deg).sum) ∧
    (∀ {n k : ℕ} (L : Fin k → List (WilkiesDesign.E.StarPiece n)) (D : Fin k → ℕ),
        (∀ i, ((L i).map fun P => P.X.deg).sum ≤ D i) →
        ((List.flatten (List.ofFn L)).map fun P => P.X.deg).sum ≤ ∑ i, D i) := by
  have h1 : ∀ {n : ℕ} (L : List (WilkiesDesign.E.StarPiece n)),
      ((L.filter fun P => P.X.deg ≠ 0).map fun P => P.X.deg).sum ≤
        (L.map fun P => P.X.deg).sum := by
    intro n L
    induction L with
    | nil => simp
    | cons a t ih =>
      rw [List.filter_cons]
      split
      · rw [List.map_cons, List.sum_cons, List.map_cons, List.sum_cons]
        exact Nat.add_le_add_left ih a.X.deg
      · rw [List.map_cons, List.sum_cons]
        exact le_trans ih (Nat.le_add_left _ _)
  have h2 : ∀ {n : ℕ} (L : List (WilkiesDesign.E.StarPiece n))
      (P : WilkiesDesign.E.StarPiece n),
      P ∈ L → P.X.deg ≤ (L.map fun P => P.X.deg).sum := by
    intro n L
    induction L with
    | nil => intro P hP; simp at hP
    | cons a t ih =>
      intro P hP
      rw [List.map_cons, List.sum_cons]
      rcases List.mem_cons.mp hP with h | h
      · rw [h]; exact Nat.le_add_right _ _
      · exact le_trans (ih P h) (Nat.le_add_left _ _)
  have h3 : ∀ {n k : ℕ} (L : Fin k → List (WilkiesDesign.E.StarPiece n)),
      ((List.flatten (List.ofFn L)).map fun P => P.X.deg).sum ≤
        ∑ i, ((L i).map fun P => P.X.deg).sum := by
    intro n k L
    rw [flatten_map_sum (List.ofFn L) (fun P : WilkiesDesign.E.StarPiece n => P.X.deg)]
    simp only [List.map_ofFn, List.sum_ofFn, Function.comp_apply]
    exact le_refl _
  have h4 : ∀ {n k : ℕ} (L : Fin k → List (WilkiesDesign.E.StarPiece n)) (D : Fin k → ℕ),
      (∀ i, ((L i).map fun P => P.X.deg).sum ≤ D i) →
      ((List.flatten (List.ofFn L)).map fun P => P.X.deg).sum ≤ ∑ i, D i := by
    intro n k L D hD
    exact le_trans (h3 L) (Finset.sum_le_sum (fun i _ => hD i))
  exact ⟨h1, h2, h3, h4⟩

end Work.WilE7
