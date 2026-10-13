import Mathlib

namespace Work.WilE9.Sharp.Layer

/-- The sum of a list of a constant is the length times the constant. -/
private lemma sum_map_const_eq {α : Type*} (l : List α) (c : ℕ) :
    (l.map fun _ => c).sum = l.length * c := by
  induction l with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.sum_cons, List.length_cons, ih]
      ring

theorem lengthBound {α β : Type*}
    (L : List α) (f : α → List β) (b : Polynomial ℕ) (D : ℕ)
    (hlen : L.length ≤ D + 1) (h : ∀ a ∈ L, (f a).length ≤ b.eval D) :
    (L.flatMap f).length ≤ (D + 1) * b.eval D := by
  rw [List.length_flatMap]
  have h1 : (L.map fun a => (f a).length).sum ≤ (L.map fun _ => b.eval D).sum :=
    List.sum_le_sum (fun a ha => h a ha)
  have h2 : (L.map fun _ => b.eval D).sum = L.length * b.eval D :=
    sum_map_const_eq L (b.eval D)
  rw [h2] at h1
  exact le_trans h1 (Nat.mul_le_mul_right _ hlen)

end Work.WilE9.Sharp.Layer
